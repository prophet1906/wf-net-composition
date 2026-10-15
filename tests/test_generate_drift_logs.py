#!/usr/bin/env python3
"""
Unit and invariant tests for Deterministic Service Event Log Label Drift Generation.

Verifies:
  - Format drift tag and tag inference from paths and strings.
  - Deterministic case selection using SHA-256 modulo: int(sha256(case_id)) % 10000 < round(D * 100).
  - Canonical-to-drifted RPC span mutation rules and proof-of-call callee preservation.
  - Strict mathematical invariants: row count preservation, timestamp invariance, case count preservation.
  - Strict read-only immutability of the source logs directory.
  - Batch execution and directory structure creation (logs_drift_<percentage>).
  - Structured summary JSON creation and schema validation (drift_<tag>.summary.json).
  - Boundary and edge case handling (0% drift, 100% drift, fractional drift, empty files,
    missing columns, non-existent directories, invalid drift parameters).
  - CLI command-line execution.
"""

import csv
import hashlib
import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

# Add repository root to path
REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT))

from src.generate_drift_logs import (
    DEFAULT_DRIFT_RULES,
    PROOF_OF_CALL_TARGETS,
    REQUIRED_CSV_COLUMNS,
    format_drift_filename,
    format_drift_tag,
    generate_drift_logs,
    generate_drift_logs_batch,
    infer_drift_tag,
    is_case_selected_for_drift,
    main,
    process_service_drift_log,
    validate_csv_header,
)


def get_dir_checksums(dir_path: str) -> dict:
    """Calculate SHA256 hashes of all files in a directory."""
    checksums = {}
    for root, _, files in os.walk(dir_path):
        for f in sorted(files):
            file_path = os.path.join(root, f)
            with open(file_path, "rb") as fp:
                checksums[os.path.relpath(file_path, dir_path)] = hashlib.sha256(fp.read()).hexdigest()
    return checksums


class TestTagFormattingAndInference(unittest.TestCase):
    """Test suite validating drift tag formatting and regex inference."""

    def test_format_drift_tag(self):
        """Verify drift percentage formatting for integer and fractional values."""
        self.assertEqual(format_drift_tag(5.0), "drift_5")
        self.assertEqual(format_drift_tag(5), "drift_5")
        self.assertEqual(format_drift_tag(10.0), "drift_10")
        self.assertEqual(format_drift_tag(0.0), "drift_0")
        self.assertEqual(format_drift_tag(100.0), "drift_100")
        self.assertEqual(format_drift_tag(7.5), "drift_7_5")
        self.assertEqual(format_drift_tag(2.5), "drift_2_5")
        self.assertEqual(format_drift_tag(12.25), "drift_12_25")

    def test_infer_drift_tag(self):
        """Verify extraction of drift tag from various paths and strings."""
        self.assertEqual(infer_drift_tag("logs_drift_5"), "drift_5")
        self.assertEqual(infer_drift_tag("path/to/logs_drift_10"), "drift_10")
        self.assertEqual(infer_drift_tag("logs_drift_7_5/media-service.csv"), "drift_7_5")
        self.assertEqual(infer_drift_tag("drift_20"), "drift_20")
        self.assertEqual(infer_drift_tag("logs"), None)
        self.assertEqual(infer_drift_tag("logs/compose-post-service.csv"), None)
        self.assertEqual(infer_drift_tag(""), None)
        self.assertEqual(infer_drift_tag(None), None)

    def test_format_drift_filename(self):
        """Verify artifact filename construction with drift tag."""
        self.assertEqual(
            format_drift_filename("mining", "drift_5", ".summary.json"),
            "mining_drift_5.summary.json",
        )
        self.assertEqual(
            format_drift_filename("compose-post-service", "drift_10", ".pnml"),
            "compose-post-service_drift_10.pnml",
        )
        self.assertEqual(
            format_drift_filename("media-service", None, ".pnml"),
            "media-service.pnml",
        )
        # Avoid duplicate tag
        self.assertEqual(
            format_drift_filename("service_drift_5", "drift_5", ".pnml"),
            "service_drift_5.pnml",
        )


class TestDeterministicCaseSelection(unittest.TestCase):
    """Test suite validating SHA-256 modulo case selection determinism."""

    def test_case_selection_determinism(self):
        """Repeated evaluations of the same case ID yield identical selection outcomes."""
        case_ids = [f"trace_{i}_{i*17}" for i in range(100)]
        for drift in [2.5, 5.0, 10.0, 50.0]:
            first_run = [is_case_selected_for_drift(cid, drift) for cid in case_ids]
            second_run = [is_case_selected_for_drift(cid, drift) for cid in case_ids]
            self.assertEqual(first_run, second_run)

    def test_boundary_zero_and_hundred_percent(self):
        """0% drift selects 0 cases, 100% drift selects 100% of cases."""
        case_ids = [f"case_alpha_{i}" for i in range(200)]
        for cid in case_ids:
            self.assertFalse(is_case_selected_for_drift(cid, 0.0))
            self.assertTrue(is_case_selected_for_drift(cid, 100.0))

    def test_selection_subset_monotonicity(self):
        """Any case selected at D=5% is also selected at D=10% (hash threshold monotonicity)."""
        case_ids = [f"trace_uuid_{i}" for i in range(500)]
        for cid in case_ids:
            if is_case_selected_for_drift(cid, 5.0):
                self.assertTrue(is_case_selected_for_drift(cid, 10.0))
            if is_case_selected_for_drift(cid, 10.0):
                self.assertTrue(is_case_selected_for_drift(cid, 20.0))

    def test_selection_distribution(self):
        """Over a large sample, the selection ratio closely matches the configured drift percentage."""
        n_samples = 10000
        cases = [f"sim_case_{i}" for i in range(n_samples)]
        selected_10 = sum(1 for c in cases if is_case_selected_for_drift(c, 10.0))
        # Expect ~1000 selected (10%)
        self.assertAlmostEqual(selected_10 / n_samples, 0.10, delta=0.015)


class TestSpanMutationAndProofPreservation(unittest.TestCase):
    """Test suite validating caller client span mutation and callee server span immutability."""

    def setUp(self):
        self.temp_dir = tempfile.TemporaryDirectory()
        self.source_dir = os.path.join(self.temp_dir.name, "logs")
        os.makedirs(self.source_dir, exist_ok=True)

        # Service 1 (Caller): compose-post-service.csv
        # Has caller client spans: store_post_client, compose_text_client
        self.caller_csv = os.path.join(self.source_dir, "compose-post-service.csv")
        with open(self.caller_csv, "w", encoding="utf-8", newline="") as f:
            writer = csv.writer(f)
            writer.writerow(["case_id", "activity", "timestamp"])
            for i in range(100):
                cid = f"trace_{i}"
                writer.writerow([cid, "compose_post_server", str(1000 + i * 10)])
                writer.writerow([cid, "compose_text_client", str(1001 + i * 10)])
                writer.writerow([cid, "store_post_client", str(1002 + i * 10)])

        # Service 2 (Callee): post-storage-service.csv
        # Has callee server span: store_post_server
        self.callee_csv = os.path.join(self.source_dir, "post-storage-service.csv")
        with open(self.callee_csv, "w", encoding="utf-8", newline="") as f:
            writer = csv.writer(f)
            writer.writerow(["case_id", "activity", "timestamp"])
            for i in range(100):
                cid = f"trace_{i}"
                writer.writerow([cid, "store_post_server", str(1005 + i * 10)])

    def tearDown(self):
        self.temp_dir.cleanup()

    def test_default_drift_rules_mutate_caller_client_spans(self):
        """Caller client spans in selected traces are mutated to drifted aliases."""
        summary = generate_drift_logs(self.source_dir, 100.0)
        out_dir = summary["output_dir"]

        caller_out = os.path.join(out_dir, "compose-post-service.csv")
        with open(caller_out, "r", encoding="utf-8") as f:
            rows = list(csv.DictReader(f))

        # At 100% drift, all compose_text_client -> compose_text_grpc_client
        # and store_post_client -> store_post_client_v2
        activities = [r["activity"] for r in rows]
        self.assertNotIn("compose_text_client", activities)
        self.assertNotIn("store_post_client", activities)
        self.assertIn("compose_text_grpc_client", activities)
        self.assertIn("store_post_client_v2", activities)
        # Entry server span compose_post_server remains unchanged
        self.assertIn("compose_post_server", activities)

    def test_callee_server_spans_strictly_preserved(self):
        """Callee server spans remain 100% canonical and unmodified as physical proof."""
        summary = generate_drift_logs(self.source_dir, 100.0)
        out_dir = summary["output_dir"]

        callee_out = os.path.join(out_dir, "post-storage-service.csv")
        with open(callee_out, "r", encoding="utf-8") as f:
            rows = list(csv.DictReader(f))

        # All 100 events must still be store_post_server
        activities = [r["activity"] for r in rows]
        self.assertEqual(len(activities), 100)
        self.assertTrue(all(act == "store_post_server" for act in activities))


class TestMathematicalInvariantsAndImmutability(unittest.TestCase):
    """Test suite validating row count, timestamp invariance, and source immutability."""

    def setUp(self):
        self.temp_dir = tempfile.TemporaryDirectory()
        self.source_dir = os.path.join(self.temp_dir.name, "source_logs")
        os.makedirs(self.source_dir, exist_ok=True)

        self.csv1 = os.path.join(self.source_dir, "svc1.csv")
        with open(self.csv1, "w", encoding="utf-8", newline="") as f:
            writer = csv.writer(f)
            writer.writerow(["case_id", "activity", "timestamp"])
            for i in range(120):
                writer.writerow([f"c_{i % 30}", "store_post_client", str(1000000 + i * 50)])

    def tearDown(self):
        self.temp_dir.cleanup()

    def test_source_directory_immutability(self):
        """Source directory files and checksums remain untouched after single and batch runs."""
        initial_checksums = get_dir_checksums(self.source_dir)

        generate_drift_logs(self.source_dir, 5.0)
        generate_drift_logs(self.source_dir, 20.0)
        generate_drift_logs_batch(self.source_dir, [0.0, 10.0, 50.0])

        post_checksums = get_dir_checksums(self.source_dir)
        self.assertEqual(initial_checksums, post_checksums)

    def test_immutability_guard_rejects_identical_output_dir(self):
        """Attempting to specify output_dir identical to source_dir raises ValueError."""
        with self.assertRaises(ValueError) as ctx:
            generate_drift_logs(self.source_dir, 10.0, output_dir=self.source_dir)
        self.assertIn("Source directory immutability violation", str(ctx.exception))

    def test_row_count_and_timestamp_invariance(self):
        """Output CSV matches source CSV in row count, case ordering, and microsecond timestamps."""
        summary = generate_drift_logs(self.source_dir, 25.0)
        out_dir = summary["output_dir"]
        dst_csv = os.path.join(out_dir, "svc1.csv")

        with open(self.csv1, "r", encoding="utf-8") as f_src, open(dst_csv, "r", encoding="utf-8") as f_dst:
            src_rows = list(csv.DictReader(f_src))
            dst_rows = list(csv.DictReader(f_dst))

        self.assertEqual(len(src_rows), len(dst_rows))
        for src_r, dst_r in zip(src_rows, dst_rows):
            self.assertEqual(src_r["case_id"], dst_r["case_id"])
            self.assertEqual(src_r["timestamp"], dst_r["timestamp"])


class TestBatchGenerationAndSummaryJSON(unittest.TestCase):
    """Test suite validating batch generation, output folder structures, and summary metrics."""

    def setUp(self):
        self.temp_dir = tempfile.TemporaryDirectory()
        self.source_dir = os.path.join(self.temp_dir.name, "logs")
        os.makedirs(self.source_dir, exist_ok=True)

        with open(os.path.join(self.source_dir, "svc_a.csv"), "w", encoding="utf-8", newline="") as f:
            writer = csv.writer(f)
            writer.writerow(["case_id", "activity", "timestamp"])
            for i in range(100):
                writer.writerow([f"case_{i}", "store_post_client", str(1000 + i)])

    def tearDown(self):
        self.temp_dir.cleanup()

    def test_single_drift_generation_creates_expected_files(self):
        """Single drift run creates logs_drift_10 with mutated CSVs and drift_drift_10.summary.json."""
        summary = generate_drift_logs(self.source_dir, 10.0)

        expected_out = os.path.join(self.temp_dir.name, "logs_drift_10")
        self.assertTrue(os.path.isdir(expected_out))

        summary_file = os.path.join(expected_out, "drift_drift_10.summary.json")
        self.assertTrue(os.path.isfile(summary_file))

        with open(summary_file, "r", encoding="utf-8") as f:
            saved = json.load(f)

        self.assertEqual(saved["source_dir"], self.source_dir)
        self.assertEqual(saved["drift_percentage"], 10.0)
        self.assertEqual(saved["total_original_events"], 100)
        self.assertEqual(saved["total_retained_events"], 100)
        self.assertEqual(saved["total_dropped_events"], 0)
        self.assertEqual(saved["total_cases"], 100)
        self.assertIn("drift_rules", saved)
        self.assertIn("proof_of_call_targets", saved)
        self.assertIn("svc_a", saved["services"])

    def test_batch_generation_creates_multiple_directories(self):
        """Batch run with --drift 0 5 10 20 creates distinct directories."""
        results = generate_drift_logs_batch(self.source_dir, [0.0, 5.0, 10.0, 20.0])

        self.assertEqual(len(results), 4)
        for drift in [0.0, 5.0, 10.0, 20.0]:
            tag = format_drift_tag(drift)
            out_dir = os.path.join(self.temp_dir.name, f"logs_{tag}")
            self.assertTrue(os.path.isdir(out_dir))
            summary_file = os.path.join(out_dir, f"drift_{tag}.summary.json")
            self.assertTrue(os.path.isfile(summary_file))

    def test_custom_output_dir_for_single_drift(self):
        """Custom output directory works for single drift runs."""
        custom_dir = os.path.join(self.temp_dir.name, "my_custom_drift")
        summary = generate_drift_logs(self.source_dir, 10.0, output_dir=custom_dir)

        self.assertTrue(os.path.isdir(custom_dir))
        self.assertTrue(os.path.isfile(os.path.join(custom_dir, "drift_drift_10.summary.json")))
        self.assertEqual(summary["output_dir"], os.path.abspath(custom_dir))

    def test_cli_execution_batch(self):
        """CLI invocation executes batch run successfully."""
        cmd = [
            sys.executable,
            str(REPO_ROOT / "src" / "generate_drift_logs.py"),
            "--logs-dir",
            self.source_dir,
            "--drift",
            "5",
            "10",
        ]
        proc = subprocess.run(cmd, capture_output=True, text=True)
        self.assertEqual(proc.returncode, 0, msg=f"CLI failed: {proc.stderr}")
        self.assertIn("Generated drift logs for drift=5.0%", proc.stdout)
        self.assertIn("Generated drift logs for drift=10.0%", proc.stdout)


class TestEdgeCasesAndValidation(unittest.TestCase):
    """Test suite validating boundary conditions, edge cases, and schema errors."""

    def setUp(self):
        self.temp_dir = tempfile.TemporaryDirectory()
        self.source_dir = os.path.join(self.temp_dir.name, "logs")
        os.makedirs(self.source_dir, exist_ok=True)

    def tearDown(self):
        self.temp_dir.cleanup()

    def test_nonexistent_source_directory_raises_error(self):
        """Non-existent source directory raises FileNotFoundError."""
        with self.assertRaises(FileNotFoundError):
            generate_drift_logs(os.path.join(self.temp_dir.name, "missing"), 5.0)

    def test_source_path_is_file_raises_error(self):
        """Source path pointing to a file raises NotADirectoryError."""
        file_path = os.path.join(self.temp_dir.name, "file.txt")
        with open(file_path, "w") as f:
            f.write("content")
        with self.assertRaises(NotADirectoryError):
            generate_drift_logs(file_path, 5.0)

    def test_out_of_bounds_drift_raises_error(self):
        """Drift percentage < 0 or > 100 raises ValueError."""
        with self.assertRaises(ValueError):
            generate_drift_logs(self.source_dir, -5.0)
        with self.assertRaises(ValueError):
            generate_drift_logs(self.source_dir, 105.0)

    def test_empty_logs_directory_raises_error(self):
        """Directory with no CSV files raises ValueError."""
        with self.assertRaises(ValueError) as ctx:
            generate_drift_logs(self.source_dir, 5.0)
        self.assertIn("No CSV event logs found", str(ctx.exception))

    def test_empty_csv_file_handling(self):
        """CSV file with only header or zero rows is handled gracefully."""
        csv_file = os.path.join(self.source_dir, "empty_svc.csv")
        with open(csv_file, "w", encoding="utf-8", newline="") as f:
            writer = csv.writer(f)
            writer.writerow(["case_id", "activity", "timestamp"])

        summary = generate_drift_logs(self.source_dir, 10.0)
        self.assertEqual(summary["total_original_events"], 0)
        self.assertEqual(summary["total_mutated_events"], 0)
        self.assertEqual(summary["total_dropped_events"], 0)
        self.assertEqual(summary["services"]["empty_svc"]["total_events"], 0)
        self.assertEqual(summary["services"]["empty_svc"]["mutated_events"], 0)

    def test_missing_csv_columns_raises_error(self):
        """CSV file missing required columns raises ValueError."""
        csv_file = os.path.join(self.source_dir, "bad_svc.csv")
        with open(csv_file, "w", encoding="utf-8", newline="") as f:
            writer = csv.writer(f)
            writer.writerow(["case_id", "timestamp"])  # missing 'activity'
            writer.writerow(["c1", "1000"])

        with self.assertRaises(ValueError) as ctx:
            generate_drift_logs(self.source_dir, 5.0)
        self.assertIn("Missing required columns", str(ctx.exception))

    def test_batch_with_custom_output_dir_raises_error(self):
        """Specifying custom output_dir with multiple drift percentages raises ValueError."""
        with self.assertRaises(ValueError) as ctx:
            generate_drift_logs_batch(
                self.source_dir,
                [5.0, 10.0],
                output_dir=os.path.join(self.temp_dir.name, "out"),
            )
class TestDownstreamMinerCompatibility(unittest.TestCase):
    """Test suite validating seamless compatibility with src/miner.py and drift tag propagation."""

    def setUp(self):
        self.temp_dir = tempfile.TemporaryDirectory()
        self.source_dir = os.path.join(self.temp_dir.name, "logs")
        os.makedirs(self.source_dir, exist_ok=True)

        # Create a valid service log
        csv_file = os.path.join(self.source_dir, "test-service.csv")
        rows = [
            "case_id,activity,timestamp\n",
            "c1,actA,1000\n",
            "c1,actB,2000\n",
            "c2,actA,1000\n",
            "c2,actB,2000\n",
            "c3,actA,1000\n",
            "c3,actB,2000\n",
            "c4,actA,1000\n",
            "c4,actB,2000\n",
        ]
        with open(csv_file, "w", encoding="utf-8") as f:
            f.writelines(rows)

    def tearDown(self):
        self.temp_dir.cleanup()

    def test_miner_adopts_drift_tag_naming(self):
        """src/miner.py run against logs_drift_5 produces drift_5 tagged summary and PNMLs."""
        # First generate logs_drift_5
        drift_summary = generate_drift_logs(self.source_dir, 5.0)
        drift_logs_dir = drift_summary["output_dir"]

        pnml_dir = os.path.join(self.temp_dir.name, "pnml")
        output_json = os.path.join(self.temp_dir.name, "mined-nets_drift_5.json")
        cmd = [
            sys.executable,
            str(REPO_ROOT / "src" / "miner.py"),
            "--logs-dir",
            drift_logs_dir,
            "--pnml-dir",
            pnml_dir,
            "--output",
            output_json,
            "--noise-threshold",
            "0.0",
        ]
        proc = subprocess.run(cmd, capture_output=True, text=True)
        self.assertEqual(proc.returncode, 0, msg=f"Miner failed: {proc.stderr}")

        # Check that default summary file was written with drift_5 naming
        expected_mining_summary = os.path.join(drift_logs_dir, "mining_drift_5.summary.json")
        self.assertTrue(os.path.isfile(expected_mining_summary))

        # Check that PNML file was exported with drift_5 naming
        expected_pnml = os.path.join(pnml_dir, "test-service_drift_5.pnml")
        self.assertTrue(os.path.isfile(expected_pnml))

        # Check that mined nets JSON was exported
        self.assertTrue(os.path.isfile(output_json))


if __name__ == "__main__":
    unittest.main()
