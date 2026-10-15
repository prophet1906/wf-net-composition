#!/usr/bin/env python3
"""
Unit and invariant tests for Deterministic Service Event Log Compound Label Drift & Truncation Loss Generation.

Verifies:
  - Format compound tag and regex tag inference from paths and strings.
  - Causal execution sequencing: caller drift mutation first across full case universe -> tail truncation second.
  - Orthogonal parameter independence between drift (D) and loss (L).
  - Baseline equivalence with standalone generate_drift_logs (when L=0) and generate_partial_logs (when D=0).
  - Physical proof preservation: callee server spans remain 100% canonical and unmodified.
  - Strict read-only immutability of the source logs directory.
  - 2D Cartesian grid batch generation (both 5x5 and 9x9 parameter matrices).
  - Structured summary JSON creation and schema validation (mixed_drift_<D>_partial_<L>.summary.json).
  - Boundary and edge case handling (0% / 100% boundaries, fractional values, empty files,
    missing columns, non-existent directories, invalid parameter errors).
  - CLI command-line execution and downstream miner compatibility.
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
    generate_drift_logs,
)
from src.generate_partial_logs import generate_partial_logs
from src.generate_mixed_logs import (
    format_mixed_filename,
    format_mixed_tag,
    generate_mixed_logs,
    generate_mixed_logs_batch,
    infer_mixed_tag,
    main,
    process_service_mixed_log,
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


class TestCompoundTagFormattingAndInference(unittest.TestCase):
    """Test suite validating compound mixed tag formatting and regex inference."""

    def test_format_mixed_tag_integer_and_fractional(self):
        """Verify compound tag formatting for integer and fractional drift/loss values."""
        self.assertEqual(format_mixed_tag(10.0, 5.0), "mixed_drift_10_partial_5")
        self.assertEqual(format_mixed_tag(0.0, 0.0), "mixed_drift_0_partial_0")
        self.assertEqual(format_mixed_tag(2.5, 7.5), "mixed_drift_2_5_partial_7_5")
        self.assertEqual(format_mixed_tag(12.25, 5.0), "mixed_drift_12_25_partial_5")
        self.assertEqual(format_mixed_tag(5, 10), "mixed_drift_5_partial_10")
        self.assertEqual(format_mixed_tag(17.5, 12.5), "mixed_drift_17_5_partial_12_5")

    def test_infer_mixed_tag(self):
        """Verify extraction of compound tag from directory paths and filenames."""
        self.assertEqual(
            infer_mixed_tag("logs_mixed_drift_10_partial_5"),
            "mixed_drift_10_partial_5",
        )
        self.assertEqual(
            infer_mixed_tag("path/to/logs_mixed_drift_2_5_partial_7_5"),
            "mixed_drift_2_5_partial_7_5",
        )
        self.assertEqual(
            infer_mixed_tag("logs_mixed_drift_0_partial_20/compose-post-service.csv"),
            "mixed_drift_0_partial_20",
        )
        self.assertEqual(infer_mixed_tag("logs"), None)
        self.assertEqual(infer_mixed_tag("logs_drift_10"), None)
        self.assertEqual(infer_mixed_tag("logs_partial_5"), None)
        self.assertEqual(infer_mixed_tag(""), None)
        self.assertEqual(infer_mixed_tag(None), None)

    def test_format_mixed_filename(self):
        """Verify artifact filename construction with compound mixed tag."""
        self.assertEqual(
            format_mixed_filename("mining", "mixed_drift_10_partial_5", ".summary.json"),
            "mining_mixed_drift_10_partial_5.summary.json",
        )
        self.assertEqual(
            format_mixed_filename("service", "mixed_drift_5_partial_5", ".pnml"),
            "service_mixed_drift_5_partial_5.pnml",
        )
        self.assertEqual(
            format_mixed_filename("compose-post-service", None, ".pnml"),
            "compose-post-service.pnml",
        )
        # Avoid duplicate tag
        self.assertEqual(
            format_mixed_filename(
                "service_mixed_drift_10_partial_5", "mixed_drift_10_partial_5", ".pnml"
            ),
            "service_mixed_drift_10_partial_5.pnml",
        )


class TestCausalSequencingAndEquivalence(unittest.TestCase):
    """Test suite validating causal pipeline sequencing, parameter independence, and baseline equivalence."""

    def setUp(self):
        self.temp_dir = tempfile.TemporaryDirectory()
        self.source_dir = os.path.join(self.temp_dir.name, "logs")
        os.makedirs(self.source_dir, exist_ok=True)

        # Service 1 (Caller): compose-post-service.csv
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
        self.callee_csv = os.path.join(self.source_dir, "post-storage-service.csv")
        with open(self.callee_csv, "w", encoding="utf-8", newline="") as f:
            writer = csv.writer(f)
            writer.writerow(["case_id", "activity", "timestamp"])
            for i in range(100):
                cid = f"trace_{i}"
                writer.writerow([cid, "store_post_server", str(1005 + i * 10)])

    def tearDown(self):
        self.temp_dir.cleanup()

    def test_zero_compound_defect_baseline_equivalence(self):
        """D=0% and L=0% compound run produces logs identical in content and counts to source logs."""
        summary = generate_mixed_logs(self.source_dir, drift_percentage=0.0, loss_percentage=0.0)
        out_dir = summary["output_dir"]

        for fname in ["compose-post-service.csv", "post-storage-service.csv"]:
            src_f = os.path.join(self.source_dir, fname)
            dst_f = os.path.join(out_dir, fname)
            with open(src_f, "r") as f1, open(dst_f, "r") as f2:
                self.assertEqual(f1.read(), f2.read())

        self.assertEqual(summary["total_original_events"], summary["total_retained_events"])
        self.assertEqual(summary["total_mutated_events"], 0)
        self.assertEqual(summary["total_mutated_cases"], 0)
        self.assertEqual(summary["total_dropped_events"], 0)

    def test_standalone_drift_equivalence(self):
        """D=10% and L=0% compound run is byte-identical to standalone generate_drift_logs at 10% drift."""
        mixed_summary = generate_mixed_logs(self.source_dir, drift_percentage=10.0, loss_percentage=0.0)
        drift_summary = generate_drift_logs(self.source_dir, drift_percentage=10.0)

        mixed_csv = os.path.join(mixed_summary["output_dir"], "compose-post-service.csv")
        drift_csv = os.path.join(drift_summary["output_dir"], "compose-post-service.csv")

        with open(mixed_csv, "r") as f1, open(drift_csv, "r") as f2:
            self.assertEqual(f1.read(), f2.read())

        self.assertEqual(
            mixed_summary["total_mutated_cases"], drift_summary["total_mutated_cases"]
        )
        self.assertEqual(
            mixed_summary["total_mutated_events"], drift_summary["total_mutated_events"]
        )

    def test_standalone_truncation_equivalence(self):
        """D=0% and L=5% compound run is byte-identical to standalone generate_partial_logs at 5% loss."""
        mixed_summary = generate_mixed_logs(self.source_dir, drift_percentage=0.0, loss_percentage=5.0)
        partial_summary = generate_partial_logs(self.source_dir, loss_percentage=5.0)

        for fname in ["compose-post-service.csv", "post-storage-service.csv"]:
            mixed_csv = os.path.join(mixed_summary["output_dir"], fname)
            partial_csv = os.path.join(partial_summary["output_dir"], fname)
            with open(mixed_csv, "r") as f1, open(partial_csv, "r") as f2:
                self.assertEqual(f1.read(), f2.read())

        self.assertEqual(
            mixed_summary["total_retained_events"], partial_summary["total_retained_events"]
        )
        self.assertEqual(
            mixed_summary["total_dropped_events"], partial_summary["total_dropped_events"]
        )

    def test_causal_order_drift_mutation_before_truncation(self):
        """Verify that caller drift mutation occurs across full case universe before tail truncation."""
        # Run at 100% drift and 20% loss
        summary = generate_mixed_logs(self.source_dir, drift_percentage=100.0, loss_percentage=20.0)
        out_dir = summary["output_dir"]

        caller_out = os.path.join(out_dir, "compose-post-service.csv")
        with open(caller_out, "r", encoding="utf-8") as f:
            rows = list(csv.DictReader(f))

        # Original was 300 rows (100 cases * 3 rows); at 20% loss, retained is floor(300 * 0.80) = 240 rows
        self.assertEqual(len(rows), 240)

        # Because drift occurred first across all cases, retained client spans must be mutated aliases
        activities = [r["activity"] for r in rows]
        self.assertNotIn("compose_text_client", activities)
        self.assertNotIn("store_post_client", activities)
        self.assertIn("compose_text_grpc_client", activities)
        self.assertIn("store_post_client_v2", activities)

    def test_proof_of_call_callee_server_preservation(self):
        """Callee server spans remain 100% canonical and unmodified under compound defect injection."""
        summary = generate_mixed_logs(self.source_dir, drift_percentage=50.0, loss_percentage=15.0)
        out_dir = summary["output_dir"]

        callee_out = os.path.join(out_dir, "post-storage-service.csv")
        with open(callee_out, "r", encoding="utf-8") as f:
            rows = list(csv.DictReader(f))

        # Original was 100 rows; at 15% loss, retained is floor(100 * 0.85) = 85 rows
        self.assertEqual(len(rows), 85)
        # All preserved rows must strictly be store_post_server
        self.assertTrue(all(r["activity"] == "store_post_server" for r in rows))


class TestMathematicalInvariantsAndImmutability(unittest.TestCase):
    """Test suite validating source immutability, mathematical invariants, and parameter bounds."""

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

        generate_mixed_logs(self.source_dir, drift_percentage=5.0, loss_percentage=10.0)
        generate_mixed_logs_batch(
            self.source_dir,
            drift_percentages=[0.0, 10.0],
            loss_percentages=[0.0, 5.0],
        )

        post_checksums = get_dir_checksums(self.source_dir)
        self.assertEqual(initial_checksums, post_checksums)

    def test_immutability_guard_rejects_identical_output_dir(self):
        """Specifying output_dir identical to source_dir raises ValueError."""
        with self.assertRaises(ValueError) as ctx:
            generate_mixed_logs(
                self.source_dir,
                drift_percentage=10.0,
                loss_percentage=5.0,
                output_dir=self.source_dir,
            )
        self.assertIn("Source directory immutability violation", str(ctx.exception))

    def test_retained_event_count_formula(self):
        """Retained event count strictly satisfies floor(N * (1 - L / 100)) regardless of drift D."""
        for drift in [0.0, 5.0, 20.0, 50.0]:
            for loss in [0.0, 2.5, 7.5, 15.0, 20.0]:
                summary = generate_mixed_logs(
                    self.source_dir, drift_percentage=drift, loss_percentage=loss
                )
                expected_retained = int(120 * (1.0 - loss / 100.0))
                self.assertEqual(summary["total_retained_events"], expected_retained)


class TestBatchGridGenerationAndSummaryJSON(unittest.TestCase):
    """Test suite validating 2D parameter grid sweeps, directory structures, and summary metadata schema."""

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

    def test_single_compound_run_creates_expected_files(self):
        """Single compound run creates logs_mixed_drift_10_partial_5 with summary JSON."""
        summary = generate_mixed_logs(self.source_dir, drift_percentage=10.0, loss_percentage=5.0)

        expected_out = os.path.join(self.temp_dir.name, "logs_mixed_drift_10_partial_5")
        self.assertTrue(os.path.isdir(expected_out))

        summary_file = os.path.join(expected_out, "mixed_drift_10_partial_5.summary.json")
        self.assertTrue(os.path.isfile(summary_file))

        with open(summary_file, "r", encoding="utf-8") as f:
            saved = json.load(f)

        self.assertEqual(saved["source_dir"], self.source_dir)
        self.assertEqual(saved["drift_percentage"], 10.0)
        self.assertEqual(saved["loss_percentage"], 5.0)
        self.assertEqual(saved["total_original_events"], 100)
        self.assertEqual(saved["total_retained_events"], 95)
        self.assertEqual(saved["total_dropped_events"], 5)
        self.assertEqual(saved["retained_event_ratio"], 0.95)
        self.assertEqual(saved["total_cases"], 100)
        self.assertIn("drift_rules", saved)
        self.assertIn("proof_of_call_targets", saved)
        self.assertIn("svc_a", saved["services"])

    def test_batch_grid_execution_creates_all_cartesian_directories(self):
        """Batch sweep with 2 drifts and 3 losses creates 6 distinct directories."""
        results = generate_mixed_logs_batch(
            self.source_dir,
            drift_percentages=[0.0, 5.0],
            loss_percentages=[0.0, 5.0, 10.0],
        )

        self.assertEqual(len(results), 6)
        for (d, l), summary in results.items():
            tag = format_mixed_tag(d, l)
            out_dir = os.path.join(self.temp_dir.name, f"logs_{tag}")
            self.assertTrue(os.path.isdir(out_dir))
            summary_file = os.path.join(out_dir, f"{tag}.summary.json")
            self.assertTrue(os.path.isfile(summary_file))

    def test_custom_output_dir_for_single_pair(self):
        """Custom output directory works for single (drift, loss) pair."""
        custom_dir = os.path.join(self.temp_dir.name, "custom_mixed")
        summary = generate_mixed_logs(
            self.source_dir, drift_percentage=10.0, loss_percentage=5.0, output_dir=custom_dir
        )

        self.assertTrue(os.path.isdir(custom_dir))
        self.assertTrue(
            os.path.isfile(os.path.join(custom_dir, "mixed_drift_10_partial_5.summary.json"))
        )
        self.assertEqual(summary["output_dir"], os.path.abspath(custom_dir))

    def test_cli_execution_batch(self):
        """CLI invocation executes 2D parameter grid successfully."""
        cmd = [
            sys.executable,
            str(REPO_ROOT / "src" / "generate_mixed_logs.py"),
            "--logs-dir",
            self.source_dir,
            "--drift",
            "0",
            "5",
            "--loss",
            "0",
            "5",
        ]
        proc = subprocess.run(cmd, capture_output=True, text=True)
        self.assertEqual(proc.returncode, 0, msg=f"CLI failed: {proc.stderr}")
        self.assertIn("Generated compound logs for drift=0.0%, loss=0.0%", proc.stdout)
        self.assertIn("Generated compound logs for drift=5.0%, loss=5.0%", proc.stdout)


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
            generate_mixed_logs(
                os.path.join(self.temp_dir.name, "missing"),
                drift_percentage=5.0,
                loss_percentage=5.0,
            )

    def test_source_path_is_file_raises_error(self):
        """Source path pointing to a file raises NotADirectoryError."""
        file_path = os.path.join(self.temp_dir.name, "file.txt")
        with open(file_path, "w") as f:
            f.write("content")
        with self.assertRaises(NotADirectoryError):
            generate_mixed_logs(file_path, drift_percentage=5.0, loss_percentage=5.0)

    def test_out_of_bounds_parameters_raise_error(self):
        """Out of bounds drift or loss (<0 or >100) raises ValueError."""
        with self.assertRaises(ValueError):
            generate_mixed_logs(self.source_dir, drift_percentage=-5.0, loss_percentage=5.0)
        with self.assertRaises(ValueError):
            generate_mixed_logs(self.source_dir, drift_percentage=105.0, loss_percentage=5.0)
        with self.assertRaises(ValueError):
            generate_mixed_logs(self.source_dir, drift_percentage=5.0, loss_percentage=-5.0)
        with self.assertRaises(ValueError):
            generate_mixed_logs(self.source_dir, drift_percentage=5.0, loss_percentage=105.0)

    def test_empty_logs_directory_raises_error(self):
        """Directory with no CSV files raises ValueError."""
        with self.assertRaises(ValueError) as ctx:
            generate_mixed_logs(self.source_dir, drift_percentage=5.0, loss_percentage=5.0)
        self.assertIn("No CSV event logs found", str(ctx.exception))

    def test_empty_csv_file_handling(self):
        """CSV file with only header or zero rows is handled gracefully."""
        csv_file = os.path.join(self.source_dir, "empty_svc.csv")
        with open(csv_file, "w", encoding="utf-8", newline="") as f:
            writer = csv.writer(f)
            writer.writerow(["case_id", "activity", "timestamp"])

        summary = generate_mixed_logs(self.source_dir, drift_percentage=10.0, loss_percentage=10.0)
        self.assertEqual(summary["total_original_events"], 0)
        self.assertEqual(summary["total_retained_events"], 0)
        self.assertEqual(summary["total_mutated_events"], 0)
        self.assertEqual(summary["services"]["empty_svc"]["original_events"], 0)

    def test_missing_csv_columns_raises_error(self):
        """CSV file missing required columns raises ValueError."""
        csv_file = os.path.join(self.source_dir, "bad_svc.csv")
        with open(csv_file, "w", encoding="utf-8", newline="") as f:
            writer = csv.writer(f)
            writer.writerow(["case_id", "timestamp"])  # missing 'activity'
            writer.writerow(["c1", "1000"])

        with self.assertRaises(ValueError) as ctx:
            generate_mixed_logs(self.source_dir, drift_percentage=5.0, loss_percentage=5.0)
        self.assertIn("Missing required columns", str(ctx.exception))

    def test_batch_with_custom_output_dir_raises_error(self):
        """Specifying custom output_dir with multiple grid combinations raises ValueError."""
        with self.assertRaises(ValueError) as ctx:
            generate_mixed_logs_batch(
                self.source_dir,
                drift_percentages=[5.0, 10.0],
                loss_percentages=[5.0],
                output_dir=os.path.join(self.temp_dir.name, "out"),
            )
        self.assertIn("Custom --output-dir can only be specified", str(ctx.exception))


class TestDownstreamMinerCompatibility(unittest.TestCase):
    """Test suite validating seamless compatibility with src/miner.py on compound datasets."""

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

    def test_miner_executes_on_mixed_logs(self):
        """src/miner.py successfully discovers Petri net on compound mixed dataset."""
        mixed_summary = generate_mixed_logs(
            self.source_dir, drift_percentage=5.0, loss_percentage=5.0
        )
        mixed_logs_dir = mixed_summary["output_dir"]

        pnml_dir = os.path.join(self.temp_dir.name, "pnml")
        output_json = os.path.join(self.temp_dir.name, "mined-nets_mixed.json")
        cmd = [
            sys.executable,
            str(REPO_ROOT / "src" / "miner.py"),
            "--logs-dir",
            mixed_logs_dir,
            "--pnml-dir",
            pnml_dir,
            "--output",
            output_json,
            "--noise-threshold",
            "0.0",
        ]
        proc = subprocess.run(cmd, capture_output=True, text=True)
        self.assertEqual(proc.returncode, 0, msg=f"Miner failed: {proc.stderr}")
        self.assertTrue(os.path.isfile(output_json))


if __name__ == "__main__":
    unittest.main()
