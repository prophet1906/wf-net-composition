#!/usr/bin/env python3
"""
Unit and invariant tests for Deterministic Service Event Log Partial Loss Generation.

Verifies:
  - Format loss tag and partial tag inference from paths and strings.
  - Deterministic tail-truncation arithmetic: K = floor(N * (1 - loss / 100)).
  - Preservation of CSV headers, row order, and schema types.
  - Strict read-only immutability of the source logs directory.
  - Batch execution and directory structure creation (logs_partial_<percentage>).
  - Structured summary JSON creation and schema validation (loss_partial_<tag>.summary.json).
  - Boundary and edge case handling (0% loss, 100% loss, fractional loss, empty files,
    missing columns, non-existent directories, invalid loss parameters).
  - CLI command-line execution and integration with downstream tools.
"""

import csv
import hashlib
import json
import math
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

# Add repository root to path
REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT))

from src.generate_partial_logs import (
    REQUIRED_CSV_COLUMNS,
    format_loss_tag,
    format_partial_filename,
    generate_partial_logs,
    generate_partial_logs_batch,
    infer_partial_tag,
    main,
    process_service_log,
    truncate_event_rows,
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
    """Test suite validating loss tag formatting and regex inference."""

    def test_format_loss_tag(self):
        """Verify loss percentage formatting for integer and fractional values."""
        self.assertEqual(format_loss_tag(5.0), "partial_5")
        self.assertEqual(format_loss_tag(5), "partial_5")
        self.assertEqual(format_loss_tag(10.0), "partial_10")
        self.assertEqual(format_loss_tag(0.0), "partial_0")
        self.assertEqual(format_loss_tag(100.0), "partial_100")
        self.assertEqual(format_loss_tag(7.5), "partial_7_5")
        self.assertEqual(format_loss_tag(12.25), "partial_12_25")

    def test_infer_partial_tag(self):
        """Verify extraction of partial tag from various paths and strings."""
        self.assertEqual(infer_partial_tag("logs_partial_5"), "partial_5")
        self.assertEqual(infer_partial_tag("path/to/logs_partial_10"), "partial_10")
        self.assertEqual(infer_partial_tag("logs_partial_7_5/media-service.csv"), "partial_7_5")
        self.assertEqual(infer_partial_tag("partial_20"), "partial_20")
        self.assertEqual(infer_partial_tag("logs"), None)
        self.assertEqual(infer_partial_tag("logs/compose-post-service.csv"), None)
        self.assertEqual(infer_partial_tag(""), None)
        self.assertEqual(infer_partial_tag(None), None)

    def test_format_partial_filename(self):
        """Verify artifact filename construction with partial tag."""
        self.assertEqual(
            format_partial_filename("mining", "partial_5", ".summary.json"),
            "mining_partial_5.summary.json",
        )
        self.assertEqual(
            format_partial_filename("compose-post-service", "partial_10", ".pnml"),
            "compose-post-service_partial_10.pnml",
        )
        self.assertEqual(
            format_partial_filename("media-service", None, ".pnml"),
            "media-service.pnml",
        )
        # Avoid duplicate tag
        self.assertEqual(
            format_partial_filename("service_partial_5", "partial_5", ".pnml"),
            "service_partial_5.pnml",
        )


class TestTruncationArithmetic(unittest.TestCase):
    """Test suite validating exact tail-truncation math and row ordering."""

    def test_truncate_event_rows_single_case(self):
        """100 events at 5% loss retains first 95 events in order."""
        rows = [{"case_id": f"c_{i}", "activity": f"act_{i}", "timestamp": str(1000 + i)} for i in range(100)]
        retained, orig_n, ret_k = truncate_event_rows(rows, 5.0)

        self.assertEqual(orig_n, 100)
        self.assertEqual(ret_k, 95)
        self.assertEqual(len(retained), 95)
        self.assertEqual(retained[0]["activity"], "act_0")
        self.assertEqual(retained[-1]["activity"], "act_94")

    def test_truncate_event_rows_fractional_floor(self):
        """121 events at 10% loss retains floor(121 * 0.90) = 108 events."""
        rows = [{"case_id": f"c_{i}", "activity": f"act_{i}", "timestamp": str(1000 + i)} for i in range(121)]
        retained, orig_n, ret_k = truncate_event_rows(rows, 10.0)

        self.assertEqual(orig_n, 121)
        self.assertEqual(ret_k, 108)
        self.assertEqual(len(retained), 108)
        self.assertEqual(retained[-1]["activity"], "act_107")

    def test_truncate_event_rows_zero_loss(self):
        """0% loss retains 100% of event rows."""
        rows = [{"case_id": f"c_{i}", "activity": f"act_{i}", "timestamp": str(i)} for i in range(50)]
        retained, orig_n, ret_k = truncate_event_rows(rows, 0.0)

        self.assertEqual(orig_n, 50)
        self.assertEqual(ret_k, 50)
        self.assertEqual(retained, rows)

    def test_truncate_event_rows_100_percent_loss(self):
        """100% loss drops all event rows."""
        rows = [{"case_id": f"c_{i}", "activity": f"act_{i}", "timestamp": str(i)} for i in range(50)]
        retained, orig_n, ret_k = truncate_event_rows(rows, 100.0)

        self.assertEqual(orig_n, 50)
        self.assertEqual(ret_k, 0)
        self.assertEqual(len(retained), 0)

    def test_truncate_event_rows_empty_input(self):
        """Empty row list returns empty without errors."""
        retained, orig_n, ret_k = truncate_event_rows([], 20.0)
        self.assertEqual(orig_n, 0)
        self.assertEqual(ret_k, 0)
        self.assertEqual(retained, [])


class TestSourceDirectoryImmutability(unittest.TestCase):
    """Test suite validating that source logs are strictly read-only and never mutated."""

    def setUp(self):
        self.temp_dir = tempfile.TemporaryDirectory()
        self.source_dir = os.path.join(self.temp_dir.name, "source_logs")
        os.makedirs(self.source_dir, exist_ok=True)

        # Create two sample service logs
        self.csv1 = os.path.join(self.source_dir, "svc1.csv")
        with open(self.csv1, "w", encoding="utf-8", newline="") as f:
            writer = csv.writer(f)
            writer.writerow(["case_id", "activity", "timestamp"])
            for i in range(100):
                writer.writerow([f"case_{i}", f"act_{i % 5}", str(1000 + i)])

        self.csv2 = os.path.join(self.source_dir, "svc2.csv")
        with open(self.csv2, "w", encoding="utf-8", newline="") as f:
            writer = csv.writer(f)
            writer.writerow(["case_id", "activity", "timestamp"])
            for i in range(50):
                writer.writerow([f"case_{i}", f"act_{i % 3}", str(2000 + i)])

    def tearDown(self):
        self.temp_dir.cleanup()

    def test_source_files_remain_identical_after_execution(self):
        """Source directory files and checksums remain untouched after single and batch runs."""
        initial_checksums = get_dir_checksums(self.source_dir)

        # Execute generation for 5% and 15% loss
        generate_partial_logs(self.source_dir, 5.0)
        generate_partial_logs(self.source_dir, 15.0)

        post_checksums = get_dir_checksums(self.source_dir)
        self.assertEqual(initial_checksums, post_checksums)

    def test_immutability_guard_rejects_identical_output_dir(self):
        """Attempting to specify output_dir identical to source_dir raises ValueError."""
        with self.assertRaises(ValueError) as ctx:
            generate_partial_logs(self.source_dir, 10.0, output_dir=self.source_dir)
        self.assertIn("Source directory immutability violation", str(ctx.exception))


class TestBatchGenerationAndSummaryJSON(unittest.TestCase):
    """Test suite validating batch generation, output folder structures, and summary metrics."""

    def setUp(self):
        self.temp_dir = tempfile.TemporaryDirectory()
        self.source_dir = os.path.join(self.temp_dir.name, "logs")
        os.makedirs(self.source_dir, exist_ok=True)

        # Create service CSVs with known counts
        # Service A: 200 events across 20 cases
        with open(os.path.join(self.source_dir, "service-a.csv"), "w", encoding="utf-8", newline="") as f:
            writer = csv.writer(f)
            writer.writerow(["case_id", "activity", "timestamp"])
            for i in range(200):
                writer.writerow([f"c_{i % 20}", f"step_{i % 4}", str(1000 + i)])

        # Service B: 100 events across 10 cases
        with open(os.path.join(self.source_dir, "service-b.csv"), "w", encoding="utf-8", newline="") as f:
            writer = csv.writer(f)
            writer.writerow(["case_id", "activity", "timestamp"])
            for i in range(100):
                writer.writerow([f"c_{i % 10}", f"step_{i % 2}", str(2000 + i)])

    def tearDown(self):
        self.temp_dir.cleanup()

    def test_single_loss_generation_creates_expected_files(self):
        """Single loss run creates logs_partial_5 with truncated CSVs and loss_partial_5.summary.json."""
        summary = generate_partial_logs(self.source_dir, 5.0)

        expected_out = os.path.join(self.temp_dir.name, "logs_partial_5")
        self.assertTrue(os.path.isdir(expected_out))

        summary_file = os.path.join(expected_out, "loss_partial_5.summary.json")
        self.assertTrue(os.path.isfile(summary_file))

        with open(summary_file, "r", encoding="utf-8") as f:
            saved_summary = json.load(f)

        self.assertEqual(saved_summary["source_dir"], self.source_dir)
        self.assertEqual(saved_summary["loss_percentage"], 5.0)
        self.assertEqual(saved_summary["total_original_events"], 300)
        # Service A: floor(200 * 0.95) = 190, Service B: floor(100 * 0.95) = 95 -> Total: 285
        self.assertEqual(saved_summary["total_retained_events"], 285)
        self.assertEqual(saved_summary["total_dropped_events"], 15)
        self.assertEqual(saved_summary["retained_event_ratio"], 0.95)
        self.assertEqual(saved_summary["total_retained_cases"], 20)

        # Check service A details
        self.assertEqual(saved_summary["services"]["service-a"]["original_events"], 200)
        self.assertEqual(saved_summary["services"]["service-a"]["retained_events"], 190)
        self.assertEqual(saved_summary["services"]["service-a"]["dropped_events"], 10)
        self.assertEqual(saved_summary["services"]["service-a"]["retained_cases"], 20)

        # Check service B details
        self.assertEqual(saved_summary["services"]["service-b"]["original_events"], 100)
        self.assertEqual(saved_summary["services"]["service-b"]["retained_events"], 95)
        self.assertEqual(saved_summary["services"]["service-b"]["dropped_events"], 5)
        self.assertEqual(saved_summary["services"]["service-b"]["retained_cases"], 10)

        # Verify output CSV file contents and header preservation
        out_csv_a = os.path.join(expected_out, "service-a.csv")
        with open(out_csv_a, "r", encoding="utf-8") as f:
            reader = list(csv.reader(f))
            self.assertEqual(reader[0], ["case_id", "activity", "timestamp"])
            self.assertEqual(len(reader), 191)  # 1 header + 190 data rows

    def test_batch_generation_creates_multiple_directories(self):
        """Batch run with --loss 5 10 20 creates distinct directories."""
        results = generate_partial_logs_batch(self.source_dir, [5.0, 10.0, 20.0])

        self.assertEqual(len(results), 3)
        for loss in [5.0, 10.0, 20.0]:
            tag = format_loss_tag(loss)
            out_dir = os.path.join(self.temp_dir.name, f"logs_{tag}")
            self.assertTrue(os.path.isdir(out_dir))
            summary_file = os.path.join(out_dir, f"loss_{tag}.summary.json")
            self.assertTrue(os.path.isfile(summary_file))

    def test_custom_output_dir_for_single_loss(self):
        """Custom output directory works for single loss runs."""
        custom_dir = os.path.join(self.temp_dir.name, "my_custom_partial")
        summary = generate_partial_logs(self.source_dir, 10.0, output_dir=custom_dir)

        self.assertTrue(os.path.isdir(custom_dir))
        self.assertTrue(os.path.isfile(os.path.join(custom_dir, "loss_partial_10.summary.json")))
        self.assertEqual(summary["output_dir"], os.path.abspath(custom_dir))

    def test_cli_execution_batch(self):
        """CLI invocation executes batch run successfully."""
        cmd = [
            sys.executable,
            str(REPO_ROOT / "src" / "generate_partial_logs.py"),
            "--logs-dir",
            self.source_dir,
            "--loss",
            "5",
            "10",
        ]
        proc = subprocess.run(cmd, capture_output=True, text=True)
        self.assertEqual(proc.returncode, 0, msg=f"CLI failed: {proc.stderr}")
        self.assertIn("Generated partial logs for loss=5.0%", proc.stdout)
        self.assertIn("Generated partial logs for loss=10.0%", proc.stdout)


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
            generate_partial_logs(os.path.join(self.temp_dir.name, "missing"), 5.0)

    def test_source_path_is_file_raises_error(self):
        """Source path pointing to a file raises NotADirectoryError."""
        file_path = os.path.join(self.temp_dir.name, "file.txt")
        with open(file_path, "w") as f:
            f.write("content")
        with self.assertRaises(NotADirectoryError):
            generate_partial_logs(file_path, 5.0)

    def test_out_of_bounds_loss_raises_error(self):
        """Loss percentage < 0 or > 100 raises ValueError."""
        with self.assertRaises(ValueError):
            generate_partial_logs(self.source_dir, -5.0)
        with self.assertRaises(ValueError):
            generate_partial_logs(self.source_dir, 105.0)

    def test_empty_logs_directory_raises_error(self):
        """Directory with no CSV files raises ValueError."""
        with self.assertRaises(ValueError) as ctx:
            generate_partial_logs(self.source_dir, 5.0)
        self.assertIn("No CSV event logs found", str(ctx.exception))

    def test_empty_csv_file_handling(self):
        """CSV file with only header or zero rows is handled gracefully."""
        csv_file = os.path.join(self.source_dir, "empty_svc.csv")
        with open(csv_file, "w", encoding="utf-8", newline="") as f:
            writer = csv.writer(f)
            writer.writerow(["case_id", "activity", "timestamp"])

        summary = generate_partial_logs(self.source_dir, 10.0)
        self.assertEqual(summary["total_original_events"], 0)
        self.assertEqual(summary["total_retained_events"], 0)
        self.assertEqual(summary["total_dropped_events"], 0)
        self.assertEqual(summary["services"]["empty_svc"]["original_events"], 0)
        self.assertEqual(summary["services"]["empty_svc"]["retained_events"], 0)

    def test_missing_csv_columns_raises_error(self):
        """CSV file missing required columns raises ValueError."""
        csv_file = os.path.join(self.source_dir, "bad_svc.csv")
        with open(csv_file, "w", encoding="utf-8", newline="") as f:
            writer = csv.writer(f)
            writer.writerow(["case_id", "timestamp"])  # missing 'activity'
            writer.writerow(["c1", "1000"])

        with self.assertRaises(ValueError) as ctx:
            generate_partial_logs(self.source_dir, 5.0)
        self.assertIn("Missing required columns", str(ctx.exception))

    def test_batch_with_custom_output_dir_raises_error(self):
        """Specifying custom output_dir with multiple loss percentages raises ValueError."""
        with self.assertRaises(ValueError) as ctx:
            generate_partial_logs_batch(
                self.source_dir,
                [5.0, 10.0],
                output_dir=os.path.join(self.temp_dir.name, "out"),
            )
        self.assertIn("Custom --output-dir can only be specified", str(ctx.exception))


class TestDownstreamMinerCompatibility(unittest.TestCase):
    """Test suite validating seamless compatibility with src/miner.py and partial tag propagation."""

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

    def test_miner_adopts_partial_tag_naming(self):
        """src/miner.py run against logs_partial_5 produces partial_5 tagged summary and PNMLs."""
        # First generate logs_partial_5
        partial_summary = generate_partial_logs(self.source_dir, 5.0)
        partial_logs_dir = partial_summary["output_dir"]

        pnml_dir = os.path.join(self.temp_dir.name, "pnml")
        cmd = [
            sys.executable,
            str(REPO_ROOT / "src" / "miner.py"),
            "--logs-dir",
            partial_logs_dir,
            "--pnml-dir",
            pnml_dir,
            "--noise-threshold",
            "0.0",
        ]
        proc = subprocess.run(cmd, capture_output=True, text=True)
        self.assertEqual(proc.returncode, 0, msg=f"Miner failed: {proc.stderr}")

        # Check that default summary file was written with partial_5 naming
        expected_mining_summary = os.path.join(partial_logs_dir, "mining_partial_5.summary.json")
        self.assertTrue(os.path.isfile(expected_mining_summary))

        # Check that PNML file was exported with partial_5 naming
        expected_pnml = os.path.join(pnml_dir, "test-service_partial_5.pnml")
        self.assertTrue(os.path.isfile(expected_pnml))


if __name__ == "__main__":
    unittest.main()
