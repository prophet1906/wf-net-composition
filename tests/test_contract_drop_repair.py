#!/usr/bin/env python3
"""
Unit and Invariant Tests for Contract-Guided DROP-Repair Engine (src/contract_drop_repair.py).

Verifies:
  - Mandatory client send (A_i) contract extraction from IDL and topology oracle.
  - Identification of gap traces missing mandatory sends vs complete traces.
  - Multi-workflow trigger matching (e.g. nginx-web-server, home-timeline-service).
  - Complete purging of gap traces with zero trace remnants.
  - Strict physical observation invariant (0 synthetic events injected).
  - Row order, case order, and timestamp preservation for retained complete traces.
  - CLI execution and summary report serialization.
"""

import csv
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

from src.contract_drop_repair import (
    DEFAULT_MANDATORY_CONTRACTS,
    REQUIRED_CSV_COLUMNS,
    detect_gap_traces_in_rows,
    drop_repair_logs_directory,
    drop_repair_service_log,
    extract_mandatory_sends_from_topology,
    infer_artifact_tag,
    main,
    validate_csv_header,
)


class TestMandatoryContractsExtraction(unittest.TestCase):
    """Test suite validating extraction of mandatory client sends (A_i)."""

    def test_extract_mandatory_sends_from_topology(self):
        """Verify dynamic extraction and default fallbacks for microservices."""
        c_map = extract_mandatory_sends_from_topology(
            topology_path="interfaces/social-network.json",
            contracts_path="interfaces/idl-contracts.json",
        )
        self.assertIn("compose-post-service", c_map)
        cp_sends = c_map["compose-post-service"]["compose_post_server"]
        self.assertIn("store_post_client", cp_sends)
        self.assertIn("compose_text_client", cp_sends)
        self.assertIn("write_home_timeline_client", cp_sends)

        self.assertIn("text-service", c_map)
        txt_sends = c_map["text-service"]["compose_text_server"]
        self.assertIn("compose_urls_client", txt_sends)
        self.assertIn("compose_user_mentions_client", txt_sends)

        self.assertIn("nginx-web-server", c_map)
        self.assertIn("compose_post_client", c_map["nginx-web-server"]["/wrk2-api/post/compose"])


class TestGapTraceDetectionAndPurge(unittest.TestCase):
    """Test suite validating gap trace detection and physical row purging."""

    def setUp(self):
        self.temp_dir = tempfile.TemporaryDirectory()
        self.logs_dir = os.path.join(self.temp_dir.name, "logs")
        self.output_dir = os.path.join(self.temp_dir.name, "output")
        os.makedirs(self.logs_dir, exist_ok=True)
        os.makedirs(self.output_dir, exist_ok=True)

        # Create sample service log for text-service
        # Case 1: Complete trace (has compose_text_server, compose_urls_client, compose_user_mentions_client)
        # Case 2: Gap trace (missing compose_user_mentions_client due to partial tail loss)
        # Case 3: Gap trace (missing both client sends)
        self.text_rows = [
            {"case_id": "c1", "activity": "compose_text_server", "timestamp": "100"},
            {"case_id": "c1", "activity": "compose_urls_client", "timestamp": "110"},
            {"case_id": "c1", "activity": "compose_user_mentions_client", "timestamp": "120"},
            {"case_id": "c2", "activity": "compose_text_server", "timestamp": "200"},
            {"case_id": "c2", "activity": "compose_urls_client", "timestamp": "210"},
            {"case_id": "c3", "activity": "compose_text_server", "timestamp": "300"},
        ]
        self.text_path = os.path.join(self.logs_dir, "text-service.csv")
        with open(self.text_path, "w", encoding="utf-8", newline="") as f:
            writer = csv.DictWriter(f, fieldnames=REQUIRED_CSV_COLUMNS)
            writer.writeheader()
            writer.writerows(self.text_rows)

    def tearDown(self):
        self.temp_dir.cleanup()

    def test_detect_gap_traces_in_rows(self):
        """Verify gap trace classification identifying missing client sends."""
        c_map = extract_mandatory_sends_from_topology()
        complete, gaps, missing = detect_gap_traces_in_rows(
            rows=self.text_rows,
            service_name="text-service",
            contracts_map=c_map,
        )

        self.assertEqual(complete, {"c1"})
        self.assertEqual(gaps, {"c2", "c3"})
        self.assertIn("compose_user_mentions_client", missing["c2"])
        self.assertIn("compose_urls_client", missing["c3"])
        self.assertIn("compose_user_mentions_client", missing["c3"])

    def test_drop_repair_service_log(self):
        """Verify purging gap traces drops all associated rows while preserving complete traces."""
        surviving_rows, fieldnames, stats = drop_repair_service_log(
            csv_path=self.text_path,
        )

        self.assertEqual(stats["input_cases"], 3)
        self.assertEqual(stats["retained_cases"], 1)
        self.assertEqual(stats["dropped_cases"], 2)
        self.assertEqual(stats["input_rows"], 6)
        self.assertEqual(stats["retained_rows"], 3)
        self.assertEqual(stats["dropped_rows"], 3)
        self.assertAlmostEqual(stats["retention_ratio"], 1.0 / 3.0, places=5)
        self.assertTrue(stats["zero_synthetic_events"])
        self.assertTrue(stats["csv_order_preserved"])

        # Check surviving rows are exclusively from c1
        surviving_cases = {r["case_id"] for r in surviving_rows}
        self.assertEqual(surviving_cases, {"c1"})
        self.assertEqual(len(surviving_rows), 3)
        self.assertEqual(surviving_rows[0]["activity"], "compose_text_server")
        self.assertEqual(surviving_rows[1]["activity"], "compose_urls_client")
        self.assertEqual(surviving_rows[2]["activity"], "compose_user_mentions_client")

    def test_drop_repair_logs_directory_lifecycle(self):
        """Verify full directory drop repair, summary serialization, and invariant checks."""
        summary_file = os.path.join(self.output_dir, "custom_drop_summary.json")
        summary = drop_repair_logs_directory(
            logs_dir=self.logs_dir,
            output_dir=self.output_dir,
            summary_file=summary_file,
        )

        self.assertEqual(summary["total_files"], 1)
        self.assertEqual(summary["total_cases_input"], 3)
        self.assertEqual(summary["total_cases_retained"], 1)
        self.assertEqual(summary["total_cases_dropped"], 2)
        self.assertEqual(summary["total_rows_input"], 6)
        self.assertEqual(summary["total_rows_retained"], 3)
        self.assertEqual(summary["total_rows_dropped"], 3)
        self.assertTrue(summary["invariants_verified"]["zero_synthetic_events"])
        self.assertTrue(summary["invariants_verified"]["csv_order_preserved"])
        self.assertTrue(summary["invariants_verified"]["row_retention_sound"])

        # Check saved summary file
        self.assertTrue(os.path.exists(summary_file))
        with open(summary_file, "r", encoding="utf-8") as f:
            loaded = json.load(f)
        self.assertEqual(loaded["total_cases_retained"], 1)


class TestContractDropRepairCLI(unittest.TestCase):
    """Test suite validating CLI arguments and benchmark execution."""

    def test_cli_execution_on_partial_loss_benchmark(self):
        """Verify CLI execution on partial loss benchmark directory."""
        with tempfile.TemporaryDirectory() as tmp_out:
            cmd = [
                sys.executable,
                "src/contract_drop_repair.py",
                "--logs-dir",
                "data/benchmarks/partial/logs_partial_10",
                "--output-dir",
                tmp_out,
            ]
            res = subprocess.run(cmd, capture_output=True, text=True)
            self.assertEqual(res.returncode, 0, f"CLI failed: {res.stderr}")
            self.assertIn("Contract drop repair complete", res.stdout)
            self.assertTrue(os.path.exists(os.path.join(tmp_out, "compose-post-service.csv")))
            self.assertTrue(os.path.exists(os.path.join(tmp_out, "drop_repair_partial_10.summary.json")))

    def test_cli_missing_logs_dir_error(self):
        """Verify CLI error on non-existent input directory."""
        cmd = [
            sys.executable,
            "src/contract_drop_repair.py",
            "--logs-dir",
            "data/benchmarks/non_existent_partial_dir",
        ]
        res = subprocess.run(cmd, capture_output=True, text=True)
        self.assertNotEqual(res.returncode, 0)
        self.assertIn("Error during contract drop repair", res.stderr)


if __name__ == "__main__":
    unittest.main()
