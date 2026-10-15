#!/usr/bin/env python3
"""
Unit and Invariant Tests for Server-Span Proof-of-Call Relabeler (src/proof_of_call_relabeler.py).

Verifies:
  - Alias to canonical resolution and custom rule injection.
  - Distributed trace ID callee server-span proof-of-call indexing and matching.
  - In-place relabeling of drifted caller spans with proof of call.
  - Untouched preservation of caller spans when callee server span is absent.
  - Zero-drop invariants: 100% case retention, exact row count and timestamp preservation.
  - Strict physical observation invariant (0 synthetic events).
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

from src.proof_of_call_relabeler import (
    DEFAULT_DRIFT_RULES,
    PROOF_OF_CALL_TARGETS,
    REQUIRED_CSV_COLUMNS,
    build_alias_to_canonical_map,
    build_proof_of_call_index,
    infer_artifact_tag,
    load_canonical_targets,
    main,
    relabel_logs_directory,
    relabel_service_log,
    validate_csv_header,
)


class TestProofOfCallRelabelerRules(unittest.TestCase):
    """Test suite validating alias mapping and topology resolution."""

    def test_build_alias_to_canonical_map_defaults(self):
        """Verify default drift rules inversion."""
        alias_map = build_alias_to_canonical_map()
        self.assertEqual(alias_map["store_post_client_v2"], "store_post_client")
        self.assertEqual(alias_map["compose_text_grpc_client"], "compose_text_client")
        self.assertEqual(alias_map["unique_id_rpc_client"], "compose_unique_id_client")
        self.assertEqual(alias_map["post_home_timeline_client"], "write_home_timeline_client")
        self.assertEqual(alias_map["get_followers_rpc_client"], "get_followers_client")

    def test_build_alias_to_canonical_map_custom_rules(self):
        """Verify custom drift rules injection."""
        custom = {"custom_caller_span": "custom_canonical_client"}
        alias_map = build_alias_to_canonical_map(custom_rules=custom)
        self.assertEqual(alias_map["custom_caller_span"], "custom_canonical_client")
        self.assertEqual(alias_map["store_post_client_v2"], "store_post_client")

    def test_load_canonical_targets(self):
        """Verify canonical targets mapping to server spans."""
        targets = load_canonical_targets(
            topology_path="interfaces/social-network.json",
        )
        self.assertEqual(targets["store_post_client"], "store_post_server")
        self.assertEqual(targets["compose_text_client"], "compose_text_server")
        self.assertEqual(targets["compose_unique_id_client"], "compose_unique_id_server")
        self.assertEqual(targets["get_followers_client"], "get_followers_server")

    def test_infer_artifact_tag(self):
        """Verify tag extraction across drift, partial, mixed, and baseline directories."""
        self.assertEqual(infer_artifact_tag("data/benchmarks/drift/logs_drift_10"), "drift_10")
        self.assertEqual(infer_artifact_tag("logs_partial_7_5"), "partial_7_5")
        self.assertEqual(infer_artifact_tag("logs_mixed_drift_10_partial_5"), "mixed_drift_10_partial_5")
        self.assertEqual(infer_artifact_tag("data/logs"), "baseline")
        self.assertEqual(infer_artifact_tag(""), "baseline")


class TestProofOfCallIndexingAndRelabeling(unittest.TestCase):
    """Test suite validating proof indexing and in-place service log relabeling."""

    def setUp(self):
        self.temp_dir = tempfile.TemporaryDirectory()
        self.logs_dir = os.path.join(self.temp_dir.name, "logs")
        self.output_dir = os.path.join(self.temp_dir.name, "output")
        os.makedirs(self.logs_dir, exist_ok=True)
        os.makedirs(self.output_dir, exist_ok=True)

        # Create caller service log (compose-post-service)
        # Case 1: Drifted span with callee server span present
        # Case 2: Drifted span with callee server span ABSENT (e.g. dropped RPC)
        # Case 3: Already canonical span
        self.caller_rows = [
            {"case_id": "c1", "activity": "compose_post_server", "timestamp": "1000"},
            {"case_id": "c1", "activity": "store_post_client_v2", "timestamp": "1010"},
            {"case_id": "c2", "activity": "compose_post_server", "timestamp": "2000"},
            {"case_id": "c2", "activity": "store_post_client_v2", "timestamp": "2010"},
            {"case_id": "c3", "activity": "compose_post_server", "timestamp": "3000"},
            {"case_id": "c3", "activity": "store_post_client", "timestamp": "3010"},
        ]
        self.caller_path = os.path.join(self.logs_dir, "compose-post-service.csv")
        with open(self.caller_path, "w", encoding="utf-8", newline="") as f:
            writer = csv.DictWriter(f, fieldnames=REQUIRED_CSV_COLUMNS)
            writer.writeheader()
            writer.writerows(self.caller_rows)

        # Create callee service log (post-storage-service)
        # Only Case 1 and Case 3 contain store_post_server (Case 2 server span missing)
        self.callee_rows = [
            {"case_id": "c1", "activity": "store_post_server", "timestamp": "1015"},
            {"case_id": "c3", "activity": "store_post_server", "timestamp": "3015"},
        ]
        self.callee_path = os.path.join(self.logs_dir, "post-storage-service.csv")
        with open(self.callee_path, "w", encoding="utf-8", newline="") as f:
            writer = csv.DictWriter(f, fieldnames=REQUIRED_CSV_COLUMNS)
            writer.writeheader()
            writer.writerows(self.callee_rows)

    def tearDown(self):
        self.temp_dir.cleanup()

    def test_proof_of_call_indexing(self):
        """Verify proof-of-call index correctly records server spans for matching case_ids."""
        proof_index = build_proof_of_call_index(
            logs_dir=self.logs_dir,
            canonical_targets=PROOF_OF_CALL_TARGETS,
        )
        self.assertIn("c1", proof_index)
        self.assertIn("store_post_server", proof_index["c1"])
        self.assertIn("compose_post_server", proof_index["c1"])

        # c2 has compose_post_server in caller, but store_post_server is absent in callee
        self.assertIn("c2", proof_index)
        self.assertNotIn("store_post_server", proof_index["c2"])

        self.assertIn("c3", proof_index)
        self.assertIn("store_post_server", proof_index["c3"])

    def test_relabel_service_log_proof_verification(self):
        """Verify drifted caller span is relabeled ONLY when callee server span is verified."""
        proof_index = build_proof_of_call_index(logs_dir=self.logs_dir)
        alias_map = build_alias_to_canonical_map()
        targets = PROOF_OF_CALL_TARGETS

        out_rows, fieldnames, stats = relabel_service_log(
            csv_path=self.caller_path,
            proof_index=proof_index,
            alias_map=alias_map,
            canonical_targets=targets,
        )

        self.assertEqual(stats["input_rows"], 6)
        self.assertEqual(stats["output_rows"], 6)
        self.assertEqual(stats["relabeled_count"], 1)
        self.assertEqual(stats["retention_ratio"], 1.0)
        self.assertTrue(stats["row_count_preserved"])
        self.assertTrue(stats["case_count_preserved"])

        # c1 should be relabeled from store_post_client_v2 -> store_post_client
        c1_acts = [r["activity"] for r in out_rows if r["case_id"] == "c1"]
        self.assertIn("store_post_client", c1_acts)
        self.assertNotIn("store_post_client_v2", c1_acts)

        # c2 should REMAIN store_post_client_v2 because store_post_server was absent
        c2_acts = [r["activity"] for r in out_rows if r["case_id"] == "c2"]
        self.assertIn("store_post_client_v2", c2_acts)
        self.assertNotIn("store_post_client", c2_acts)

        # c3 was already canonical
        c3_acts = [r["activity"] for r in out_rows if r["case_id"] == "c3"]
        self.assertIn("store_post_client", c3_acts)

    def test_relabel_logs_directory_full_lifecycle(self):
        """Verify full directory relabeling lifecycle, invariants, and summary generation."""
        summary_file = os.path.join(self.output_dir, "custom_summary.json")
        summary = relabel_logs_directory(
            logs_dir=self.logs_dir,
            output_dir=self.output_dir,
            summary_file=summary_file,
        )

        self.assertEqual(summary["total_files"], 2)
        self.assertEqual(summary["total_cases_input"], 3)
        self.assertEqual(summary["total_cases_output"], 3)
        self.assertEqual(summary["total_rows_input"], 8)
        self.assertEqual(summary["total_rows_output"], 8)
        self.assertEqual(summary["total_relabeled_events"], 1)
        self.assertEqual(summary["retention_ratio"], 1.0)
        self.assertTrue(summary["invariants_verified"]["row_count_preserved"])
        self.assertTrue(summary["invariants_verified"]["case_count_preserved"])
        self.assertTrue(summary["invariants_verified"]["zero_synthetic_events"])
        self.assertTrue(summary["invariants_verified"]["zero_trace_loss"])

        # Verify summary JSON file was created
        self.assertTrue(os.path.exists(summary_file))
        with open(summary_file, "r", encoding="utf-8") as f:
            loaded_summary = json.load(f)
        self.assertEqual(loaded_summary["total_relabeled_events"], 1)


class TestProofOfCallRelabelerCLI(unittest.TestCase):
    """Test suite validating CLI arguments and error handling."""

    def test_cli_execution_on_benchmark_drift(self):
        """Verify CLI execution on drift benchmark directory."""
        with tempfile.TemporaryDirectory() as tmp_out:
            cmd = [
                sys.executable,
                "src/proof_of_call_relabeler.py",
                "--logs-dir",
                "data/benchmarks/drift/logs_drift_10",
                "--output-dir",
                tmp_out,
            ]
            res = subprocess.run(cmd, capture_output=True, text=True)
            self.assertEqual(res.returncode, 0, f"CLI failed: {res.stderr}")
            self.assertIn("Proof-of-call relabeling complete", res.stdout)
            self.assertTrue(os.path.exists(os.path.join(tmp_out, "compose-post-service.csv")))
            self.assertTrue(os.path.exists(os.path.join(tmp_out, "relabel_drift_10.summary.json")))

    def test_cli_missing_logs_dir_error(self):
        """Verify CLI error on non-existent logs directory."""
        cmd = [
            sys.executable,
            "src/proof_of_call_relabeler.py",
            "--logs-dir",
            "data/benchmarks/non_existent_directory",
        ]
        res = subprocess.run(cmd, capture_output=True, text=True)
        self.assertNotEqual(res.returncode, 0)
        self.assertIn("Error during proof-of-call relabeling", res.stderr)


if __name__ == "__main__":
    unittest.main()
