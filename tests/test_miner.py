#!/usr/bin/env python3
"""
Unit tests for the Noise-Unfiltered Inductive Process Miner (src/miner.py).

Verifies:
  - Strict invariant rejection of noise_threshold > 0.0.
  - 100% trace variant retention across synthetic and real service logs.
  - Sound Petri net discovery (places, visible/silent transitions, arcs, markings).
  - JSON serialization format and standard PNML export compatibility.
  - Mining summary metric consistency.
  - CLI execution for single-service and batch discovery modes.
"""

import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

import pandas as pd
import pm4py

# Add repository root to path
REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT))

from src.miner import (
    calculate_mining_summary,
    discover_service_net,
    export_diagrams,
    export_pnml,
    get_log_statistics,
    load_event_log,
    process_all_logs,
    process_service_log,
    serialize_petri_net_to_dict,
)


class TestNoiseThresholdInvariant(unittest.TestCase):
    """Test suite verifying strict invariant enforcement: noise_threshold must be strictly 0.0."""

    def setUp(self):
        self.temp_dir = tempfile.TemporaryDirectory()
        self.csv_path = os.path.join(self.temp_dir.name, "test-service.csv")
        # Create a minimal event log with 2 variants
        rows = [
            "case_id,activity,timestamp\n",
            "c1,actA,1000\n",
            "c1,actB,2000\n",
            "c2,actA,1000\n",
            "c2,actC,2000\n",
        ]
        with open(self.csv_path, "w", encoding="utf-8") as f:
            f.writelines(rows)

        self.df = load_event_log(self.csv_path)

    def tearDown(self):
        self.temp_dir.cleanup()

    def test_zero_noise_threshold_succeeds(self):
        """noise_threshold = 0.0 discovers Petri net successfully."""
        net, im, fm = discover_service_net(self.df, noise_threshold=0.0)
        self.assertIsNotNone(net)
        self.assertGreater(len(net.places), 0)
        self.assertGreater(len(net.transitions), 0)

    def test_nonzero_noise_threshold_raises_value_error(self):
        """Any noise_threshold > 0.0 or != 0.0 raises a strict ValueError."""
        for invalid_threshold in [0.01, 0.1, 0.2, 0.5, 1.0, -0.1]:
            with self.subTest(threshold=invalid_threshold):
                with self.assertRaises(ValueError) as ctx:
                    discover_service_net(self.df, noise_threshold=invalid_threshold)
                self.assertIn("Strict Invariant Violation", str(ctx.exception))
                self.assertIn("noise_threshold must be strictly 0.0", str(ctx.exception))

    def test_cli_rejects_nonzero_noise_threshold(self):
        """CLI invocation with --noise-threshold > 0 exits with non-zero code."""
        cmd = [
            sys.executable,
            str(REPO_ROOT / "src" / "miner.py"),
            "--log",
            self.csv_path,
            "--noise-threshold",
            "0.2",
        ]
        proc = subprocess.run(cmd, capture_output=True, text=True)
        self.assertNotEqual(proc.returncode, 0)
        self.assertIn("Strict Invariant Violation", proc.stderr)


class TestEventLogIngestion(unittest.TestCase):
    """Test suite validating CSV event log loading and mapping."""

    def setUp(self):
        self.temp_dir = tempfile.TemporaryDirectory()

    def tearDown(self):
        self.temp_dir.cleanup()

    def test_load_event_log_maps_columns_and_preserves_order(self):
        """Event log maps case_id, activity, timestamp to canonical pm4py columns."""
        csv_file = os.path.join(self.temp_dir.name, "sample.csv")
        with open(csv_file, "w", encoding="utf-8") as f:
            f.write("case_id,activity,timestamp\n")
            f.write("trace_1,start,100\n")
            f.write("trace_1,process,200\n")
            f.write("trace_1,end,300\n")

        df = load_event_log(csv_file)
        self.assertIn("case:concept:name", df.columns)
        self.assertIn("concept:name", df.columns)
        self.assertIn("time:timestamp", df.columns)
        self.assertEqual(len(df), 3)
        self.assertEqual(list(df["concept:name"]), ["start", "process", "end"])

    def test_load_missing_file_raises_error(self):
        """Non-existent file raises FileNotFoundError."""
        with self.assertRaises(FileNotFoundError):
            load_event_log(os.path.join(self.temp_dir.name, "missing.csv"))

    def test_load_empty_file_raises_error(self):
        """Empty CSV raises ValueError."""
        empty_file = os.path.join(self.temp_dir.name, "empty.csv")
        with open(empty_file, "w", encoding="utf-8") as f:
            f.write("case_id,activity,timestamp\n")
        with self.assertRaises(ValueError):
            load_event_log(empty_file)

    def test_load_missing_columns_raises_error(self):
        """CSV missing required columns raises ValueError."""
        invalid_file = os.path.join(self.temp_dir.name, "invalid.csv")
        with open(invalid_file, "w", encoding="utf-8") as f:
            f.write("case_id,activity\n")
            f.write("c1,actA\n")
        with self.assertRaises(ValueError):
            load_event_log(invalid_file)


class TestVariantRetentionAndModelStructure(unittest.TestCase):
    """Test suite verifying 100% trace variant retention and Petri net structure."""

    def test_anomaly_and_rare_variant_retention(self):
        """Infrequent / single-occurrence anomaly variants are 100% retained."""
        with tempfile.TemporaryDirectory() as tmp_dir:
            csv_path = os.path.join(tmp_dir, "anomaly_service.csv")
            rows = ["case_id,activity,timestamp\n"]
            # 99 cases of standard path: A -> B -> C
            for i in range(99):
                rows.append(f"case_{i},actA,{1000 + i*10}\n")
                rows.append(f"case_{i},actB,{1001 + i*10}\n")
                rows.append(f"case_{i},actC,{1002 + i*10}\n")
            # 1 case of rare dropped RPC path (data loss artifact): A -> C (missing B)
            rows.append("case_rare_drop,actA,2000\n")
            rows.append("case_rare_drop,actC,2001\n")

            with open(csv_path, "w", encoding="utf-8") as f:
                f.writelines(rows)

            df = load_event_log(csv_path)
            case_count, event_count, variant_count = get_log_statistics(df)
            self.assertEqual(case_count, 100)
            self.assertEqual(event_count, 299)
            self.assertEqual(variant_count, 2)

            net_dict, summary = process_service_log(csv_path, noise_threshold=0.0)

            self.assertEqual(summary["case_count"], 100)
            self.assertEqual(summary["event_count"], 299)
            self.assertEqual(summary["variant_count"], 2)
            self.assertEqual(summary["noise_threshold"], 0.0)
            self.assertTrue(summary["all_variants_retained"])
            self.assertEqual(net_dict["variant_retention"], "100%")

    def test_real_deathstarbench_logs_discovery(self):
        """Verify discovery across real DeathStarBench service event logs in data/logs/."""
        logs_dir = REPO_ROOT / "data" / "logs"
        if not logs_dir.exists():
            self.skipTest("data/logs/ directory not present")

        csv_files = [f for f in os.listdir(logs_dir) if f.endswith(".csv")]
        self.assertGreaterEqual(len(csv_files), 10)

        for fname in sorted(csv_files):
            csv_path = str(logs_dir / fname)
            with self.subTest(service=fname):
                df = load_event_log(csv_path)
                case_count, event_count, variant_count = get_log_statistics(df)
                self.assertGreater(case_count, 0)
                self.assertGreater(event_count, 0)
                self.assertGreater(variant_count, 0)

                net, im, fm = discover_service_net(df, noise_threshold=0.0)
                self.assertGreaterEqual(len(net.places), 2)
                self.assertGreaterEqual(len(net.transitions), 1)
                self.assertGreaterEqual(len(net.arcs), 2)
                self.assertEqual(sum(im.values()), 1)
                self.assertEqual(sum(fm.values()), 1)


class TestSerializationAndExports(unittest.TestCase):
    """Test suite validating JSON serialization, PNML export, and summary metric consistency."""

    def setUp(self):
        self.temp_dir = tempfile.TemporaryDirectory()
        self.csv_path = str(REPO_ROOT / "data" / "logs" / "media-service.csv")

    def tearDown(self):
        self.temp_dir.cleanup()

    def test_serialize_petri_net_to_dict_schema(self):
        """Dict serialization contains all required fields and correct schema types."""
        net_dict, summary = process_service_log(self.csv_path, noise_threshold=0.0)

        required_net_keys = {
            "service",
            "noise_threshold",
            "variant_retention",
            "case_count",
            "event_count",
            "variant_count",
            "places",
            "transitions",
            "arcs",
            "initial_marking",
            "final_marking",
        }
        self.assertTrue(required_net_keys.issubset(set(net_dict.keys())))
        self.assertEqual(net_dict["service"], "media-service")
        self.assertEqual(net_dict["noise_threshold"], 0.0)
        self.assertEqual(net_dict["variant_retention"], "100%")
        self.assertIsInstance(net_dict["places"], list)
        self.assertIsInstance(net_dict["transitions"], list)
        self.assertIsInstance(net_dict["arcs"], list)
        self.assertIsInstance(net_dict["initial_marking"], list)
        self.assertIsInstance(net_dict["final_marking"], list)

        for t in net_dict["transitions"]:
            self.assertIn("id", t)
            self.assertIn("label", t)
            self.assertIn("is_silent", t)

        for arc in net_dict["arcs"]:
            self.assertEqual(len(arc), 2)

    def test_pnml_export(self):
        """Exporting to PNML creates valid XML with places, transitions, and arcs."""
        pnml_dir = os.path.join(self.temp_dir.name, "pnml")
        net_dict, summary = process_service_log(
            self.csv_path,
            noise_threshold=0.0,
            pnml_dir=pnml_dir,
        )
        pnml_file = os.path.join(pnml_dir, "media-service.pnml")
        self.assertTrue(os.path.exists(pnml_file))

        with open(pnml_file, "r", encoding="utf-8") as f:
            content = f.read()
        self.assertIn("<pnml>", content)
        self.assertIn("<place", content)
        self.assertIn("<transition", content)
        self.assertIn("<arc", content)

    def test_diagram_export(self):
        """Exporting diagrams creates DOT representation."""
        diagram_dir = os.path.join(self.temp_dir.name, "diagrams")
        net_dict, summary = process_service_log(
            self.csv_path,
            noise_threshold=0.0,
            diagram_dir=diagram_dir,
        )
        dot_file = os.path.join(diagram_dir, "media-service.dot")
        self.assertTrue(os.path.exists(dot_file))

        with open(dot_file, "r", encoding="utf-8") as f:
            content = f.read()
        self.assertIn("digraph", content)


class TestBatchProcessingAndCLI(unittest.TestCase):
    """Test suite validating batch discovery and CLI command line execution."""

    def setUp(self):
        self.temp_dir = tempfile.TemporaryDirectory()

    def tearDown(self):
        self.temp_dir.cleanup()

    def test_process_all_logs_deterministic(self):
        """Batch processing runs deterministically over directory of CSV logs."""
        logs_dir = str(REPO_ROOT / "data" / "logs")
        all_nets, all_summaries = process_all_logs(logs_dir, noise_threshold=0.0)

        self.assertGreaterEqual(len(all_nets), 12)
        self.assertGreaterEqual(len(all_summaries), 12)
        self.assertEqual(sorted(all_nets.keys()), list(all_nets.keys()))

    def test_cli_batch_run_produces_output_files(self):
        """CLI batch execution writes mined-nets.json and mining.summary.json."""
        out_nets = os.path.join(self.temp_dir.name, "mined-nets.json")
        out_summary = os.path.join(self.temp_dir.name, "mining.summary.json")
        pnml_dir = os.path.join(self.temp_dir.name, "pnml")

        cmd = [
            sys.executable,
            str(REPO_ROOT / "src" / "miner.py"),
            "--logs-dir",
            str(REPO_ROOT / "data" / "logs"),
            "--output",
            out_nets,
            "--summary-file",
            out_summary,
            "--pnml-dir",
            pnml_dir,
            "--noise-threshold",
            "0.0",
        ]
        proc = subprocess.run(cmd, capture_output=True, text=True)
        self.assertEqual(proc.returncode, 0, msg=f"CLI failed: {proc.stderr}")
        self.assertTrue(os.path.exists(out_nets))
        self.assertTrue(os.path.exists(out_summary))

        with open(out_nets, "r", encoding="utf-8") as f:
            data = json.load(f)
            self.assertIn("compose-post-service", data)
            self.assertIn("post-storage-service", data)

        with open(out_summary, "r", encoding="utf-8") as f:
            summary = json.load(f)
            self.assertIn("compose-post-service", summary)
            self.assertEqual(summary["compose-post-service"]["all_variants_retained"], True)


class TestInferArtifactTag(unittest.TestCase):
    """Test suite validating tag extraction priority for mixed, partial, and drift datasets."""

    def test_infer_artifact_tag_mixed(self):
        from src.miner import infer_artifact_tag
        self.assertEqual(infer_artifact_tag("logs_mixed_drift_10_partial_5"), "mixed_drift_10_partial_5")
        self.assertEqual(infer_artifact_tag("logs_mixed_drift_2_5_partial_7_5/compose-post-service.csv"), "mixed_drift_2_5_partial_7_5")

    def test_infer_artifact_tag_partial(self):
        from src.miner import infer_artifact_tag
        self.assertEqual(infer_artifact_tag("logs_partial_10"), "partial_10")
        self.assertEqual(infer_artifact_tag("logs_partial_2_5/compose-post-service.csv"), "partial_2_5")

    def test_infer_artifact_tag_drift(self):
        from src.miner import infer_artifact_tag
        self.assertEqual(infer_artifact_tag("logs_drift_15"), "drift_15")
        self.assertEqual(infer_artifact_tag("logs_drift_7_5/compose-post-service.csv"), "drift_7_5")


if __name__ == "__main__":
    unittest.main()

