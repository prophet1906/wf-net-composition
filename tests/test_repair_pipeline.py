#!/usr/bin/env python3
"""
Integration and End-to-End Tests for Unified Repair & Re-Verification Pipeline (src/repair_pipeline.py).

Verifies:
  - Provenance tag inference and directory discovery across benchmark categories.
  - End-to-end single suite execution (Relabel Pre-Pass -> Drop Repair -> Re-Mining -> Model Checking).
  - Pure drift repair: 100% trace retention, span rescue, and SAT -> UNSAT transition verification.
  - Pure partial loss repair: gap trace purge and unskippable alpha-morphism verification (UNSAT).
  - Compound mixed defect repair: causal chaining of relabeling pre-pass and drop repair.
  - Multi-suite batch execution and aggregate summary reporting.
  - CLI argument handling and exit codes.
"""

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

from src.detector import Verdict
from src.repair_pipeline import (
    discover_benchmark_directories,
    execute_repair_pipeline_single,
    get_defect_category,
    infer_artifact_tag,
    run_batch_repair_pipeline,
)


class TestPipelineTagInferenceAndDiscovery(unittest.TestCase):
    """Test suite validating tag extraction and benchmark directory discovery."""

    def test_infer_artifact_tag_and_category(self):
        """Verify provenance tag extraction and category mapping."""
        self.assertEqual(infer_artifact_tag("data/benchmarks/drift/logs_drift_10"), "drift_10")
        self.assertEqual(get_defect_category("drift_10"), "drift")

        self.assertEqual(infer_artifact_tag("data/benchmarks/partial/logs_partial_7_5"), "partial_7_5")
        self.assertEqual(get_defect_category("partial_7_5"), "partial")

        self.assertEqual(
            infer_artifact_tag("data/benchmarks/mixed/logs_mixed_drift_10_partial_5"),
            "mixed_drift_10_partial_5",
        )
        self.assertEqual(get_defect_category("mixed_drift_10_partial_5"), "mixed")

        self.assertEqual(infer_artifact_tag("data/logs"), "baseline")
        self.assertEqual(get_defect_category("baseline"), "baseline")

    def test_discover_benchmark_directories(self):
        """Verify discovery of existing benchmark directories."""
        all_dirs = discover_benchmark_directories(base_dir="data/benchmarks", suite="all")
        self.assertTrue(len(all_dirs) > 0)
        self.assertTrue(any("drift" in d for d in all_dirs))
        self.assertTrue(any("partial" in d for d in all_dirs))
        self.assertTrue(any("mixed" in d for d in all_dirs))

        drift_dirs = discover_benchmark_directories(base_dir="data/benchmarks", suite="drift")
        self.assertTrue(all("drift" in d for d in drift_dirs))


class TestEndToEndRepairPipeline(unittest.TestCase):
    """Test suite validating end-to-end execution on real benchmark directories."""

    def setUp(self):
        self.temp_dir = tempfile.TemporaryDirectory()

    def tearDown(self):
        self.temp_dir.cleanup()

    def test_end_to_end_pure_drift_repair(self):
        """Verify pure drift benchmark repair (logs_drift_10): 100% retention & SAT -> UNSAT transitions."""
        out_logs = os.path.join(self.temp_dir.name, "repaired_drift_10")
        out_nets = os.path.join(self.temp_dir.name, "mined_drift_10.json")
        out_det = os.path.join(self.temp_dir.name, "detection_drift_10.json")
        out_sum = os.path.join(self.temp_dir.name, "summary_drift_10.json")

        summary = execute_repair_pipeline_single(
            logs_dir="data/benchmarks/drift/logs_drift_10",
            output_dir=out_logs,
            mined_nets_path=out_nets,
            detection_report_path=out_det,
            summary_path=out_sum,
            engine="auto",
        )

        # Invariants & metrics verification
        self.assertEqual(summary["drop_repair_stage"]["retention_ratio"], 1.0)
        self.assertEqual(summary["drop_repair_stage"]["dropped_cases"], 0)
        self.assertGreater(summary["relabel_stage"]["total_relabeled_events"], 0)
        self.assertEqual(summary["mining_stage"]["noise_threshold"], 0.0)

        # Verification certificates
        self.assertTrue(summary["transition_verification"]["core_mandatory_sends_unsat_certified"])
        self.assertGreaterEqual(summary["transition_verification"]["sat_to_unsat_transitions_count"], 7)
        self.assertTrue(summary["invariants_verified"]["zero_synthetic_events"])
        self.assertTrue(summary["invariants_verified"]["sound_gwf_nets"])

        # Check artifact persistence
        self.assertTrue(os.path.exists(out_nets))
        self.assertTrue(os.path.exists(out_det))
        self.assertTrue(os.path.exists(out_sum))

    def test_end_to_end_pure_partial_loss_repair(self):
        """Verify pure partial loss repair (logs_partial_10): gap trace purging & UNSAT certificates."""
        out_logs = os.path.join(self.temp_dir.name, "repaired_partial_10")
        out_nets = os.path.join(self.temp_dir.name, "mined_partial_10.json")
        out_det = os.path.join(self.temp_dir.name, "detection_partial_10.json")
        out_sum = os.path.join(self.temp_dir.name, "summary_partial_10.json")

        summary = execute_repair_pipeline_single(
            logs_dir="data/benchmarks/partial/logs_partial_10",
            output_dir=out_logs,
            mined_nets_path=out_nets,
            detection_report_path=out_det,
            summary_path=out_sum,
            engine="auto",
        )

        self.assertGreater(summary["drop_repair_stage"]["input_cases"], 0)
        self.assertGreater(summary["drop_repair_stage"]["retained_cases"], 0)
        self.assertTrue(summary["transition_verification"]["core_mandatory_sends_unsat_certified"])
        self.assertTrue(summary["invariants_verified"]["formal_alpha_morphism_certified"])

    def test_end_to_end_compound_mixed_defect_repair(self):
        """Verify compound mixed defect repair (logs_mixed_drift_10_partial_5)."""
        mixed_dir = "data/benchmarks/mixed/logs_mixed_drift_10_partial_5"
        if not os.path.isdir(mixed_dir):
            # Find any available mixed dir
            mixed_dirs = discover_benchmark_directories(base_dir="data/benchmarks", suite="mixed")
            if mixed_dirs:
                mixed_dir = mixed_dirs[0]
            else:
                self.skipTest("No mixed benchmark directory found.")

        out_logs = os.path.join(self.temp_dir.name, "repaired_mixed")
        out_nets = os.path.join(self.temp_dir.name, "mined_mixed.json")
        out_det = os.path.join(self.temp_dir.name, "detection_mixed.json")
        out_sum = os.path.join(self.temp_dir.name, "summary_mixed.json")

        summary = execute_repair_pipeline_single(
            logs_dir=mixed_dir,
            output_dir=out_logs,
            mined_nets_path=out_nets,
            detection_report_path=out_det,
            summary_path=out_sum,
            engine="auto",
        )

        self.assertGreater(summary["relabel_stage"]["total_relabeled_events"], 0)
        self.assertTrue(summary["transition_verification"]["core_mandatory_sends_unsat_certified"])


class TestBatchRepairPipeline(unittest.TestCase):
    """Test suite validating multi-directory batch execution."""

    def test_batch_repair_small_subset(self):
        """Verify batch execution over 2 selected benchmark directories."""
        dirs = [
            "data/benchmarks/drift/logs_drift_2_5",
            "data/benchmarks/partial/logs_partial_2_5",
        ]
        existing_dirs = [d for d in dirs if os.path.isdir(d)]
        if len(existing_dirs) < 2:
            self.skipTest("Benchmark directories not present.")

        with tempfile.TemporaryDirectory() as tmp_dir:
            batch_summary_path = os.path.join(tmp_dir, "batch_test.summary.json")
            batch_summary = run_batch_repair_pipeline(
                benchmark_dirs=existing_dirs,
                batch_summary_path=batch_summary_path,
                engine="auto",
            )

            self.assertEqual(batch_summary["_meta"]["total_benchmark_suites"], len(existing_dirs))
            self.assertTrue(batch_summary["aggregate_metrics"]["all_core_mandatory_sends_certified"])
            self.assertTrue(os.path.exists(batch_summary_path))


class TestRepairPipelineCLI(unittest.TestCase):
    """Test suite validating CLI execution."""

    def test_cli_single_logs_dir(self):
        """Verify CLI single directory invocation."""
        with tempfile.TemporaryDirectory() as tmp_out:
            cmd = [
                sys.executable,
                "src/repair_pipeline.py",
                "--logs-dir",
                "data/benchmarks/drift/logs_drift_5",
                "--output-dir",
                tmp_out,
            ]
            res = subprocess.run(cmd, capture_output=True, text=True)
            self.assertEqual(res.returncode, 0, f"CLI failed: {res.stderr}")
            self.assertIn("Pipeline Summary for drift_5", res.stdout)
            self.assertTrue(os.path.exists(os.path.join(tmp_out, "repair_drift_5.summary.json")))


if __name__ == "__main__":
    unittest.main()
