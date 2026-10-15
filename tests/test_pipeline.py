#!/usr/bin/env python3
"""
Unit and Integration Tests for Unified End-to-End Fault Injection, Repair & Verification Pipeline.

Verifies:
  - Environment pre-flight check and diagnostic reporting
  - Parametric benchmark generation, step calculations, and caching logic
  - LoLA model file export and custom CLI template generation
  - 4-phase single directory execution (Pre-Repair -> Repair -> Post-Repair -> Transition Certificates)
  - SAT -> UNSAT and DEADLOCK -> VERIFIED transition certificate guarantees
  - Multi-benchmark batch evaluation harness and JSON/CSV reporting
  - Fast demo mode execution (< 60s)
  - CLI argument parsing and top-level pipeline execution
"""

import csv
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

# Add repository root to path
REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.pipeline import (
    build_parser,
    calculate_step_values,
    check_environment,
    discover_benchmark_suites,
    execute_demo,
    execute_pipeline_batch,
    execute_pipeline_single,
    export_observer_lola_models,
    export_service_lola_models,
    generate_custom_checking_templates,
    generate_parametric_benchmarks,
    get_defect_category,
    infer_artifact_tag,
    is_cache_valid,
    main,
    print_environment_report,
)


class TestPipelineEnvironment(unittest.TestCase):
    """Test environment pre-flight diagnostics."""

    def test_check_environment(self):
        env = check_environment()
        self.assertIn("python", env)
        self.assertIn("pm4py", env)
        self.assertIn("lola", env)
        self.assertIn("graphviz", env)
        self.assertIn("all_critical_ok", env)

        self.assertEqual(env["python"]["status"], "OK")
        self.assertEqual(env["pm4py"]["status"], "OK")
        self.assertTrue(env["all_critical_ok"])

    def test_print_environment_report(self):
        env = check_environment()
        # Ensure print_environment_report runs without error
        try:
            print_environment_report(env)
        except Exception as e:
            self.fail(f"print_environment_report raised unexpected exception: {e}")


class TestParametricGenerationAndCaching(unittest.TestCase):
    """Test parametric defect generator, fractional steps, and cache skipping."""

    def test_calculate_step_values(self):
        steps = calculate_step_values(0.0, 20.0, 2.5)
        expected = [0.0, 2.5, 5.0, 7.5, 10.0, 12.5, 15.0, 17.5, 20.0]
        self.assertEqual(len(steps), len(expected))
        for s, exp in zip(steps, expected):
            self.assertAlmostEqual(s, exp, places=4)

        steps_5 = calculate_step_values(0.0, 10.0, 5.0)
        self.assertEqual(steps_5, [0.0, 5.0, 10.0])

        with self.assertRaises(ValueError):
            calculate_step_values(0.0, 10.0, -1.0)
        with self.assertRaises(ValueError):
            calculate_step_values(20.0, 10.0, 2.5)

    def test_infer_artifact_tag_and_category(self):
        self.assertEqual(infer_artifact_tag("data/benchmarks/drift/logs_drift_10"), "drift_10")
        self.assertEqual(infer_artifact_tag("data/benchmarks/partial/logs_partial_7_5"), "partial_7_5")
        self.assertEqual(infer_artifact_tag("data/benchmarks/mixed/logs_mixed_drift_10_partial_5"), "mixed_drift_10_partial_5")
        self.assertEqual(infer_artifact_tag("data/logs"), "baseline")

        self.assertEqual(get_defect_category("drift_10"), "drift")
        self.assertEqual(get_defect_category("partial_5"), "partial")
        self.assertEqual(get_defect_category("mixed_drift_10_partial_5"), "mixed")
        self.assertEqual(get_defect_category("baseline"), "baseline")

    def test_is_cache_valid(self):
        with tempfile.TemporaryDirectory() as tmp_dir:
            self.assertFalse(is_cache_valid(tmp_dir, expected_csv_count=1))
            
            # Create empty CSV
            f1 = os.path.join(tmp_dir, "svc1.csv")
            Path(f1).touch()
            self.assertFalse(is_cache_valid(tmp_dir, expected_csv_count=1))

            # Populate CSV with content
            with open(f1, "w") as f:
                f.write("case_id,activity,timestamp\n1,act,100\n")
            self.assertTrue(is_cache_valid(tmp_dir, expected_csv_count=1))

    def test_parametric_generation_with_caching(self):
        with tempfile.TemporaryDirectory() as tmp_out:
            # Generate small range drift
            suites = generate_parametric_benchmarks(
                base_logs_dir="data/logs",
                defect_type="drift",
                range_min=5.0,
                range_max=10.0,
                step=5.0,
                skip_existing=True,
                force_generate=False,
                output_base_dir=tmp_out,
            )
            self.assertEqual(len(suites), 2)
            self.assertFalse(suites[0]["cached"])

            # Run again -> should hit cache
            suites_cached = generate_parametric_benchmarks(
                base_logs_dir="data/logs",
                defect_type="drift",
                range_min=5.0,
                range_max=10.0,
                step=5.0,
                skip_existing=True,
                force_generate=False,
                output_base_dir=tmp_out,
            )
            self.assertEqual(len(suites_cached), 2)
            self.assertTrue(suites_cached[0]["cached"])
            self.assertTrue(suites_cached[1]["cached"])

            # Force generate -> should not be cached
            suites_forced = generate_parametric_benchmarks(
                base_logs_dir="data/logs",
                defect_type="drift",
                range_min=5.0,
                range_max=10.0,
                step=5.0,
                skip_existing=True,
                force_generate=True,
                output_base_dir=tmp_out,
            )
            self.assertFalse(suites_forced[0]["cached"])


class TestLoLAModelPersistenceAndTemplates(unittest.TestCase):
    """Test LoLA model persistence and command template generation."""

    @classmethod
    def setUpClass(cls):
        with open("interfaces/mined-nets.json", "r", encoding="utf-8") as f:
            cls.mined_data = json.load(f)

    def test_export_service_lola_models(self):
        with tempfile.TemporaryDirectory() as tmp_dir:
            paths = export_service_lola_models(self.mined_data, tmp_dir)
            self.assertIn("compose-post-service", paths)
            self.assertTrue(os.path.exists(paths["compose-post-service"]))
            with open(paths["compose-post-service"], "r") as f:
                content = f.read()
                self.assertIn("PLACE SAFE:", content)
                self.assertIn("TRANSITION", content)

    def test_export_observer_lola_models(self):
        with tempfile.TemporaryDirectory() as tmp_dir:
            paths = export_observer_lola_models(self.mined_data, tmp_dir)
            self.assertIn("compose-post-service", paths)
            svc_targets = paths["compose-post-service"]
            self.assertIn("compose_text_client", svc_targets)
            obs_file = svc_targets["compose_text_client"]
            self.assertTrue(os.path.exists(obs_file))
            with open(obs_file, "r") as f:
                content = f.read()
                self.assertIn("EF (", content)
                self.assertIn("obs", content)

    def test_generate_custom_checking_templates(self):
        templates = generate_custom_checking_templates(
            composed_lola_path="data/composed/post_repair_drift_10/lola/composed-net.lola",
            observer_lola_sample="data/lola/observers/post_drift_10/compose-post-service_obs.lola",
            service_lola_sample="data/lola/services/post_drift_10/compose-post-service.lola",
        )
        self.assertGreaterEqual(len(templates), 4)
        categories = [t["category"] for t in templates]
        self.assertIn("P0 Soundness / Deadlock Freedom", categories)
        self.assertIn("Channel 1-Boundedness", categories)
        self.assertIn("Orphaned Message Freedom", categories)
        self.assertIn("Deductive False Tau-Skip Detection", categories)


class TestPipelineExecution(unittest.TestCase):
    """Test single execution, transitions, batch harness, demo, and CLI."""

    def test_execute_pipeline_single_on_drift_10(self):
        with tempfile.TemporaryDirectory() as tmp_out:
            result = execute_pipeline_single(
                logs_dir="data/benchmarks/drift/logs_drift_10",
                output_base=tmp_out,
                engine="internal",
            )
            self.assertIn("_meta", result)
            self.assertIn("phase1_pre_repair", result)
            self.assertIn("phase2_formal_repair", result)
            self.assertIn("phase3_post_repair", result)
            self.assertIn("formal_transitions", result)
            self.assertIn("lola_model_catalog", result)

            # Phase 1: Pre-repair defect demonstration
            p1 = result["phase1_pre_repair"]
            self.assertGreater(p1["sat_violations"], 0)
            self.assertIn("VIOLATED", p1["composition_verdict"])

            # Phase 2: Relabeling
            p2 = result["phase2_formal_repair"]
            self.assertGreater(p2["relabeled_drift_spans"], 0)
            self.assertEqual(p2["retention_ratio"], 1.0)

            # Phase 3: Post-repair verification
            p3 = result["phase3_post_repair"]
            self.assertIn("VERIFIED", p3["composition_verdict"])

            # Transitions
            trans = result["formal_transitions"]
            self.assertGreater(trans["sat_to_unsat_transitions_count"], 0)
            self.assertTrue(trans["core_mandatory_sends_unsat_certified"])
            self.assertTrue(trans["post_repair_composition_sound"])

    def test_discover_benchmark_suites(self):
        suites = discover_benchmark_suites("drift")
        self.assertGreater(len(suites), 0)
        self.assertTrue(all("drift" in s for s in suites))

    def test_execute_demo(self):
        with tempfile.TemporaryDirectory() as tmp_dir:
            report_file = os.path.join(tmp_dir, "demo_report.json")
            demo_res = execute_demo(
                base_logs_dir="data/logs",
                engine="internal",
                report_file=report_file,
            )
            self.assertIn("demo_results", demo_res)
            self.assertEqual(len(demo_res["demo_results"]), 2)
            self.assertTrue(os.path.exists(report_file))

    def test_execute_pipeline_batch(self):
        with tempfile.TemporaryDirectory() as tmp_dir:
            report_file = os.path.join(tmp_dir, "report.json")
            csv_file = os.path.join(tmp_dir, "summary.csv")

            batch_res = execute_pipeline_batch(
                benchmark_type="baseline",
                base_logs_dir="data/logs",
                engine="internal",
                report_file=report_file,
                csv_file=csv_file,
            )
            self.assertIn("aggregate_metrics", batch_res)
            self.assertIn("suites", batch_res)
            self.assertTrue(os.path.exists(report_file))
            self.assertTrue(os.path.exists(csv_file))

            # Verify CSV contents
            with open(csv_file, "r") as f:
                reader = csv.reader(f)
                header = next(reader)
                self.assertIn("tag", header)
                self.assertIn("composition_sound", header)
                rows = list(reader)
                self.assertGreater(len(rows), 0)

    def test_cli_parsing(self):
        parser = build_parser()
        args = parser.parse_args(["--demo"])
        self.assertTrue(args.demo)

        args = parser.parse_args(["--check-env"])
        self.assertTrue(args.check_env)

        args = parser.parse_args(["--range", "0", "20", "--step", "2.5", "--defect-type", "drift"])
        self.assertEqual(args.range, [0.0, 20.0])
        self.assertEqual(args.step, 2.5)
        self.assertEqual(args.defect_type, "drift")

    def test_cli_main_check_env(self):
        ret = main(["--check-env"])
        self.assertEqual(ret, 0)

    def test_pipeline_composed_diagram_generation(self):
        """Verify pipeline execution generates pre-repair and post-repair flat and grouped diagrams."""
        with tempfile.TemporaryDirectory() as tmp_out:
            result = execute_pipeline_single(
                logs_dir="data/benchmarks/drift/logs_drift_10",
                output_base=tmp_out,
                engine="internal",
            )
            tag = result["_meta"]["tag"]
            pre_comp_dir = os.path.join(tmp_out, "composed", f"pre_repair_{tag}")
            post_comp_dir = os.path.join(tmp_out, "composed", f"post_repair_{tag}")

            # Verify Phase 1 diagram artifacts
            self.assertTrue(os.path.exists(os.path.join(pre_comp_dir, "composed-net.dot")))
            self.assertTrue(os.path.exists(os.path.join(pre_comp_dir, "composed-net.svg")))
            self.assertTrue(os.path.exists(os.path.join(pre_comp_dir, "composed-net-grouped.dot")))
            self.assertTrue(os.path.exists(os.path.join(pre_comp_dir, "composed-net-grouped.svg")))

            # Verify Phase 3 diagram artifacts
            self.assertTrue(os.path.exists(os.path.join(post_comp_dir, "composed-net.dot")))
            self.assertTrue(os.path.exists(os.path.join(post_comp_dir, "composed-net.svg")))
            self.assertTrue(os.path.exists(os.path.join(post_comp_dir, "composed-net-grouped.dot")))
            self.assertTrue(os.path.exists(os.path.join(post_comp_dir, "composed-net-grouped.svg")))

            # Verify summary catalog entries
            self.assertIn("diagrams", result["phase1_pre_repair"])
            self.assertIn("diagrams", result["phase3_post_repair"])
            self.assertIn("pre_repair_composed_diagrams", result["lola_model_catalog"])
            self.assertIn("post_repair_composed_diagrams", result["lola_model_catalog"])


if __name__ == "__main__":
    unittest.main()
