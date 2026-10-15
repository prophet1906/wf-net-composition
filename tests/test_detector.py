#!/usr/bin/env python3
"""
Unit and Integration Tests for Observer Instrumentation & LoLA Model Checking Detector (src/detector.py).

Verifies:
  - Dynamic observer place injection and unconsumed arc invariant.
  - LoLA low-level net specification and CTL formula generation.
  - State-space / coverability reachability verification (UNSAT vs SAT).
  - Alpha-morphism conformance classification.
  - Programmatic negative control bypass generation (UNSAT -> SAT flip).
  - CLI batch detection and summary report serialization.
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

from src.detector import (
    AlphaMorphismStatus,
    PetriNetModel,
    Verdict,
    formulate_ctl_reachability_formula,
    inject_negative_control_bypass,
    instrument_observer_place,
    resolve_candidate_mandatory_sends,
    run_batch_detection,
    sanitize_lola_identifier,
    serialize_to_lola,
    solve_reachability_internal,
    verify_target_transition,
)


class TestObserverInstrumentation(unittest.TestCase):
    """Test suite validating dynamic observer place injection."""

    def setUp(self):
        # Create a simple sequential net: source -> t1 -> p1 -> t2 -> sink
        self.net = PetriNetModel(
            name="seq-net",
            places=["source", "p1", "sink"],
            transitions=[
                {"id": "t1", "label": "send_request_client", "is_silent": False},
                {"id": "t2", "label": "recv_response_client", "is_silent": False},
            ],
            arcs=[
                ("source", "t1"),
                ("t1", "p1"),
                ("p1", "t2"),
                ("t2", "sink"),
            ],
            initial_marking=["source"],
            final_marking=["sink"],
        )

    def test_instrument_observer_by_label(self):
        """Observer injection by transition label adds place obs and arc t -> obs."""
        inst_net, target_ids, obs_place = instrument_observer_place(self.net, "send_request_client")
        self.assertEqual(target_ids, ["t1"])
        self.assertIn(obs_place, inst_net.places)
        self.assertIn(("t1", obs_place), inst_net.arcs)
        # Verify observer place has no outgoing arcs
        self.assertEqual(len(inst_net.get_postset(obs_place)), 0)
        # Original net should remain untouched
        self.assertNotIn("obs", self.net.places)

    def test_instrument_observer_by_id(self):
        """Observer injection by exact transition ID works as expected."""
        inst_net, target_ids, obs_place = instrument_observer_place(self.net, "t2")
        self.assertEqual(target_ids, ["t2"])
        self.assertIn(obs_place, inst_net.places)
        self.assertIn(("t2", obs_place), inst_net.arcs)

    def test_instrument_invalid_target_raises_value_error(self):
        """Attempting to instrument a non-existent transition raises ValueError."""
        with self.assertRaises(ValueError) as ctx:
            instrument_observer_place(self.net, "non_existent_call")
        self.assertIn("not found in Petri net", str(ctx.exception))


class TestLoLASerialization(unittest.TestCase):
    """Test suite validating LoLA grammar serialization and identifier sanitization."""

    def test_sanitize_lola_identifier(self):
        """Sanitizer replaces invalid characters, prevents collisions and reserved keywords."""
        used = set()
        self.assertEqual(sanitize_lola_identifier("user-service::ComposeCreator", used), "user_service__ComposeCreator")
        self.assertEqual(sanitize_lola_identifier("123place", used), "p_123place")
        self.assertEqual(sanitize_lola_identifier("PLACE", used), "node_PLACE")
        # Ensure duplicates get unique numerical suffixes
        tok1 = sanitize_lola_identifier("same_name", used)
        tok2 = sanitize_lola_identifier("same_name", used)
        self.assertNotEqual(tok1, tok2)

    def test_serialize_to_lola_format(self):
        """Serializer outputs valid LoLA structure with places, markings, and transitions."""
        net = PetriNetModel(
            name="test_lola_net",
            places=["source", "p_1", "sink", "obs"],
            transitions=[
                {"id": "t_send", "label": "send_msg", "is_silent": False},
            ],
            arcs=[
                ("source", "t_send"),
                ("t_send", "p_1"),
                ("t_send", "obs"),
            ],
            initial_marking=["source"],
            final_marking=["sink"],
        )
        formula = formulate_ctl_reachability_formula("sink", "obs")
        lola_str, n2l, l2n = serialize_to_lola(net, formula=formula)

        self.assertIn("PLACE SAFE:", lola_str)
        self.assertIn("MARKING", lola_str)
        self.assertIn("TRANSITION", lola_str)
        self.assertIn("CONSUME", lola_str)
        self.assertIn("PRODUCE", lola_str)
        self.assertIn("FORMULA EF (sink > 0 AND obs = 0);", lola_str)

    def test_ctl_formula_formulation(self):
        """Formula generator outputs standard EF(sink > 0 AND obs = 0)."""
        formula = formulate_ctl_reachability_formula("p_sink", "p_obs")
        self.assertEqual(formula, "EF (p_sink > 0 AND p_obs = 0)")


class TestModelCheckingReachability(unittest.TestCase):
    """Test suite validating reachability analysis, UNSAT/SAT classification, and witness extraction."""

    def test_unskippable_sequential_net_yields_unsat(self):
        """A linear workflow where target transition must fire evaluates to UNSAT (Alpha-morphism holds)."""
        net = PetriNetModel(
            name="strict-seq",
            places=["source", "p1", "sink"],
            transitions=[
                {"id": "t1", "label": "mandatory_client", "is_silent": False},
                {"id": "t2", "label": "finalize_server", "is_silent": False},
            ],
            arcs=[
                ("source", "t1"),
                ("t1", "p1"),
                ("p1", "t2"),
                ("t2", "sink"),
            ],
            initial_marking=["source"],
            final_marking=["sink"],
        )
        res = verify_target_transition(net, "mandatory_client", engine="internal")
        self.assertEqual(res["verdict"], Verdict.UNSAT.value)
        self.assertEqual(res["alpha_morphism"], AlphaMorphismStatus.HOLDS.value)
        self.assertIsNone(res.get("witness_trace"))

    def test_skippable_branch_net_yields_sat(self):
        """A workflow with a silent branch bypassing target transition evaluates to SAT (False tau-skip)."""
        net = PetriNetModel(
            name="branch-net",
            places=["source", "p1", "sink"],
            transitions=[
                {"id": "t1", "label": "mandatory_client", "is_silent": False},
                {"id": "t_tau_skip", "label": None, "is_silent": True},  # Spurious bypass
                {"id": "t2", "label": "finalize", "is_silent": False},
            ],
            arcs=[
                ("source", "t1"),
                ("t1", "p1"),
                ("source", "t_tau_skip"),
                ("t_tau_skip", "p1"),
                ("p1", "t2"),
                ("t2", "sink"),
            ],
            initial_marking=["source"],
            final_marking=["sink"],
        )
        res = verify_target_transition(net, "mandatory_client", engine="internal")
        self.assertEqual(res["verdict"], Verdict.SAT.value)
        self.assertEqual(res["alpha_morphism"], AlphaMorphismStatus.VIOLATED.value)
        self.assertIsNotNone(res.get("witness_trace"))
        # Verify witness trace contains the tau skip transition
        witness_t_ids = [step["transition_id"] for step in res["witness_trace"]]
        self.assertIn("t_tau_skip", witness_t_ids)
        self.assertNotIn("t1", witness_t_ids)

    def test_concurrent_fork_join_net_yields_unsat(self):
        """In a concurrent fork-join workflow, all parallel branches must fire to reach sink -> UNSAT."""
        net = PetriNetModel(
            name="fork-join",
            places=["source", "p_fork1", "p_fork2", "p_join1", "p_join2", "sink"],
            transitions=[
                {"id": "t_fork", "label": "fork", "is_silent": True},
                {"id": "t_branch1", "label": "mandatory_send_1", "is_silent": False},
                {"id": "t_branch2", "label": "mandatory_send_2", "is_silent": False},
                {"id": "t_join", "label": "join", "is_silent": True},
            ],
            arcs=[
                ("source", "t_fork"),
                ("t_fork", "p_fork1"),
                ("t_fork", "p_fork2"),
                ("p_fork1", "t_branch1"),
                ("t_branch1", "p_join1"),
                ("p_fork2", "t_branch2"),
                ("t_branch2", "p_join2"),
                ("p_join1", "t_join"),
                ("p_join2", "t_join"),
                ("t_join", "sink"),
            ],
            initial_marking=["source"],
            final_marking=["sink"],
        )
        # Check branch 1
        res1 = verify_target_transition(net, "mandatory_send_1", engine="internal")
        self.assertEqual(res1["verdict"], Verdict.UNSAT.value)
        self.assertEqual(res1["alpha_morphism"], AlphaMorphismStatus.HOLDS.value)

        # Check branch 2
        res2 = verify_target_transition(net, "mandatory_send_2", engine="internal")
        self.assertEqual(res2["verdict"], Verdict.UNSAT.value)
        self.assertEqual(res2["alpha_morphism"], AlphaMorphismStatus.HOLDS.value)


class TestNegativeControlSelfCheck(unittest.TestCase):
    """Test suite validating negative control artificial bypass injection."""

    def test_negative_control_flips_unsat_to_sat(self):
        """Injecting an artificial bypass into an UNSAT net flips verification to SAT."""
        net = PetriNetModel(
            name="strict-net",
            places=["source", "p1", "sink"],
            transitions=[
                {"id": "t1", "label": "critical_rpc_client", "is_silent": False},
                {"id": "t2", "label": "done", "is_silent": False},
            ],
            arcs=[
                ("source", "t1"),
                ("t1", "p1"),
                ("p1", "t2"),
                ("t2", "sink"),
            ],
            initial_marking=["source"],
            final_marking=["sink"],
        )

        # Baseline verification: UNSAT
        base_res = verify_target_transition(net, "critical_rpc_client", engine="internal")
        self.assertEqual(base_res["verdict"], Verdict.UNSAT.value)

        # Inject negative control bypass
        bypassed_net, bypass_id = inject_negative_control_bypass(net, "critical_rpc_client")
        self.assertIn(bypass_id, [t["id"] for t in bypassed_net.transitions])

        # Verification on bypassed net must flip to SAT
        bypassed_res = verify_target_transition(bypassed_net, "critical_rpc_client", engine="internal")
        self.assertEqual(bypassed_res["verdict"], Verdict.SAT.value)
        self.assertEqual(bypassed_res["alpha_morphism"], AlphaMorphismStatus.VIOLATED.value)


class TestCandidateResolverAndBatchDetection(unittest.TestCase):
    """Test suite validating candidate resolution and batch report generation."""

    def test_resolve_candidate_mandatory_sends(self):
        """Candidate resolver identifies all client spans in a mined net."""
        net = PetriNetModel(
            name="compose-post-service",
            places=["source", "sink"],
            transitions=[
                {"id": "t1", "label": "compose_post_server", "is_silent": False},
                {"id": "t2", "label": "compose_text_client", "is_silent": False},
                {"id": "t3", "label": "compose_media_client", "is_silent": False},
            ],
            arcs=[("source", "t1"), ("t1", "sink")],
            initial_marking=["source"],
            final_marking=["sink"],
        )
        candidates = resolve_candidate_mandatory_sends("compose-post-service", net)
        labels = [c["label"] for c in candidates]
        self.assertIn("compose_text_client", labels)
        self.assertIn("compose_media_client", labels)
        self.assertNotIn("compose_post_server", labels)

    def test_batch_detection_on_repository_mined_nets(self):
        """Batch detection on interfaces/mined-nets.json executes cleanly and passes negative controls."""
        mined_nets_path = str(REPO_ROOT / "interfaces" / "mined-nets.json")
        if not os.path.exists(mined_nets_path):
            self.skipTest("interfaces/mined-nets.json not found")

        with tempfile.TemporaryDirectory() as tmp_dir:
            lola_dir = os.path.join(tmp_dir, "lola")
            report = run_batch_detection(
                mined_nets_path=mined_nets_path,
                engine="internal",
                run_negative_control=True,
                export_lola_dir=lola_dir,
            )

            self.assertIn("summary", report)
            self.assertGreater(report["summary"]["total_checks"], 0)
            self.assertEqual(report["summary"]["errors"], 0)
            self.assertTrue(report["negative_control_self_check"]["all_passed"])
            # Ensure LoLA files were exported
            self.assertTrue(os.path.exists(lola_dir))
            self.assertGreater(len(os.listdir(lola_dir)), 0)


class TestCLIExecution(unittest.TestCase):
    """Test suite validating CLI execution and argument parsing."""

    def test_cli_execution_with_output_flags(self):
        """Running detector CLI produces output and summary files."""
        with tempfile.TemporaryDirectory() as tmp_dir:
            out_file = os.path.join(tmp_dir, "report.json")
            sum_file = os.path.join(tmp_dir, "summary.json")
            lola_dir = os.path.join(tmp_dir, "lola")

            cmd = [
                sys.executable,
                str(REPO_ROOT / "src" / "detector.py"),
                "--engine",
                "internal",
                "--output",
                out_file,
                "--summary-file",
                sum_file,
                "--export-lola-dir",
                lola_dir,
            ]
            proc = subprocess.run(cmd, capture_output=True, text=True)
            self.assertEqual(proc.returncode, 0, msg=proc.stderr)
            self.assertTrue(os.path.exists(out_file))
            self.assertTrue(os.path.exists(sum_file))

            with open(sum_file, "r", encoding="utf-8") as f:
                sum_data = json.load(f)
            self.assertIn("summary", sum_data)
            self.assertGreater(sum_data["summary"]["total_checks"], 0)


if __name__ == "__main__":
    unittest.main()
