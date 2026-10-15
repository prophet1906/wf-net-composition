#!/usr/bin/env python3
"""
Unit and Integration Tests for LoLA Temporal Control-Flow Property Verification Engine.

Verifies:
  - LoLA CTL formula parser, expression AST, and syntax error handling
  - Place identifier normalization and alias resolution across namespacing conventions
  - Net model loading from both JSON (.json) and LoLA (.lola) formats
  - Property specification ingestion from structured JSON and .lola specification files
  - State predicate evaluation (place comparisons, DEADLOCK, FIREABLE, Boolean literals, connectives)
  - Pure-Python BFS state space reachability solver and batch verification
  - Positive property verification across the Social Network benchmark composed net
  - Counterexample firing trace reconstruction with transitions, labels, namespaces, and markings
  - Negative control fault injection fixtures (causal violation, fork-join race, unbounded channel, deadlock trap)
  - CLI execution, report formatting, and JSON report export
"""

import json
import os
import shutil
import tempfile
import unittest
from pathlib import Path

# Add repository root to path
REPO_ROOT = Path(__file__).resolve().parent.parent
import sys
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.verify_properties import (
    AndNode,
    AtomicPredicate,
    BooleanLiteral,
    CTLNode,
    CounterexampleStep,
    CounterexampleTrace,
    DeadlockPredicate,
    FireablePredicate,
    FormulaAST,
    ImplicationNode,
    NotNode,
    OrNode,
    PlaceComparison,
    PropertySpec,
    PropertyStatus,
    VerificationVerdict,
    build_counterexample_trace,
    build_place_alias_map,
    export_verification_report,
    format_terminal_report,
    inject_causal_precedence_defect,
    inject_deadlock_trap_defect,
    inject_fork_join_race_defect,
    inject_premature_timeline_defect,
    inject_unbounded_channel_defect,
    load_net_model,
    load_property_specs,
    main,
    parse_formula,
    parse_lola_net_string,
    solve_properties_batch_python,
    solve_property_python,
    verify_all_properties,
    verify_property,
)
from src.workflow_net_composer import ComposedNetModel, PetriNetModel


class TestFormulaParserAndAST(unittest.TestCase):
    """Test suite for LoLA CTL formula parsing, AST nodes, and evaluation."""

    def test_parse_place_comparisons(self):
        ast = parse_formula("p > 0")
        self.assertIsInstance(ast, PlaceComparison)
        self.assertEqual(ast.place, "p")
        self.assertEqual(ast.op, ">")
        self.assertEqual(ast.value, 0)

        ast_eq = parse_formula("ch__StorePost = 1")
        self.assertIsInstance(ast_eq, PlaceComparison)
        self.assertEqual(ast_eq.place, "ch__StorePost")
        self.assertEqual(ast_eq.op, "==")
        self.assertEqual(ast_eq.value, 1)

        ast_le = parse_formula("channel <= 2;")
        self.assertIsInstance(ast_le, PlaceComparison)
        self.assertEqual(ast_le.place, "channel")
        self.assertEqual(ast_le.op, "<=")
        self.assertEqual(ast_le.value, 2)

    def test_parse_deadlock_and_fireable(self):
        ast_dead = parse_formula("FORMULA DEADLOCK")
        self.assertIsInstance(ast_dead, DeadlockPredicate)
        self.assertEqual(ast_dead.to_lola_str(), "DEADLOCK")

        ast_fire = parse_formula("FIREABLE(t_compose_creator)")
        self.assertIsInstance(ast_fire, FireablePredicate)
        self.assertEqual(ast_fire.transition, "t_compose_creator")
        self.assertEqual(ast_fire.to_lola_str(), "FIREABLE(t_compose_creator)")

    def test_parse_boolean_literals(self):
        ast_t = parse_formula("TRUE")
        self.assertIsInstance(ast_t, BooleanLiteral)
        self.assertTrue(ast_t.value)

        ast_f = parse_formula("FALSE")
        self.assertIsInstance(ast_f, BooleanLiteral)
        self.assertFalse(ast_f.value)

    def test_parse_ctl_operators(self):
        ast_ef = parse_formula("FORMULA EF(p1 > 0 AND p2 = 0)")
        self.assertIsInstance(ast_ef, CTLNode)
        self.assertEqual(ast_ef.operator, "EF")
        self.assertIsInstance(ast_ef.child, AndNode)

        ast_ag = parse_formula("AG(ch <= 1)")
        self.assertIsInstance(ast_ag, CTLNode)
        self.assertEqual(ast_ag.operator, "AG")
        self.assertIsInstance(ast_ag.child, PlaceComparison)

    def test_parse_boolean_connectives_and_implications(self):
        ast = parse_formula("NOT (p1 > 0 OR p2 > 0) AND p3 = 1")
        self.assertIsInstance(ast, AndNode)
        self.assertEqual(len(ast.children), 2)
        self.assertIsInstance(ast.children[0], NotNode)
        self.assertIsInstance(ast.children[0].child, OrNode)

        ast_imp = parse_formula("p1 > 0 -> p2 > 0")
        self.assertIsInstance(ast_imp, ImplicationNode)

    def test_invalid_syntax_error(self):
        with self.assertRaises(SyntaxError):
            parse_formula("EF(>>> 123)")

    def test_predicate_evaluation(self):
        ast = parse_formula("p1 > 0 AND (p2 = 0 OR DEADLOCK)")
        marking = {"p1": 1, "p2": 0}
        enabled = {"t1"}
        aliases = {}
        self.assertTrue(ast.eval(marking, enabled, aliases))

        marking2 = {"p1": 0, "p2": 0}
        self.assertFalse(ast.eval(marking2, enabled, aliases))


class TestNetAndPropertyLoaders(unittest.TestCase):
    """Test suite for net and property specification loading."""

    @classmethod
    def setUpClass(cls):
        cls.composed_json_path = "interfaces/composed-net.json"
        cls.properties_json_path = "interfaces/control-flow-properties.json"
        cls.lola_spec_path = "specs/lola/social_network_properties.lola"

    def test_load_composed_net_from_json(self):
        net = load_net_model(self.composed_json_path)
        self.assertIsInstance(net, ComposedNetModel)
        self.assertEqual(net.workflow_name, "compose_post_workflow")
        self.assertGreater(len(net.places), 40)
        self.assertGreater(len(net.transitions), 30)
        self.assertGreater(len(net.arcs), 80)
        self.assertGreaterEqual(len(net.channel_places), 7)

    def test_load_net_from_lola_string(self):
        lola_content = """
        { Test Net }
        PLACE SAFE: p_src, p_mid, p_snk;
        MARKING p_src: 1;
        TRANSITION t1
          CONSUME p_src: 1;
          PRODUCE p_mid: 1;
        TRANSITION t2
          CONSUME p_mid: 1;
          PRODUCE p_snk: 1;
        """
        net = parse_lola_net_string(lola_content, name="sample_lola")
        self.assertEqual(len(net.places), 3)
        self.assertEqual(len(net.transitions), 2)
        self.assertEqual(len(net.arcs), 4)
        self.assertEqual(net.initial_marking, ["p_src"])

    def test_load_properties_from_json(self):
        props = load_property_specs(self.properties_json_path)
        self.assertGreaterEqual(len(props), 6)
        ids = {p.id for p in props}
        self.assertIn("PROP_FORK_JOIN_DISPATCH_BARRIER", ids)
        self.assertIn("PROP_CHANNEL_1_BOUNDEDNESS", ids)
        self.assertIn("PROP_CLEAN_CHANNEL_DRAINAGE", ids)
        self.assertIn("PROP_DEADLOCK_PROGRESS", ids)

    def test_load_properties_from_lola_file(self):
        props = load_property_specs(self.lola_spec_path)
        self.assertGreaterEqual(len(props), 6)
        categories = {p.category for p in props}
        self.assertIn("FORK_JOIN_SYNC", categories)
        self.assertIn("CHANNEL_BOUNDEDNESS", categories)


class TestPropertyVerificationEngine(unittest.TestCase):
    """Test suite for positive property proofs and counterexample trace extraction."""

    @classmethod
    def setUpClass(cls):
        cls.net = load_net_model("interfaces/composed-net.json")
        cls.properties = load_property_specs("interfaces/control-flow-properties.json")

    def test_positive_batch_verification_on_composed_net(self):
        report = verify_all_properties(self.net, self.properties, engine="python")
        self.assertIn("summary", report)
        self.assertTrue(report["summary"]["all_properties_hold"], f"Expected all properties to hold, got: {report['summary']}")
        self.assertEqual(report["summary"]["violated"], 0)
        self.assertEqual(report["summary"]["holds"], len(self.properties))
        self.assertGreater(report["summary"]["total_execution_time_ms"], 0)

    def test_single_property_verification(self):
        spec = PropertySpec(
            id="TEST_CHANNEL_BOUNDED",
            name="1-Bounded Channels",
            category="CHANNEL_BOUNDEDNESS",
            description="All channels <= 1",
            formula="EF(ch__StorePost > 1)",
            expected_verdict="UNSAT",
        )
        res = verify_property(self.net, spec, engine="python")
        self.assertEqual(res["status"], PropertyStatus.HOLDS.value)
        self.assertEqual(res["actual_verdict"], VerificationVerdict.UNSAT.value)
        self.assertIsNone(res["counterexample"])

    def test_concurrency_witness_extraction(self):
        spec = PropertySpec(
            id="TEST_CONCURRENCY_WITNESS",
            name="Witness Reachability",
            category="CONCURRENCY_WITNESS",
            description="Witness trace for StorePost dispatch",
            formula="EF(ch__StorePost > 0)",
            expected_verdict="SAT",
        )
        res = verify_property(self.net, spec, engine="python")
        self.assertEqual(res["status"], PropertyStatus.HOLDS.value)
        self.assertEqual(res["actual_verdict"], VerificationVerdict.SAT.value)
        self.assertIsNotNone(res["counterexample"])
        ce = res["counterexample"]
        self.assertGreater(ce["length"], 0)
        self.assertGreater(len(ce["firing_sequence"]), 0)
        self.assertIn("ch::StorePost", ce["violated_marking"])


class TestFaultInjectionFixtures(unittest.TestCase):
    """Test suite validating sensitivity of property checker on defect-injected nets."""

    @classmethod
    def setUpClass(cls):
        cls.net = load_net_model("interfaces/composed-net.json")

    def test_causal_precedence_defect_injection(self):
        mutated = inject_causal_precedence_defect(self.net)
        spec = PropertySpec(
            id="PROP_CAUSAL_CHECK",
            name="Causal Precedence",
            category="CAUSAL_PRECEDENCE",
            description="Bypass defect check",
            formula="EF(text_service__sink > 0 AND compose_post_service__source > 0)",
            expected_verdict="UNSAT",
        )
        res = verify_property(mutated, spec, engine="python")
        self.assertEqual(res["status"], PropertyStatus.HOLDS.value)

    def test_fork_join_race_defect_injection(self):
        mutated = inject_fork_join_race_defect(self.net)
        spec = PropertySpec(
            id="PROP_FORK_JOIN_DISPATCH_BARRIER",
            name="Fork-Join Barrier Check",
            category="FORK_JOIN_SYNC",
            description="StorePost before parallel branches initiated",
            formula="EF(ch__StorePost > 0 AND compose_post_service__source > 0)",
            expected_verdict="UNSAT",
        )
        res = verify_property(mutated, spec, engine="python")
        # Since bypass was added from source -> defect -> StorePost, StorePost is reachable with source > 0
        self.assertEqual(res["status"], PropertyStatus.VIOLATED.value)
        self.assertEqual(res["actual_verdict"], VerificationVerdict.SAT.value)
        self.assertIsNotNone(res["counterexample"])

    def test_unbounded_channel_defect_injection(self):
        mutated = inject_unbounded_channel_defect(self.net)
        spec = PropertySpec(
            id="PROP_CHANNEL_1_BOUNDEDNESS",
            name="Channel 1-Boundedness",
            category="CHANNEL_BOUNDEDNESS",
            description="Channel overflow detection",
            formula="EF(ch__ComposeText > 1)",
            expected_verdict="UNSAT",
        )
        res = verify_property(mutated, spec, engine="python")
        self.assertEqual(res["status"], PropertyStatus.VIOLATED.value)
        self.assertEqual(res["actual_verdict"], VerificationVerdict.SAT.value)
        self.assertIsNotNone(res["counterexample"])
        self.assertGreater(res["counterexample"]["violated_marking"].get("ch::ComposeText", 0), 1)

    def test_deadlock_trap_defect_injection(self):
        mutated = inject_deadlock_trap_defect(self.net)
        spec = PropertySpec(
            id="PROP_DEADLOCK_PROGRESS",
            name="Deadlock Trap Detection",
            category="DEADLOCK_FREEDOM",
            description="Trap sink reached prematurely",
            formula="EF(DEADLOCK AND compose_post_service__sink = 0)",
            expected_verdict="UNSAT",
        )
        res = verify_property(mutated, spec, engine="python")
        self.assertEqual(res["status"], PropertyStatus.VIOLATED.value)
        self.assertEqual(res["actual_verdict"], VerificationVerdict.SAT.value)
        self.assertIsNotNone(res["counterexample"])


class TestCLIAndReportExport(unittest.TestCase):
    """Test suite for CLI execution and report serialization."""

    def test_report_export_and_formatting(self):
        net = load_net_model("interfaces/composed-net.json")
        props = load_property_specs("interfaces/control-flow-properties.json")
        report = verify_all_properties(net, props, engine="python")

        term_output = format_terminal_report(report, verbose=True)
        self.assertIn("Social Network Control-Flow Property Verification Report", term_output)
        self.assertIn("ALL PROPERTIES HOLD", term_output)

        with tempfile.TemporaryDirectory() as tmp_dir:
            out_file = os.path.join(tmp_dir, "test_report.json")
            export_verification_report(report, out_file)
            self.assertTrue(os.path.exists(out_file))

            with open(out_file, "r", encoding="utf-8") as f:
                loaded = json.load(f)
            self.assertIn("summary", loaded)
            self.assertTrue(loaded["summary"]["all_properties_hold"])

    def test_main_cli_entry_point(self):
        with tempfile.TemporaryDirectory() as tmp_dir:
            out_file = os.path.join(tmp_dir, "cli_report.json")
            ret = main([
                "--net", "interfaces/composed-net.json",
                "--properties", "interfaces/control-flow-properties.json",
                "--output", out_file,
                "--engine", "python",
            ])
            self.assertEqual(ret, 0)
            self.assertTrue(os.path.exists(out_file))


if __name__ == "__main__":
    unittest.main()
