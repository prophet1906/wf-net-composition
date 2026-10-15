#!/usr/bin/env python3
"""
Unit and Integration Tests for Asynchronous Channel Fusion Workflow Net Composer.

Verifies:
  - Disjoint service namespacing (<svc>::<node>)
  - Direct callee source fusion and caller produce wiring (ch::<ChannelName>)
  - Composed net serialization (JSON, LoLA, PNML)
  - 4-Property formal verification (P0 Soundness, Orphaned Message Freedom, Channel 1-Boundedness, Response-Liveness)
  - Negative control fault injection fixtures (deadlocks, orphaned messages, unbounded channels)
  - CLI execution and report export
"""

import json
import os
import shutil
import tempfile
import unittest

from src.workflow_net_composer import (
    ChannelMetadata,
    ComposedNetModel,
    PetriNetModel,
    PropertyStatus,
    VerificationVerdict,
    compose_workflow_nets,
    export_verification_report,
    extract_topology_dispatches,
    inject_artificial_deadlock,
    inject_stranded_orphaned_message,
    inject_unbounded_channel,
    main,
    namespace_service_net,
    sanitize_lola_identifier,
    serialize_composed_to_json,
    serialize_composed_to_lola,
    serialize_composed_to_pnml,
    generate_composed_dot,
    render_composed_via_graphviz,
    render_composed_standalone_svg,
    render_composed_diagrams,
    solve_reachability_lola,
    solve_state_space_internal,
    verify_channel_1_boundedness,
    verify_composition,
    verify_orphaned_message_freedom,
    verify_p0_soundness,
    verify_response_liveness,
)


class TestWorkflowNetComposer(unittest.TestCase):
    """Test suite for Asynchronous Channel Fusion Composer & 4-Property Verifier."""

    @classmethod
    def setUpClass(cls):
        cls.topo_path = "interfaces/social-network.json"
        cls.mined_path = "interfaces/mined-nets.json"
        with open(cls.topo_path, "r", encoding="utf-8") as f:
            cls.topo_data = json.load(f)
        with open(cls.mined_path, "r", encoding="utf-8") as f:
            cls.mined_data = json.load(f)
        cls.service_nets = {
            k: PetriNetModel.from_dict(v, name=k) for k, v in cls.mined_data.items() if isinstance(v, dict)
        }

    def setUp(self):
        self.tmp_dir = tempfile.mkdtemp(prefix="test_composer_")

    def tearDown(self):
        shutil.rmtree(self.tmp_dir, ignore_errors=True)

    # ------------------------------------------------------------------------
    # 1. Namespacing Tests
    # ------------------------------------------------------------------------

    def test_disjoint_service_namespacing(self):
        """Test namespacing prefixes all places and transitions with `<svc>::`."""
        svc_name = "test-service"
        raw_net = PetriNetModel(
            name=svc_name,
            places=["source", "p_1", "sink"],
            transitions=[
                {"id": "t_1", "label": "op_1", "is_silent": False},
                {"id": "t_2", "label": "op_2", "is_silent": False},
            ],
            arcs=[("source", "t_1"), ("t_1", "p_1"), ("p_1", "t_2"), ("t_2", "sink")],
            initial_marking=["source"],
            final_marking=["sink"],
        )

        ns_net = namespace_service_net(raw_net, svc_name)

        self.assertIn("test-service::source", ns_net.places)
        self.assertIn("test-service::p_1", ns_net.places)
        self.assertIn("test-service::sink", ns_net.places)
        self.assertNotIn("source", ns_net.places)

        trans_ids = [t["id"] for t in ns_net.transitions]
        self.assertIn("test-service::t_1", trans_ids)
        self.assertIn("test-service::t_2", trans_ids)

        expected_arcs = [
            ("test-service::source", "test-service::t_1"),
            ("test-service::t_1", "test-service::p_1"),
            ("test-service::p_1", "test-service::t_2"),
            ("test-service::t_2", "test-service::sink"),
        ]
        self.assertEqual(ns_net.arcs, expected_arcs)
        self.assertEqual(ns_net.initial_marking, ["test-service::source"])
        self.assertEqual(ns_net.final_marking, ["test-service::sink"])

    # ------------------------------------------------------------------------
    # 2. Topology Ingestion & Channel Fusion Tests
    # ------------------------------------------------------------------------

    def test_extract_topology_dispatches(self):
        """Test extracting workflow channels and participating services."""
        wf_name, channels, svcs = extract_topology_dispatches(self.topo_data, "compose_post_workflow")
        self.assertEqual(wf_name, "compose_post_workflow")
        self.assertGreaterEqual(len(channels), 9)
        self.assertIn("compose-post-service", svcs)
        self.assertIn("text-service", svcs)
        self.assertIn("url-shorten-service", svcs)
        self.assertIn("user-mention-service", svcs)

        ch_places = [ch.channel_place for ch in channels]
        self.assertIn("ch::ComposeText", ch_places)
        self.assertIn("ch::ComposeUrls", ch_places)
        self.assertIn("ch::ComposeUserMentions", ch_places)
        self.assertIn("ch::StorePost", ch_places)

    def test_compose_workflow_nets_structure(self):
        """Test direct callee fusion and caller produce wiring on compose_post_workflow."""
        cnet = compose_workflow_nets(self.service_nets, self.topo_data, "compose_post_workflow")

        # Verify participating services
        self.assertEqual(len(cnet.participating_services), 10)
        self.assertIn("compose-post-service", cnet.participating_services)
        self.assertIn("text-service", cnet.participating_services)

        # Verify channel places
        self.assertIn("ch::ComposeText", cnet.channel_places)
        self.assertIn("ch::ComposeUrls", cnet.channel_places)

        # Verify initial marking has only root service source place
        self.assertEqual(cnet.initial_marking, ["compose-post-service::source"])

        # Verify callee source place was replaced by channel place
        self.assertNotIn("text-service::source", cnet.places)
        self.assertNotIn("url-shorten-service::source", cnet.places)

        # Verify caller send produces into channel place
        caller_send_arcs = [tgt for src, tgt in cnet.arcs if tgt == "ch::ComposeText"]
        self.assertGreater(len(caller_send_arcs), 0)

        # Verify callee consumes from channel place
        callee_recv_arcs = [tgt for src, tgt in cnet.arcs if src == "ch::ComposeText"]
        self.assertGreater(len(callee_recv_arcs), 0)

    # ------------------------------------------------------------------------
    # 3. Serialization Tests (JSON, LoLA, PNML)
    # ------------------------------------------------------------------------

    def test_serialization_json(self):
        """Test exporting composed net to JSON format."""
        cnet = compose_workflow_nets(self.service_nets, self.topo_data, "compose_post_workflow")
        out_json = os.path.join(self.tmp_dir, "composed-net.json")
        serialize_composed_to_json(cnet, out_json)

        self.assertTrue(os.path.exists(out_json))
        with open(out_json, "r", encoding="utf-8") as f:
            data = json.load(f)

        self.assertEqual(data["workflow_name"], "compose_post_workflow")
        self.assertEqual(len(data["participating_services"]), 10)
        self.assertIn("places", data)
        self.assertIn("transitions", data)
        self.assertIn("arcs", data)

    def test_serialization_lola(self):
        """Test LoLA specification generation with sanitized identifiers."""
        cnet = compose_workflow_nets(self.service_nets, self.topo_data, "compose_post_workflow")
        out_lola = os.path.join(self.tmp_dir, "composed-net.lola")
        content, n2l, l2n = serialize_composed_to_lola(cnet, output_path=out_lola)

        self.assertTrue(os.path.exists(out_lola))
        self.assertIn("PLACE SAFE:", content)
        self.assertIn("MARKING compose_post_service__source: 1;", content)
        self.assertIn("TRANSITION", content)
        self.assertIn("CONSUME", content)
        self.assertIn("PRODUCE", content)

        # Ensure no invalid double colons exist in LoLA identifier tokens
        for tok in n2l.values():
            self.assertNotIn("::", tok)
            self.assertNotIn("-", tok)

    def test_serialization_pnml(self):
        """Test PNML XML model export."""
        cnet = compose_workflow_nets(self.service_nets, self.topo_data, "compose_post_workflow")
        out_pnml = os.path.join(self.tmp_dir, "composed-net.pnml")
        serialize_composed_to_pnml(cnet, out_pnml)

        self.assertTrue(os.path.exists(out_pnml))
        with open(out_pnml, "r", encoding="utf-8") as f:
            xml_text = f.read()

        self.assertIn("<pnml", xml_text)
        self.assertIn("compose_post_workflow", xml_text)
        self.assertIn("<place", xml_text)
        self.assertIn("<transition", xml_text)
        self.assertIn("<arc", xml_text)

    # ------------------------------------------------------------------------
    # 4. Four Formal Verification Properties
    # ------------------------------------------------------------------------

    def test_sound_composition_4_properties(self):
        """Test that all 4 formal properties hold on sound compose_post_workflow composition."""
        cnet = compose_workflow_nets(self.service_nets, self.topo_data, "compose_post_workflow")
        report = verify_composition(cnet, engine="internal", max_states=300000)

        # 1. P0 Soundness
        p0 = report["properties"]["p0_soundness"]
        self.assertEqual(p0["verdict"], VerificationVerdict.UNSAT.value)
        self.assertEqual(p0["status"], PropertyStatus.HOLDS.value)

        # 2. Orphaned Message Freedom
        orphan = report["properties"]["orphaned_message_freedom"]
        self.assertEqual(orphan["verdict"], VerificationVerdict.UNSAT.value)
        self.assertEqual(orphan["status"], PropertyStatus.HOLDS.value)

        # 3. Channel 1-Boundedness
        bound = report["properties"]["channel_1_boundedness"]
        self.assertEqual(bound["status"], PropertyStatus.HOLDS.value)
        self.assertTrue(bound["all_channels_1_bounded"])
        for ch, depth in bound["max_channel_depth"].items():
            self.assertLessEqual(depth, 1, f"Channel {ch} exceeded 1 token capacity: {depth}")

        # 4. Response-Liveness
        live = report["properties"]["response_liveness"]
        self.assertEqual(live["status"], PropertyStatus.HOLDS.value)
        self.assertTrue(live["all_ip4_channels_live"])

        # Overall summary
        self.assertTrue(report["summary"]["all_properties_hold"])

    # ------------------------------------------------------------------------
    # 5. Negative Control Fault Injection Tests
    # ------------------------------------------------------------------------

    def test_negative_control_deadlock_detection(self):
        """Test that artificial deadlock injection causes P0 soundness violation (SAT)."""
        cnet = compose_workflow_nets(self.service_nets, self.topo_data, "compose_post_workflow")
        faulty_net = inject_artificial_deadlock(cnet)
        report = verify_composition(faulty_net, engine="internal", max_states=100000)

        p0 = report["properties"]["p0_soundness"]
        self.assertEqual(p0["verdict"], VerificationVerdict.SAT.value)
        self.assertEqual(p0["status"], PropertyStatus.VIOLATED.value)
        self.assertIn("witness_trace", p0)
        self.assertFalse(report["summary"]["all_properties_hold"])

    def test_negative_control_orphaned_message_detection(self):
        """Test that stranded orphan message injection causes Orphaned Message Freedom violation."""
        cnet = compose_workflow_nets(self.service_nets, self.topo_data, "compose_post_workflow")
        faulty_net = inject_stranded_orphaned_message(cnet)
        report = verify_composition(faulty_net, engine="internal", max_states=300000)

        orphan = report["properties"]["orphaned_message_freedom"]
        self.assertEqual(orphan["verdict"], VerificationVerdict.SAT.value)
        self.assertEqual(orphan["status"], PropertyStatus.VIOLATED.value)
        self.assertIn("orphaned_channels", orphan)
        self.assertIn("ch::InjectedOrphan", orphan["orphaned_channels"])
        self.assertFalse(report["summary"]["all_properties_hold"])

    def test_negative_control_unbounded_channel_detection(self):
        """Test that unbounded channel token injection causes Channel 1-Boundedness violation."""
        cnet = compose_workflow_nets(self.service_nets, self.topo_data, "compose_post_workflow")
        faulty_net = inject_unbounded_channel(cnet)
        report = verify_composition(faulty_net, engine="internal", max_states=300000)

        bound = report["properties"]["channel_1_boundedness"]
        self.assertEqual(bound["status"], PropertyStatus.VIOLATED.value)
        self.assertFalse(bound["all_channels_1_bounded"])
        self.assertFalse(report["summary"]["all_properties_hold"])

    # ------------------------------------------------------------------------
    # 6. CLI Execution & Report Export
    # ------------------------------------------------------------------------

    def test_cli_execution_and_report_export(self):
        """Test main CLI entrypoint generating all output artifacts."""
        out_json = os.path.join(self.tmp_dir, "composed-net.json")
        out_lola = os.path.join(self.tmp_dir, "composed-net.lola")
        out_pnml = os.path.join(self.tmp_dir, "composed-net.pnml")
        out_report = os.path.join(self.tmp_dir, "composition-verification-report.json")

        cmd_args = [
            "--mined-nets", self.mined_path,
            "--topology", self.topo_path,
            "--workflow", "compose_post_workflow",
            "--output-json", out_json,
            "--output-lola", out_lola,
            "--output-pnml", out_pnml,
            "--output-report", out_report,
            "--engine", "internal",
            "--max-states", "300000",
        ]

        exit_code = main(cmd_args)
        self.assertEqual(exit_code, 0)
        self.assertTrue(os.path.exists(out_json))
        self.assertTrue(os.path.exists(out_lola))
        self.assertTrue(os.path.exists(out_pnml))
        self.assertTrue(os.path.exists(out_report))

        with open(out_report, "r", encoding="utf-8") as f:
            rep = json.load(f)
        self.assertTrue(rep["summary"]["all_properties_hold"])

    # ------------------------------------------------------------------------
    # 7. Composed Net Diagram Rendering Tests (DOT, SVG, PNG)
    # ------------------------------------------------------------------------

    def test_generate_composed_dot_flat(self):
        """Test flat composed net DOT generation with standard Petri net circles and boxes."""
        cnet = compose_workflow_nets(self.service_nets, self.topo_data, "compose_post_workflow")
        dot_str = generate_composed_dot(cnet, group_by_service=False)

        self.assertIn('digraph "compose_post_workflow"', dot_str)
        self.assertIn('rankdir="TB"', dot_str)
        # Verify places are circles
        self.assertIn('shape=circle', dot_str)
        # Verify sink is double circle
        self.assertIn('shape=doublecircle', dot_str)
        # Verify transitions are boxes
        self.assertIn('shape=box', dot_str)
        # Verify channel place exists and is circle
        self.assertIn('"ch::ComposeText" [shape=circle', dot_str)
        # Verify source place has initial token
        self.assertIn('label="●"', dot_str)
        # Verify directed arcs
        self.assertIn('->', dot_str)

    def test_generate_composed_dot_grouped(self):
        """Test service-grouped composed net DOT generation with service cluster subgraphs."""
        cnet = compose_workflow_nets(self.service_nets, self.topo_data, "compose_post_workflow")
        dot_str = generate_composed_dot(cnet, group_by_service=True)

        self.assertIn('digraph "compose_post_workflow"', dot_str)
        # Verify service cluster subgraphs are created
        self.assertIn('subgraph "cluster_compose_post_service"', dot_str)
        self.assertIn('subgraph "cluster_text_service"', dot_str)
        self.assertIn('subgraph "cluster_user_service"', dot_str)
        # Verify inter-service channel places exist at top level
        self.assertIn('"ch::ComposeText" [shape=circle', dot_str)

    def test_render_composed_standalone_svg_flat_and_grouped(self):
        """Test pure-Python fallback SVG rendering for both flat and grouped variations."""
        cnet = compose_workflow_nets(self.service_nets, self.topo_data, "compose_post_workflow")
        flat_svg = os.path.join(self.tmp_dir, "test-flat.svg")
        grouped_svg = os.path.join(self.tmp_dir, "test-grouped.svg")

        # Flat SVG
        res_flat = render_composed_standalone_svg(cnet, flat_svg, group_by_service=False)
        self.assertTrue(res_flat)
        self.assertTrue(os.path.exists(flat_svg))
        with open(flat_svg, "r", encoding="utf-8") as f:
            flat_content = f.read()
        self.assertIn("<svg", flat_content)
        self.assertIn("<circle", flat_content)
        self.assertIn("<rect", flat_content)
        self.assertIn("<line", flat_content)

        # Grouped SVG
        res_grouped = render_composed_standalone_svg(cnet, grouped_svg, group_by_service=True)
        self.assertTrue(res_grouped)
        self.assertTrue(os.path.exists(grouped_svg))
        with open(grouped_svg, "r", encoding="utf-8") as f:
            grouped_content = f.read()
        self.assertIn("<svg", grouped_content)
        self.assertIn('class="cluster-box"', grouped_content)
        self.assertIn("compose-post-service", grouped_content)

    def test_render_composed_diagrams_all_formats(self):
        """Test top-level render_composed_diagrams coordinating flat and grouped outputs."""
        cnet = compose_workflow_nets(self.service_nets, self.topo_data, "compose_post_workflow")
        diag_dir = os.path.join(self.tmp_dir, "diagrams")
        results = render_composed_diagrams(cnet, output_dir=diag_dir)

        self.assertIn("flat_dot", results)
        self.assertIn("flat_svg", results)
        self.assertIn("grouped_dot", results)
        self.assertIn("grouped_svg", results)

        self.assertTrue(os.path.exists(results["flat_dot"]))
        self.assertTrue(os.path.exists(results["flat_svg"]))
        self.assertTrue(os.path.exists(results["grouped_dot"]))
        self.assertTrue(os.path.exists(results["grouped_svg"]))

        if "flat_png" in results:
            self.assertTrue(os.path.exists(results["flat_png"]))
        if "grouped_png" in results:
            self.assertTrue(os.path.exists(results["grouped_png"]))

    def test_cli_execution_with_diagram_export(self):
        """Test CLI execution with --export-diagrams and --diagram-dir flags."""
        diag_dir = os.path.join(self.tmp_dir, "cli_diagrams")
        cmd_args = [
            "--mined-nets", self.mined_path,
            "--topology", self.topo_path,
            "--workflow", "compose_post_workflow",
            "--output-json", os.path.join(self.tmp_dir, "composed-net.json"),
            "--output-lola", os.path.join(self.tmp_dir, "composed-net.lola"),
            "--output-pnml", os.path.join(self.tmp_dir, "composed-net.pnml"),
            "--output-report", os.path.join(self.tmp_dir, "report.json"),
            "--diagram-dir", diag_dir,
            "--export-diagrams",
            "--engine", "internal",
            "--max-states", "100000",
        ]

        exit_code = main(cmd_args)
        self.assertEqual(exit_code, 0)
        self.assertTrue(os.path.exists(os.path.join(diag_dir, "composed-net.dot")))
        self.assertTrue(os.path.exists(os.path.join(diag_dir, "composed-net.svg")))
        self.assertTrue(os.path.exists(os.path.join(diag_dir, "composed-net-grouped.dot")))
        self.assertTrue(os.path.exists(os.path.join(diag_dir, "composed-net-grouped.svg")))


if __name__ == "__main__":
    unittest.main()
