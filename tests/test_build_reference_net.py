#!/usr/bin/env python3
"""
Unit and Integration Tests for Reference Net Authoring & Verification Engine.
"""

import json
import os
from pathlib import Path
import shutil
import tempfile
import unittest

from src.build_reference_net import (
    Place,
    Transition,
    Arc,
    WorkflowNet,
    WFNetValidator,
    ReferenceNetBuilder,
    WorkflowNetRenderer,
    serialize_reference_nets,
)


class TestPetriNetPrimitives(unittest.TestCase):
    """Tests core data models: Place, Transition, Arc, WorkflowNet."""

    def test_place_attributes_and_serialization(self):
        p = Place(id="p_src", name="source", type="source", initial_marking=1, final_marking=0)
        self.assertEqual(p.id, "p_src")
        self.assertEqual(p.name, "source")
        self.assertEqual(p.type, "source")
        self.assertEqual(p.initial_marking, 1)
        self.assertEqual(p.final_marking, 0)
        d = p.to_dict()
        self.assertEqual(d["id"], "p_src")
        self.assertEqual(d["initial_marking"], 1)

    def test_transition_attributes_and_serialization(self):
        t = Transition(
            id="t_store",
            name="StorePost",
            type="rpc_dispatch",
            service="post-storage-service",
            channel="StorePost",
            span_client="store_post_client",
            span_server="store_post_server",
            phase="P2",
            launch_type="async",
        )
        self.assertEqual(t.id, "t_store")
        self.assertEqual(t.service, "post-storage-service")
        self.assertEqual(t.span_client, "store_post_client")
        d = t.to_dict()
        self.assertEqual(d["service"], "post-storage-service")
        self.assertEqual(d["span_client"], "store_post_client")
        self.assertEqual(d["phase"], "P2")

    def test_arc_attributes_and_serialization(self):
        arc = Arc(source="p1", target="t1", weight=1)
        self.assertEqual(arc.source, "p1")
        self.assertEqual(arc.target, "t1")
        self.assertEqual(arc.weight, 1)
        d = arc.to_dict()
        self.assertEqual(d["source"], "p1")
        self.assertEqual(d["target"], "t1")

    def test_workflow_net_node_management(self):
        net = WorkflowNet(name="test_wf", entry_service="test-svc", entry_channel="TestChan")
        p1 = net.add_place(Place(id="p_in", name="in", type="source", initial_marking=1))
        t1 = net.add_transition(Transition(id="t_act", name="action"))
        p2 = net.add_place(Place(id="p_out", name="out", type="sink", final_marking=1))
        net.add_arc("p_in", "t_act")
        net.add_arc("t_act", "p_out")

        self.assertEqual(len(net.places), 2)
        self.assertEqual(len(net.transitions), 1)
        self.assertEqual(len(net.arcs), 2)
        self.assertEqual(net.preset("t_act"), ["p_in"])
        self.assertEqual(net.postset("t_act"), ["p_out"])
        self.assertTrue(net.is_place("p_in"))
        self.assertTrue(net.is_transition("t_act"))

        # Duplicate place ID should raise ValueError
        with self.assertRaises(ValueError):
            net.add_place(Place(id="p_in", name="dup"))

        # Conflicting transition ID should raise ValueError
        with self.assertRaises(ValueError):
            net.add_transition(Transition(id="p_in", name="conflict"))


class TestWFNetValidator(unittest.TestCase):
    """Tests WFNetValidator invariants: source, sink, bipartite, and reachability."""

    def test_valid_minimal_wf_net(self):
        net = WorkflowNet(name="minimal_wf", entry_service="svc", entry_channel="chan")
        net.add_place(Place(id="p_src", name="source", type="source", initial_marking=1))
        net.add_transition(Transition(id="t_main", name="MainAction"))
        net.add_place(Place(id="p_snk", name="sink", type="sink", final_marking=1))
        net.add_arc("p_src", "t_main")
        net.add_arc("t_main", "p_snk")

        report = WFNetValidator.validate(net)
        self.assertTrue(report["is_wf_net"])
        self.assertEqual(report["source_places"], ["p_src"])
        self.assertEqual(report["sink_places"], ["p_snk"])
        self.assertEqual(report["unreachable_from_source"], [])
        self.assertEqual(report["cannot_reach_sink"], [])
        self.assertTrue(report["bipartite_valid"])

    def test_invalid_multiple_source_places(self):
        net = WorkflowNet(name="multi_source", entry_service="svc", entry_channel="chan")
        net.add_place(Place(id="p_src1", name="src1", type="source"))
        net.add_place(Place(id="p_src2", name="src2", type="source"))
        net.add_transition(Transition(id="t1", name="t1"))
        net.add_place(Place(id="p_snk", name="sink", type="sink"))
        net.add_arc("p_src1", "t1")
        net.add_arc("p_src2", "t1")
        net.add_arc("t1", "p_snk")

        report = WFNetValidator.validate(net)
        self.assertFalse(report["is_wf_net"])
        self.assertEqual(len(report["source_places"]), 2)
        self.assertTrue(any("Multiple source places" in err for err in report.get("errors", [])))

    def test_invalid_multiple_sink_places(self):
        net = WorkflowNet(name="multi_sink", entry_service="svc", entry_channel="chan")
        net.add_place(Place(id="p_src", name="src", type="source"))
        net.add_transition(Transition(id="t1", name="t1"))
        net.add_place(Place(id="p_snk1", name="snk1", type="sink"))
        net.add_place(Place(id="p_snk2", name="snk2", type="sink"))
        net.add_arc("p_src", "t1")
        net.add_arc("t1", "p_snk1")
        net.add_arc("t1", "p_snk2")

        report = WFNetValidator.validate(net)
        self.assertFalse(report["is_wf_net"])
        self.assertEqual(len(report["sink_places"]), 2)
        self.assertTrue(any("Multiple sink places" in err for err in report.get("errors", [])))

    def test_invalid_non_bipartite_arcs(self):
        net = WorkflowNet(name="non_bipartite", entry_service="svc", entry_channel="chan")
        net.add_place(Place(id="p_src", name="src", type="source"))
        net.add_place(Place(id="p_mid", name="mid", type="internal"))
        net.add_transition(Transition(id="t1", name="t1"))
        net.add_place(Place(id="p_snk", name="snk", type="sink"))
        # Invalid place-to-place arc
        net.add_arc("p_src", "p_mid")
        net.add_arc("p_mid", "t1")
        net.add_arc("t1", "p_snk")

        report = WFNetValidator.validate(net)
        self.assertFalse(report["is_wf_net"])
        self.assertFalse(report["bipartite_valid"])
        self.assertTrue(any("Non-bipartite arc" in err for err in report.get("errors", [])))

    def test_invalid_disconnected_orphan_node(self):
        net = WorkflowNet(name="orphan", entry_service="svc", entry_channel="chan")
        net.add_place(Place(id="p_src", name="src", type="source"))
        net.add_transition(Transition(id="t1", name="t1"))
        net.add_place(Place(id="p_snk", name="snk", type="sink"))
        # Isolated transition with no arcs
        net.add_transition(Transition(id="t_orphan", name="orphan"))
        net.add_arc("p_src", "t1")
        net.add_arc("t1", "p_snk")

        report = WFNetValidator.validate(net)
        self.assertFalse(report["is_wf_net"])
        self.assertIn("t_orphan", report["unreachable_from_source"])
        self.assertIn("t_orphan", report["cannot_reach_sink"])

    def test_invalid_dead_end_branch(self):
        net = WorkflowNet(name="dead_end", entry_service="svc", entry_channel="chan")
        net.add_place(Place(id="p_src", name="src", type="source"))
        net.add_transition(Transition(id="t_fork", name="fork"))
        net.add_place(Place(id="p_branch1", name="b1"))
        net.add_place(Place(id="p_dead", name="dead"))
        net.add_transition(Transition(id="t_main", name="main"))
        net.add_place(Place(id="p_snk", name="snk", type="sink"))

        net.add_arc("p_src", "t_fork")
        net.add_arc("t_fork", "p_branch1")
        net.add_arc("t_fork", "p_dead")  # p_dead has no outgoing arcs
        net.add_arc("p_branch1", "t_main")
        net.add_arc("t_main", "p_snk")

        report = WFNetValidator.validate(net)
        self.assertFalse(report["is_wf_net"])
        self.assertIn("p_dead", report["cannot_reach_sink"])


class TestReferenceNetBuilder(unittest.TestCase):
    """Tests ReferenceNetBuilder synthesis from social-network.json oracle."""

    @classmethod
    def setUpClass(cls):
        cls.builder = ReferenceNetBuilder("interfaces/social-network.json")
        cls.nets = cls.builder.build_all()

    def test_all_workflows_synthesized_and_valid(self):
        expected_workflows = {
            "read_home_timeline_workflow",
            "compose_post_workflow",
            "follow_workflow",
            "register_user_with_id_workflow",
            "unfollow_workflow",
            "read_user_timeline_workflow",
        }
        self.assertEqual(set(self.nets.keys()), expected_workflows)

        for wf_name, net in self.nets.items():
            val = net.validation
            self.assertTrue(val["is_wf_net"], f"Workflow '{wf_name}' failed WF-net validation: {val.get('errors')}")
            self.assertEqual(len(val["source_places"]), 1)
            self.assertEqual(len(val["sink_places"]), 1)
            self.assertEqual(val["unreachable_from_source"], [])
            self.assertEqual(val["cannot_reach_sink"], [])
            self.assertTrue(val["bipartite_valid"])

    def test_compose_post_workflow_structure(self):
        net = self.nets["compose_post_workflow"]
        self.assertEqual(net.entry_service, "compose-post-service")
        self.assertEqual(net.entry_channel, "ComposePost")

        # Verify ingress and egress
        ingress_trans = [t for t in net.transitions if t.type == "ingress"]
        self.assertEqual(len(ingress_trans), 1)
        self.assertEqual(ingress_trans[0].span_client, "compose_post_client")
        self.assertEqual(ingress_trans[0].span_server, "compose_post_server")

        egress_trans = [t for t in net.transitions if t.type == "egress"]
        self.assertEqual(len(egress_trans), 1)

        # Verify Phase P1 fork & barrier
        fork_trans = [t for t in net.transitions if t.type == "fork" and t.phase == "P1"]
        self.assertEqual(len(fork_trans), 1)

        barrier_trans = [t for t in net.transitions if t.type == "join_barrier" and t.barrier_name == "compose_post_barrier"]
        self.assertEqual(len(barrier_trans), 1)

        # Verify nested text-service subnet
        text_entry = [t for t in net.transitions if t.type == "nested_entry" and t.service == "text-service"]
        self.assertEqual(len(text_entry), 1)
        self.assertEqual(text_entry[0].span_client, "compose_text_client")

        text_fork = [t for t in net.transitions if t.type == "nested_fork" and t.service == "text-service"]
        self.assertEqual(len(text_fork), 1)

        text_children = [t for t in net.transitions if t.service in ("url-shorten-service", "user-mention-service")]
        self.assertEqual(len(text_children), 2)
        child_services = {t.service for t in text_children}
        self.assertEqual(child_services, {"url-shorten-service", "user-mention-service"})

        text_join = [t for t in net.transitions if t.type == "nested_join" and t.service == "text-service"]
        self.assertEqual(len(text_join), 1)

        text_exit = [t for t in net.transitions if t.type == "nested_exit" and t.service == "text-service"]
        self.assertEqual(len(text_exit), 1)

        # Verify Phase P2 sequential dispatches
        p2_trans = [t for t in net.transitions if t.phase == "P2"]
        self.assertEqual(len(p2_trans), 3)
        p2_services = [t.service for t in p2_trans]
        self.assertEqual(p2_services, ["post-storage-service", "user-timeline-service", "home-timeline-service"])

    def test_missing_topology_file_raises_error(self):
        with self.assertRaises(FileNotFoundError):
            ReferenceNetBuilder("non_existent_path.json")

    def test_invalid_json_topology_raises_error(self):
        with tempfile.NamedTemporaryFile(mode="w", delete=False) as f:
            f.write("{invalid_json:")
            tmp_path = f.name
        try:
            with self.assertRaises(ValueError):
                ReferenceNetBuilder(tmp_path)
        finally:
            if os.path.exists(tmp_path):
                os.remove(tmp_path)


class TestDiagramRendering(unittest.TestCase):
    """Tests DOT generation, SVG rendering, and PNG generation."""

    def setUp(self):
        self.builder = ReferenceNetBuilder("interfaces/social-network.json")
        self.nets = self.builder.build_all()
        self.temp_dir = tempfile.mkdtemp()

    def tearDown(self):
        shutil.rmtree(self.temp_dir, ignore_errors=True)

    def test_generate_dot_portrait_properties(self):
        net = self.nets["compose_post_workflow"]
        dot = WorkflowNetRenderer.generate_dot(net)
        self.assertIn('rankdir="TB";', dot)
        self.assertIn('p_source', dot)
        self.assertIn('p_sink', dot)
        self.assertIn('shape=doublecircle', dot)
        self.assertIn('compose_post_barrier', dot)

    def test_render_svg_and_png_files(self):
        net = self.nets["read_home_timeline_workflow"]
        rendered = WorkflowNetRenderer.render(net, diagram_dir=self.temp_dir, render_format="all")
        self.assertIn("svg", rendered)
        self.assertTrue(os.path.exists(rendered["svg"]))
        self.assertTrue(os.path.getsize(rendered["svg"]) > 0)

        # Check if PNG was generated (if dot binary is available)
        if shutil.which("dot"):
            self.assertIn("png", rendered)
            self.assertTrue(os.path.exists(rendered["png"]))
            self.assertTrue(os.path.getsize(rendered["png"]) > 0)

    def test_standalone_svg_fallback(self):
        net = self.nets["register_user_with_id_workflow"]
        svg_path = os.path.join(self.temp_dir, "fallback.svg")
        success = WorkflowNetRenderer.render_standalone_svg(net, svg_path)
        self.assertTrue(success)
        self.assertTrue(os.path.exists(svg_path))
        with open(svg_path, "r", encoding="utf-8") as f:
            content = f.read()
            self.assertIn("<svg", content)
            self.assertIn("register_user_with_id_workflow", content)


class TestSerialization(unittest.TestCase):
    """Tests JSON serialization formatting."""

    def test_serialize_reference_nets_payload(self):
        builder = ReferenceNetBuilder("interfaces/social-network.json")
        nets = builder.build_all()
        payload = serialize_reference_nets(nets, topology_source="interfaces/social-network.json")

        self.assertIn("_meta", payload)
        self.assertEqual(payload["_meta"]["name"], "Social Network GWF Reference Nets")
        self.assertTrue(payload["_meta"]["all_valid_wf_nets"])
        self.assertEqual(payload["_meta"]["total_workflows"], 6)

        workflows = payload["workflows"]
        self.assertIn("compose_post_workflow", workflows)
        cp_wf = workflows["compose_post_workflow"]
        self.assertIn("places", cp_wf)
        self.assertIn("transitions", cp_wf)
        self.assertIn("arcs", cp_wf)
        self.assertIn("validation", cp_wf)
        self.assertTrue(cp_wf["validation"]["is_wf_net"])


if __name__ == "__main__":
    unittest.main()
