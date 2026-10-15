#!/usr/bin/env python3
"""
Reference Net Authoring & Verification Engine.

Programmatically synthesizes Generalized Workflow (GWF) Petri reference nets
from JSON topology contracts (interfaces/social-network.json), wiring concurrent
forks, join barriers, and nested execution subnets, validating WF-net
well-formedness invariants, and rendering SVG/PNG portrait visual diagrams.

Outputs:
  - interfaces/reference-nets.json
  - interfaces/diagrams/*.svg
  - interfaces/diagrams/*.png
"""

import argparse
import collections
from dataclasses import asdict, dataclass, field
import datetime
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
from typing import Any, Dict, List, Optional, Set, Tuple


# ============================================================================
# 1. Petri Net Core Data Structures
# ============================================================================

@dataclass
class Place:
    """Represents a Petri net Place (control-flow state or condition)."""
    id: str
    name: str
    type: str = "internal"  # "source", "sink", "internal", "branch_pre", "branch_post"
    initial_marking: int = 0
    final_marking: int = 0

    def to_dict(self) -> Dict[str, Any]:
        return {
            "id": self.id,
            "name": self.name,
            "type": self.type,
            "initial_marking": self.initial_marking,
            "final_marking": self.final_marking,
        }


@dataclass
class Transition:
    """Represents a Petri net Transition (service invocation, fork, join, ingress/egress)."""
    id: str
    name: str
    type: str = "rpc_dispatch"  # "ingress", "egress", "fork", "join_barrier", "rpc_dispatch", "nested_entry", "nested_exit", "nested_fork", "nested_join"
    service: Optional[str] = None
    channel: Optional[str] = None
    span_client: Optional[str] = None
    span_server: Optional[str] = None
    phase: Optional[str] = None
    barrier_name: Optional[str] = None
    launch_type: Optional[str] = None

    def to_dict(self) -> Dict[str, Any]:
        res: Dict[str, Any] = {
            "id": self.id,
            "name": self.name,
            "type": self.type,
        }
        if self.service is not None:
            res["service"] = self.service
        if self.channel is not None:
            res["channel"] = self.channel
        if self.span_client is not None:
            res["span_client"] = self.span_client
        if self.span_server is not None:
            res["span_server"] = self.span_server
        if self.phase is not None:
            res["phase"] = self.phase
        if self.barrier_name is not None:
            res["barrier_name"] = self.barrier_name
        if self.launch_type is not None:
            res["launch_type"] = self.launch_type
        return res


@dataclass
class Arc:
    """Represents a directed Arc connecting a Place to Transition or Transition to Place."""
    source: str
    target: str
    weight: int = 1

    def to_dict(self) -> Dict[str, Any]:
        return {
            "source": self.source,
            "target": self.target,
            "weight": self.weight,
        }


@dataclass
class WorkflowNet:
    """Represents a complete Generalized Workflow (GWF) Petri Net model."""
    name: str
    entry_service: str
    entry_channel: str
    diagram_svg: Optional[str] = None
    diagram_png: Optional[str] = None
    places: List[Place] = field(default_factory=list)
    transitions: List[Transition] = field(default_factory=list)
    arcs: List[Arc] = field(default_factory=list)
    validation: Dict[str, Any] = field(default_factory=dict)

    def __post_init__(self) -> None:
        self._places_map: Dict[str, Place] = {p.id: p for p in self.places}
        self._transitions_map: Dict[str, Transition] = {t.id: t for t in self.transitions}

    def add_place(self, place: Place) -> Place:
        if place.id in self._places_map:
            raise ValueError(f"Duplicate place ID: '{place.id}'")
        if place.id in self._transitions_map:
            raise ValueError(f"Place ID conflicts with existing transition ID: '{place.id}'")
        self.places.append(place)
        self._places_map[place.id] = place
        return place

    def add_transition(self, transition: Transition) -> Transition:
        if transition.id in self._transitions_map:
            raise ValueError(f"Duplicate transition ID: '{transition.id}'")
        if transition.id in self._places_map:
            raise ValueError(f"Transition ID conflicts with existing place ID: '{transition.id}'")
        self.transitions.append(transition)
        self._transitions_map[transition.id] = transition
        return transition

    def add_arc(self, source: str, target: str, weight: int = 1) -> Arc:
        arc = Arc(source=source, target=target, weight=weight)
        self.arcs.append(arc)
        return arc

    def get_place(self, place_id: str) -> Optional[Place]:
        return self._places_map.get(place_id)

    def get_transition(self, trans_id: str) -> Optional[Transition]:
        return self._transitions_map.get(trans_id)

    def has_node(self, node_id: str) -> bool:
        return node_id in self._places_map or node_id in self._transitions_map

    def is_place(self, node_id: str) -> bool:
        return node_id in self._places_map

    def is_transition(self, node_id: str) -> bool:
        return node_id in self._transitions_map

    def preset(self, node_id: str) -> List[str]:
        """Return preset (incoming node IDs: •x)."""
        return [arc.source for arc in self.arcs if arc.target == node_id]

    def postset(self, node_id: str) -> List[str]:
        """Return postset (outgoing node IDs: x•)."""
        return [arc.target for arc in self.arcs if arc.source == node_id]

    def to_dict(self) -> Dict[str, Any]:
        return {
            "name": self.name,
            "entry_service": self.entry_service,
            "entry_channel": self.entry_channel,
            "diagram_svg": self.diagram_svg,
            "diagram_png": self.diagram_png,
            "places": [p.to_dict() for p in self.places],
            "transitions": [t.to_dict() for t in self.transitions],
            "arcs": [a.to_dict() for a in self.arcs],
            "validation": self.validation,
        }


# ============================================================================
# 2. WF-Net Well-Formedness Validator
# ============================================================================

class WFNetValidator:
    """
    Validates classical Workflow Net (WF-net) well-formedness criteria (van der Aalst):
      1. Single dedicated source place: Exactly one place i in P with in-degree 0 (•i = ∅).
      2. Single dedicated sink place: Exactly one place o in P with out-degree 0 (o• = ∅).
      3. Path completeness (Strong Connectedness): Every node x in P ∪ T lies on at least
         one directed path from source place i to sink place o:
           Forward reachability: {x | i ⇝ x} == P ∪ T
           Backward reachability: {x | x ⇝ o} == P ∪ T
      4. Strict bipartite structure: Arcs only connect P -> T or T -> P.
      5. No dead transitions or orphan nodes without both in and out connectivity
         (except source in-degree=0 and sink out-degree=0).
    """

    @classmethod
    def validate(cls, net: WorkflowNet) -> Dict[str, Any]:
        errors: List[str] = []
        all_place_ids: Set[str] = {p.id for p in net.places}
        all_trans_ids: Set[str] = {t.id for t in net.transitions}
        all_node_ids: Set[str] = all_place_ids | all_trans_ids

        # 1. Check for empty net
        if not net.places:
            errors.append("WF-net has no places.")
        if not net.transitions:
            errors.append("WF-net has no transitions.")

        # 2. Check Bipartite Structure & Endpoint existence
        bipartite_valid = True
        for arc in net.arcs:
            src_in_p = arc.source in all_place_ids
            src_in_t = arc.source in all_trans_ids
            tgt_in_p = arc.target in all_place_ids
            tgt_in_t = arc.target in all_trans_ids

            if not (src_in_p or src_in_t):
                errors.append(f"Arc source '{arc.source}' does not exist in net.")
                bipartite_valid = False
            if not (tgt_in_p or tgt_in_t):
                errors.append(f"Arc target '{arc.target}' does not exist in net.")
                bipartite_valid = False

            if (src_in_p and tgt_in_p) or (src_in_t and tgt_in_t):
                errors.append(f"Non-bipartite arc: '{arc.source}' -> '{arc.target}'")
                bipartite_valid = False

        # Build adjacency maps
        fwd_adj: Dict[str, List[str]] = collections.defaultdict(list)
        bwd_adj: Dict[str, List[str]] = collections.defaultdict(list)
        for arc in net.arcs:
            fwd_adj[arc.source].append(arc.target)
            bwd_adj[arc.target].append(arc.source)

        # 3. Source Place Check: Exactly one place with in-degree 0
        source_places = [p.id for p in net.places if len(bwd_adj[p.id]) == 0]
        if len(source_places) == 0:
            errors.append("No source place found with in-degree 0.")
        elif len(source_places) > 1:
            errors.append(f"Multiple source places found with in-degree 0: {source_places}")

        # Check that no transitions have in-degree 0
        trans_with_no_inputs = [t.id for t in net.transitions if len(bwd_adj[t.id]) == 0]
        if trans_with_no_inputs:
            errors.append(f"Transitions with in-degree 0 (no input places): {trans_with_no_inputs}")

        # 4. Sink Place Check: Exactly one place with out-degree 0
        sink_places = [p.id for p in net.places if len(fwd_adj[p.id]) == 0]
        if len(sink_places) == 0:
            errors.append("No sink place found with out-degree 0.")
        elif len(sink_places) > 1:
            errors.append(f"Multiple sink places found with out-degree 0: {sink_places}")

        # Check that no transitions have out-degree 0
        trans_with_no_outputs = [t.id for t in net.transitions if len(fwd_adj[t.id]) == 0]
        if trans_with_no_outputs:
            errors.append(f"Transitions with out-degree 0 (no output places): {trans_with_no_outputs}")

        # 5. Path Completeness (Forward & Backward Reachability)
        designated_sources = [p.id for p in net.places if p.type == "source"]
        src_start_nodes = designated_sources if designated_sources else (source_places if len(source_places) == 1 else [])

        designated_sinks = [p.id for p in net.places if p.type == "sink"]
        sink_start_nodes = designated_sinks if designated_sinks else (sink_places if len(sink_places) == 1 else [])

        unreachable_from_source: List[str] = []
        cannot_reach_sink: List[str] = []

        if src_start_nodes:
            fwd_visited: Set[str] = set()
            queue = collections.deque(src_start_nodes)
            while queue:
                curr = queue.popleft()
                if curr not in fwd_visited:
                    fwd_visited.add(curr)
                    for nxt in fwd_adj[curr]:
                        if nxt not in fwd_visited:
                            queue.append(nxt)
            unreachable = all_node_ids - fwd_visited
            if unreachable:
                unreachable_from_source = sorted(list(unreachable))
                errors.append(f"Nodes unreachable from source place(s) {src_start_nodes}: {unreachable_from_source}")

        if sink_start_nodes:
            bwd_visited: Set[str] = set()
            queue = collections.deque(sink_start_nodes)
            while queue:
                curr = queue.popleft()
                if curr not in bwd_visited:
                    bwd_visited.add(curr)
                    for prev_node in bwd_adj[curr]:
                        if prev_node not in bwd_visited:
                            queue.append(prev_node)
            unreachable_sink = all_node_ids - bwd_visited
            if unreachable_sink:
                cannot_reach_sink = sorted(list(unreachable_sink))
                errors.append(f"Nodes that cannot reach sink place(s) {sink_start_nodes}: {cannot_reach_sink}")

        is_wf_net = (len(errors) == 0)
        report: Dict[str, Any] = {
            "is_wf_net": is_wf_net,
            "source_places": source_places,
            "sink_places": sink_places,
            "unreachable_from_source": unreachable_from_source,
            "cannot_reach_sink": cannot_reach_sink,
            "bipartite_valid": bipartite_valid,
        }
        if errors:
            report["errors"] = errors
        return report


# ============================================================================
# 3. Reference Net Builder (Synthesis Engine)
# ============================================================================

class ReferenceNetBuilder:
    """
    Synthesizes Generalized Workflow (GWF) Petri reference nets from an enriched
    topology contract (interfaces/social-network.json).
    """

    def __init__(self, topology_path: str = "interfaces/social-network.json") -> None:
        self.topology_path = Path(topology_path)
        self.topology_data: Dict[str, Any] = {}
        self.reference_nets: Dict[str, WorkflowNet] = {}
        self._load_topology()

    def _load_topology(self) -> None:
        """Load and parse the topology contract JSON."""
        if not self.topology_path.exists():
            raise FileNotFoundError(f"Topology contract file not found: {self.topology_path}")
        with open(self.topology_path, "r", encoding="utf-8") as f:
            try:
                self.topology_data = json.load(f)
            except json.JSONDecodeError as exc:
                raise ValueError(f"Invalid JSON in topology contract '{self.topology_path}': {exc}")

    def build_all(self, diagram_dir: str = "interfaces/diagrams") -> Dict[str, WorkflowNet]:
        """Synthesize reference nets for all workflows declared in topology."""
        workflows = self.topology_data.get("workflows", {})
        self.reference_nets = {}

        for wf_name, wf_cfg in workflows.items():
            net = self.build_workflow_net(wf_name, wf_cfg, diagram_dir=diagram_dir)
            self.reference_nets[wf_name] = net

        return self.reference_nets

    def build_workflow_net(
        self,
        wf_name: str,
        wf_cfg: Dict[str, Any],
        diagram_dir: str = "interfaces/diagrams",
    ) -> WorkflowNet:
        """
        Synthesizes a formally sound WF-net for a single workflow definition.
        """
        entry_service = wf_cfg.get("entry_service", "")
        entry_channel = wf_cfg.get("entry_channel", "")
        server_span = wf_cfg.get("server_span")
        client_span = wf_cfg.get("client_span")
        phases = wf_cfg.get("phases", {})

        svg_path = f"{diagram_dir}/{wf_name}.svg"
        png_path = f"{diagram_dir}/{wf_name}.png"

        net = WorkflowNet(
            name=wf_name,
            entry_service=entry_service,
            entry_channel=entry_channel,
            diagram_svg=svg_path,
            diagram_png=png_path,
        )

        # 1. Ingress Stage: p_source -> t_ingress -> p_ingress_out
        p_source = net.add_place(Place(
            id="p_source",
            name="source",
            type="source",
            initial_marking=1,
            final_marking=0,
        ))
        t_ingress = net.add_transition(Transition(
            id="t_ingress",
            name=f"Ingress: {entry_channel}",
            type="ingress",
            service=entry_service,
            channel=entry_channel,
            span_client=client_span,
            span_server=server_span,
        ))
        net.add_arc(p_source.id, t_ingress.id)

        p_curr = net.add_place(Place(
            id="p_ingress_out",
            name="ingress_out",
            type="internal",
        ))
        net.add_arc(t_ingress.id, p_curr.id)

        # 2. Process Phases: P1, Barrier, P2
        p1_cfg = phases.get("P1")
        barrier_cfg = phases.get("barrier")
        p2_cfg = phases.get("P2")

        if p1_cfg:
            p1_type = p1_cfg.get("type", "sequential")
            p1_dispatches = p1_cfg.get("dispatches", [])

            if p1_type == "concurrent" and len(p1_dispatches) > 0:
                p_curr = self._synthesize_concurrent_phase(
                    net=net,
                    phase_id="P1",
                    dispatches=p1_dispatches,
                    in_place=p_curr,
                    barrier_cfg=barrier_cfg,
                )
            else:
                # Sequential P1
                p_curr = self._synthesize_sequential_dispatches(
                    net=net,
                    phase_id="P1",
                    dispatches=p1_dispatches,
                    in_place=p_curr,
                )
                if barrier_cfg:
                    p_curr = self._synthesize_standalone_barrier(net, barrier_cfg, p_curr)
        elif barrier_cfg:
            # Workflow with barrier but no P1 dispatches in JSON (e.g. follow, unfollow)
            p_curr = self._synthesize_standalone_barrier(net, barrier_cfg, p_curr)

        # 3. Phase P2 (sequential / deferred)
        if p2_cfg:
            p2_dispatches = p2_cfg.get("dispatches", [])
            p_curr = self._synthesize_sequential_dispatches(
                net=net,
                phase_id="P2",
                dispatches=p2_dispatches,
                in_place=p_curr,
            )

        # 4. Egress Stage: p_curr -> t_egress -> p_sink
        t_egress = net.add_transition(Transition(
            id="t_egress",
            name=f"Egress: {entry_channel} Return",
            type="egress",
            service=entry_service,
            channel=entry_channel,
            span_server=server_span,
        ))
        net.add_arc(p_curr.id, t_egress.id)

        p_sink = net.add_place(Place(
            id="p_sink",
            name="sink",
            type="sink",
            initial_marking=0,
            final_marking=1,
        ))
        net.add_arc(t_egress.id, p_sink.id)

        # 5. Validate Well-Formedness
        validation_report = WFNetValidator.validate(net)
        net.validation = validation_report

        return net

    def _synthesize_concurrent_phase(
        self,
        net: WorkflowNet,
        phase_id: str,
        dispatches: List[Dict[str, Any]],
        in_place: Place,
        barrier_cfg: Optional[Dict[str, Any]] = None,
    ) -> Place:
        """
        Synthesizes a concurrent fork, parallel branch places/transitions/nested subnets,
        and synchronizing join barrier.
        """
        # Fork Transition
        t_fork = net.add_transition(Transition(
            id=f"t_fork_{phase_id.lower()}",
            name=f"Fork: Phase {phase_id}",
            type="fork",
            phase=phase_id,
        ))
        net.add_arc(in_place.id, t_fork.id)

        branch_out_places: List[Place] = []

        for idx, disp in enumerate(dispatches):
            svc = disp.get("service", f"service_{idx}")
            chan = disp.get("channel", f"channel_{idx}")
            svc_slug = svc.replace("-", "_")
            chan_slug = chan.replace("-", "_")
            branch_prefix = f"b_{svc_slug}_{chan_slug}_{idx}"

            # Branch pre-place
            p_branch_in = net.add_place(Place(
                id=f"p_{branch_prefix}_in",
                name=f"{svc}::{chan} (in)",
                type="branch_pre",
            ))
            net.add_arc(t_fork.id, p_branch_in.id)

            nested_dispatches = disp.get("nested_dispatches", [])
            if nested_dispatches:
                # Multi-tier nested subnet expansion
                p_branch_out = self._synthesize_nested_subnet(
                    net=net,
                    parent_dispatch=disp,
                    in_place=p_branch_in,
                    prefix=branch_prefix,
                )
            else:
                # Leaf branch dispatch
                t_leaf = net.add_transition(Transition(
                    id=f"t_{branch_prefix}",
                    name=f"{svc}::{chan}",
                    type="rpc_dispatch",
                    service=svc,
                    channel=chan,
                    span_client=disp.get("client_span"),
                    span_server=disp.get("server_span"),
                    phase=phase_id,
                    launch_type=disp.get("launch_type", "async"),
                ))
                net.add_arc(p_branch_in.id, t_leaf.id)

                p_branch_out = net.add_place(Place(
                    id=f"p_{branch_prefix}_out",
                    name=f"{svc}::{chan} (out)",
                    type="branch_post",
                ))
                net.add_arc(t_leaf.id, p_branch_out.id)

            branch_out_places.append(p_branch_out)

        # Barrier Join Transition
        barrier_name = barrier_cfg.get("name", f"join_{phase_id.lower()}_barrier") if barrier_cfg else f"join_{phase_id.lower()}_barrier"
        t_join = net.add_transition(Transition(
            id=f"t_join_{barrier_name}",
            name=f"Join: {barrier_name}",
            type="join_barrier",
            barrier_name=barrier_name,
            phase=phase_id,
        ))
        for p_out in branch_out_places:
            net.add_arc(p_out.id, t_join.id)

        p_post_barrier = net.add_place(Place(
            id=f"p_post_{barrier_name}",
            name=f"post_{barrier_name}",
            type="internal",
        ))
        net.add_arc(t_join.id, p_post_barrier.id)

        return p_post_barrier

    def _synthesize_nested_subnet(
        self,
        net: WorkflowNet,
        parent_dispatch: Dict[str, Any],
        in_place: Place,
        prefix: str,
    ) -> Place:
        """
        Synthesizes a nested multi-tier subnet:
          in_place -> t_parent_entry -> p_nested_fork -> t_nested_fork
                   -> parallel child branches
                   -> t_nested_join -> p_nested_exit -> t_parent_exit -> p_out
        """
        svc = parent_dispatch.get("service", "")
        chan = parent_dispatch.get("channel", "")
        client_span = parent_dispatch.get("client_span")
        server_span = parent_dispatch.get("server_span")
        nested_dispatches = parent_dispatch.get("nested_dispatches", [])

        # 1. Parent Entry Transition
        t_entry = net.add_transition(Transition(
            id=f"t_{prefix}_entry",
            name=f"Entry: {svc}::{chan}",
            type="nested_entry",
            service=svc,
            channel=chan,
            span_client=client_span,
            span_server=server_span,
            launch_type=parent_dispatch.get("launch_type", "async"),
        ))
        net.add_arc(in_place.id, t_entry.id)

        p_nested_fork = net.add_place(Place(
            id=f"p_{prefix}_nested_fork_in",
            name=f"{svc} nested fork",
            type="internal",
        ))
        net.add_arc(t_entry.id, p_nested_fork.id)

        # 2. Nested Fork Transition
        t_nested_fork = net.add_transition(Transition(
            id=f"t_{prefix}_nested_fork",
            name=f"Fork: {svc} Children",
            type="nested_fork",
            service=svc,
        ))
        net.add_arc(p_nested_fork.id, t_nested_fork.id)

        # 3. Child parallel branches
        child_out_places: List[Place] = []
        for c_idx, child in enumerate(nested_dispatches):
            c_svc = child.get("service", f"c_svc_{c_idx}")
            c_chan = child.get("channel", f"c_chan_{c_idx}")
            c_svc_slug = c_svc.replace("-", "_")
            c_chan_slug = c_chan.replace("-", "_")
            child_prefix = f"{prefix}_c{c_idx}_{c_svc_slug}_{c_chan_slug}"

            p_c_in = net.add_place(Place(
                id=f"p_{child_prefix}_in",
                name=f"{c_svc}::{c_chan} (in)",
                type="branch_pre",
            ))
            net.add_arc(t_nested_fork.id, p_c_in.id)

            t_child = net.add_transition(Transition(
                id=f"t_{child_prefix}",
                name=f"{c_svc}::{c_chan}",
                type="rpc_dispatch",
                service=c_svc,
                channel=c_chan,
                span_client=child.get("client_span"),
                span_server=child.get("server_span"),
                launch_type=child.get("launch_type", "async"),
            ))
            net.add_arc(p_c_in.id, t_child.id)

            p_c_out = net.add_place(Place(
                id=f"p_{child_prefix}_out",
                name=f"{c_svc}::{c_chan} (out)",
                type="branch_post",
            ))
            net.add_arc(t_child.id, p_c_out.id)
            child_out_places.append(p_c_out)

        # 4. Nested Join Transition
        t_nested_join = net.add_transition(Transition(
            id=f"t_{prefix}_nested_join",
            name=f"Join: {svc} Children",
            type="nested_join",
            service=svc,
        ))
        for p_c_out in child_out_places:
            net.add_arc(p_c_out.id, t_nested_join.id)

        p_nested_exit = net.add_place(Place(
            id=f"p_{prefix}_nested_exit_in",
            name=f"{svc} nested exit",
            type="internal",
        ))
        net.add_arc(t_nested_join.id, p_nested_exit.id)

        # 5. Parent Exit Transition
        t_exit = net.add_transition(Transition(
            id=f"t_{prefix}_exit",
            name=f"Exit: {svc}::{chan}",
            type="nested_exit",
            service=svc,
            channel=chan,
            span_server=server_span,
        ))
        net.add_arc(p_nested_exit.id, t_exit.id)

        p_branch_out = net.add_place(Place(
            id=f"p_{prefix}_out",
            name=f"{svc}::{chan} (out)",
            type="branch_post",
        ))
        net.add_arc(t_exit.id, p_branch_out.id)

        return p_branch_out

    def _synthesize_sequential_dispatches(
        self,
        net: WorkflowNet,
        phase_id: str,
        dispatches: List[Dict[str, Any]],
        in_place: Place,
    ) -> Place:
        """Synthesizes sequential transitions in series."""
        p_curr = in_place
        for idx, disp in enumerate(dispatches):
            svc = disp.get("service", f"service_{idx}")
            chan = disp.get("channel", f"channel_{idx}")
            svc_slug = svc.replace("-", "_")
            chan_slug = chan.replace("-", "_")
            disp_id = f"t_{phase_id.lower()}_{svc_slug}_{chan_slug}_{idx}"

            t_disp = net.add_transition(Transition(
                id=disp_id,
                name=f"{svc}::{chan}",
                type="rpc_dispatch",
                service=svc,
                channel=chan,
                span_client=disp.get("client_span"),
                span_server=disp.get("server_span"),
                phase=phase_id,
                launch_type=disp.get("launch_type", "direct"),
            ))
            net.add_arc(p_curr.id, t_disp.id)

            p_next = net.add_place(Place(
                id=f"p_{phase_id.lower()}_{svc_slug}_{chan_slug}_{idx}_out",
                name=f"{svc}::{chan} (out)",
                type="internal",
            ))
            net.add_arc(t_disp.id, p_next.id)
            p_curr = p_next

        return p_curr

    def _synthesize_standalone_barrier(
        self,
        net: WorkflowNet,
        barrier_cfg: Dict[str, Any],
        in_place: Place,
    ) -> Place:
        """Synthesizes a standalone barrier transition."""
        b_name = barrier_cfg.get("name", "barrier")
        b_slug = b_name.replace("-", "_")
        t_barrier = net.add_transition(Transition(
            id=f"t_barrier_{b_slug}",
            name=f"Barrier: {b_name}",
            type="join_barrier",
            barrier_name=b_name,
        ))
        net.add_arc(in_place.id, t_barrier.id)

        p_out = net.add_place(Place(
            id=f"p_post_barrier_{b_slug}",
            name=f"post_{b_name}",
            type="internal",
        ))
        net.add_arc(t_barrier.id, p_out.id)
        return p_out


# ============================================================================
# 4. Portrait Visual Diagram Renderer (DOT / SVG / PNG)
# ============================================================================

class WorkflowNetRenderer:
    """
    Renders Workflow Petri nets into portrait visual diagrams in SVG and PNG formats.
    Strictly follows formal Petri Net / WF-net conventions:
      - Initial state: Single circle with solid black token (●) inside
      - Final state: Double circle representing accepting sink state
      - Internal states: Single circle, unmarked
      - Place names: Rendered as external labels outside the circle (xlabel)
      - Transitions: Clean rectangular blocks without emojis/icons
    """

    @classmethod
    def generate_dot(cls, net: WorkflowNet) -> str:
        """
        Generates Graphviz DOT string with portrait orientation (rankdir=TB).
        """
        lines = [
            f'digraph "{net.name}" {{',
            '  // Portrait Layout & Global Settings',
            '  rankdir="TB";',
            '  charset="UTF-8";',
            '  compound=true;',
            '  bgcolor="#FAFAFA";',
            '  node [fontname="Helvetica,Arial,sans-serif", fontsize=9];',
            '  edge [fontname="Helvetica,Arial,sans-serif", fontsize=8, color="#333333", arrowsize=0.7];',
            '',
            '  // Places (Petri Net Conventions: Single circle initial with token, double circle final sink)',
        ]

        for p in net.places:
            if p.type == "source":
                # Initial State: Single circle with token ● inside, name outside via xlabel
                label = "●" if p.initial_marking > 0 else ""
                lines.append(
                    f'  "{p.id}" [shape=circle, style="filled", fillcolor="#D0E1F9", '
                    f'color="#1E395B", penwidth=1.8, label="{label}", '
                    f'xlabel=<<FONT POINT-SIZE="8" COLOR="#1E395B">{p.name}</FONT>>, '
                    f'width=0.28, height=0.28, fixedsize=true, fontsize=10];'
                )
            elif p.type == "sink":
                # Final State: Double circle, name outside via xlabel
                lines.append(
                    f'  "{p.id}" [shape=doublecircle, style="filled", fillcolor="#FDE8E8", '
                    f'color="#9B1C1C", penwidth=1.8, label="", '
                    f'xlabel=<<FONT POINT-SIZE="8" COLOR="#9B1C1C">{p.name}</FONT>>, '
                    f'width=0.28, height=0.28, fixedsize=true, fontsize=9];'
                )
            elif p.type in ("branch_pre", "branch_post"):
                # Branch Places: Single circle, name outside via xlabel
                lines.append(
                    f'  "{p.id}" [shape=circle, style="filled", fillcolor="#F3F4F6", '
                    f'color="#4B5563", penwidth=1.2, label="", '
                    f'xlabel=<<FONT POINT-SIZE="7" COLOR="#4B5563">{p.name}</FONT>>, '
                    f'width=0.22, height=0.22, fixedsize=true, fontsize=7];'
                )
            else:
                # Internal Places: Single circle, name outside via xlabel
                lines.append(
                    f'  "{p.id}" [shape=circle, style="filled", fillcolor="#EBF3FA", '
                    f'color="#2A6496", penwidth=1.2, label="", '
                    f'xlabel=<<FONT POINT-SIZE="7" COLOR="#2A6496">{p.name}</FONT>>, '
                    f'width=0.22, height=0.22, fixedsize=true, fontsize=7];'
                )

        lines.append('')
        lines.append('  // Transitions (Clean styling, no decorative icons)')

        for t in net.transitions:
            t_type = t.type
            if t_type in ("fork", "nested_fork"):
                fill = "#FEF3C7"
                border = "#D97706"
                label = (
                    f'<<TABLE BORDER="0" CELLBORDER="0" CELLSPACING="1">'
                    f'<TR><TD><B><FONT COLOR="#92400E">{t.name}</FONT></B></TD></TR>'
                    f'</TABLE>>'
                )
            elif t_type in ("join_barrier", "nested_join"):
                fill = "#FEF3C7"
                border = "#D97706"
                b_info = f'<TR><TD><FONT POINT-SIZE="8" COLOR="#78350F">Barrier: {t.barrier_name}</FONT></TD></TR>' if t.barrier_name else ''
                label = (
                    f'<<TABLE BORDER="0" CELLBORDER="0" CELLSPACING="1">'
                    f'<TR><TD><B><FONT COLOR="#92400E">{t.name}</FONT></B></TD></TR>'
                    f'{b_info}'
                    f'</TABLE>>'
                )
            elif t_type == "ingress":
                fill = "#E0F2FE"
                border = "#0284C7"
                span_info = t.span_client or t.span_server or ""
                span_row = f'<TR><TD><FONT POINT-SIZE="7" COLOR="#64748B">span: {span_info}</FONT></TD></TR>' if span_info else ''
                label = (
                    f'<<TABLE BORDER="0" CELLBORDER="0" CELLSPACING="1">'
                    f'<TR><TD><B><FONT COLOR="#0369A1">{t.name}</FONT></B></TD></TR>'
                    f'<TR><TD><FONT POINT-SIZE="8" COLOR="#475569">{t.service}::{t.channel}</FONT></TD></TR>'
                    f'{span_row}'
                    f'</TABLE>>'
                )
            elif t_type == "egress":
                fill = "#DCFCE7"
                border = "#16A34A"
                label = (
                    f'<<TABLE BORDER="0" CELLBORDER="0" CELLSPACING="1">'
                    f'<TR><TD><B><FONT COLOR="#15803D">{t.name}</FONT></B></TD></TR>'
                    f'<TR><TD><FONT POINT-SIZE="8" COLOR="#475569">{t.service}::{t.channel}</FONT></TD></TR>'
                    f'</TABLE>>'
                )
            elif t_type in ("nested_entry", "nested_exit"):
                fill = "#F1F5F9"
                border = "#64748B"
                label = (
                    f'<<TABLE BORDER="0" CELLBORDER="0" CELLSPACING="1">'
                    f'<TR><TD><B><FONT COLOR="#334155">{t.name}</FONT></B></TD></TR>'
                    f'<TR><TD><FONT POINT-SIZE="8" COLOR="#475569">{t.service}::{t.channel}</FONT></TD></TR>'
                    f'</TABLE>>'
                )
            else:
                # Standard RPC dispatch
                fill = "#F2F9EC"
                border = "#3C763D"
                span_info = t.span_client or t.span_server or ""
                span_row = f'<TR><TD><FONT POINT-SIZE="7" COLOR="#64748B">span: {span_info}</FONT></TD></TR>' if span_info else ''
                launch_row = f'<TR><TD><FONT POINT-SIZE="7" COLOR="#854D0E">[{t.launch_type}]</FONT></TD></TR>' if t.launch_type else ''
                label = (
                    f'<<TABLE BORDER="0" CELLBORDER="0" CELLSPACING="1">'
                    f'<TR><TD><B><FONT COLOR="#1B4D1B">{t.name}</FONT></B></TD></TR>'
                    f'{span_row}'
                    f'{launch_row}'
                    f'</TABLE>>'
                )

            lines.append(
                f'  "{t.id}" [shape=box, style="filled", fillcolor="{fill}", '
                f'color="{border}", penwidth=1.5, label={label}];'
            )

        lines.append('')
        lines.append('  // Arcs')
        for arc in net.arcs:
            lines.append(f'  "{arc.source}" -> "{arc.target}";')

        lines.append('}')
        return '\n'.join(lines)

    @classmethod
    def render_via_graphviz(cls, dot_str: str, output_path: str, format_type: str) -> bool:
        """Executes Graphviz 'dot' CLI to produce SVG or PNG."""
        dot_bin = shutil.which("dot")
        if not dot_bin:
            return False
        try:
            cmd = [dot_bin, f"-T{format_type}", "-o", output_path]
            proc = subprocess.run(cmd, input=dot_str.encode("utf-8"), capture_output=True, check=True)
            return proc.returncode == 0
        except Exception:
            return False

    @classmethod
    def render_standalone_svg(cls, net: WorkflowNet, output_path: str) -> bool:
        """
        Pure-Python fallback SVG renderer when Graphviz binary is not available.
        Places nodes in top-to-bottom vertical topological bands.
        """
        # Topological level computation
        in_degrees: Dict[str, int] = collections.defaultdict(int)
        all_nodes = [p.id for p in net.places] + [t.id for t in net.transitions]
        for arc in net.arcs:
            in_degrees[arc.target] += 1

        levels: Dict[str, int] = {}
        queue = collections.deque([n for n in all_nodes if in_degrees[n] == 0])
        for n in queue:
            levels[n] = 0

        # Run BFS to compute longest distance from source
        fwd_adj: Dict[str, List[str]] = collections.defaultdict(list)
        for arc in net.arcs:
            fwd_adj[arc.source].append(arc.target)

        while queue:
            curr = queue.popleft()
            curr_lvl = levels[curr]
            for nxt in fwd_adj[curr]:
                if nxt not in levels or levels[nxt] < curr_lvl + 1:
                    levels[nxt] = curr_lvl + 1
                    queue.append(nxt)

        # Group by level
        level_groups: Dict[int, List[str]] = collections.defaultdict(list)
        for n in all_nodes:
            lvl = levels.get(n, 0)
            level_groups[lvl].append(n)

        sorted_levels = sorted(level_groups.keys())
        max_width_count = max((len(nodes) for nodes in level_groups.values()), default=1)

        # SVG layout constants
        col_width = 240
        row_height = 80
        svg_width = max(600, (max_width_count + 1) * col_width)
        svg_height = max(400, (len(sorted_levels) + 2) * row_height)

        node_positions: Dict[str, Tuple[float, float]] = {}
        for lvl in sorted_levels:
            nodes_in_lvl = level_groups[lvl]
            y = (lvl + 1) * row_height
            k = len(nodes_in_lvl)
            for idx, nid in enumerate(nodes_in_lvl):
                x = (svg_width / (k + 1)) * (idx + 1)
                node_positions[nid] = (x, y)

        svg_lines = [
            f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {svg_width} {svg_height}" width="{svg_width}" height="{svg_height}">',
            f'  <title>{net.name}</title>',
            '  <defs>',
            '    <marker id="arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse">',
            '      <path d="M 0 0 L 10 5 L 0 10 z" fill="#333333" />',
            '    </marker>',
            '  </defs>',
            '  <style>',
            '    .place-lbl { font-family: sans-serif; font-size: 10px; fill: #1E395B; text-anchor: middle; dominant-baseline: central; }',
            '    .trans-lbl { font-family: sans-serif; font-size: 10px; font-weight: 600; fill: #1B4D1B; text-anchor: middle; dominant-baseline: central; }',
            '    .edge { stroke: #475569; stroke-width: 1.5; fill: none; marker-end: url(#arrow); }',
            '  </style>',
            f'  <rect width="100%" height="100%" fill="#FAFAFA" />',
            '',
            '  <!-- Arcs -->',
        ]

        for arc in net.arcs:
            if arc.source in node_positions and arc.target in node_positions:
                x1, y1 = node_positions[arc.source]
                x2, y2 = node_positions[arc.target]
                svg_lines.append(f'  <line x1="{x1:.1f}" y1="{y1:.1f}" x2="{x2:.1f}" y2="{y2:.1f}" class="edge" />')

        svg_lines.append('')
        svg_lines.append('  <!-- Nodes -->')

        for p in net.places:
            if p.id in node_positions:
                x, y = node_positions[p.id]
                fill = "#D0E1F9" if p.type == "source" else ("#FDE8E8" if p.type == "sink" else "#EBF3FA")
                stroke = "#1E395B" if p.type == "source" else ("#9B1C1C" if p.type == "sink" else "#2A6496")
                r = 10
                svg_lines.append(f'  <circle cx="{x:.1f}" cy="{y:.1f}" r="{r}" fill="{fill}" stroke="{stroke}" stroke-width="1.8" />')
                if p.type == "sink":
                    svg_lines.append(f'  <circle cx="{x:.1f}" cy="{y:.1f}" r="{r-3}" fill="none" stroke="{stroke}" stroke-width="1.2" />')
                if p.type == "source" and p.initial_marking > 0:
                    svg_lines.append(f'  <text x="{x:.1f}" y="{y:.1f}" class="place-lbl" font-size="8px">●</text>')
                # Place label text outside the circle
                svg_lines.append(f'  <text x="{x + r + 4:.1f}" y="{y:.1f}" font-family="sans-serif" font-size="8px" fill="#475569" text-anchor="start" dominant-baseline="central">{p.name}</text>')

        for t in net.transitions:
            if t.id in node_positions:
                x, y = node_positions[t.id]
                w, h = 180, 36
                rx, ry = x - w/2, y - h/2
                fill = "#FEF3C7" if "fork" in t.type or "join" in t.type else ("#E0F2FE" if t.type == "ingress" else ("#DCFCE7" if t.type == "egress" else "#F2F9EC"))
                stroke = "#D97706" if "fork" in t.type or "join" in t.type else ("#0284C7" if t.type == "ingress" else ("#16A34A" if t.type == "egress" else "#3C763D"))
                svg_lines.append(f'  <rect x="{rx:.1f}" y="{ry:.1f}" width="{w}" height="{h}" fill="{fill}" stroke="{stroke}" stroke-width="1.5" />')
                svg_lines.append(f'  <text x="{x:.1f}" y="{y:.1f}" class="trans-lbl">{t.name[:26]}</text>')

        svg_lines.append('</svg>')

        try:
            Path(output_path).parent.mkdir(parents=True, exist_ok=True)
            with open(output_path, "w", encoding="utf-8") as f:
                f.write('\n'.join(svg_lines))
            return True
        except Exception:
            return False

    @classmethod
    def render(
        cls,
        net: WorkflowNet,
        diagram_dir: str = "interfaces/diagrams",
        render_format: str = "all",
    ) -> Dict[str, str]:
        """
        Renders diagram for the given WorkflowNet into SVG and/or PNG.
        Returns a dict of format -> written file path.
        """
        out_dir = Path(diagram_dir)
        out_dir.mkdir(parents=True, exist_ok=True)

        results: Dict[str, str] = {}
        dot_str = cls.generate_dot(net)

        # Also write the .dot definition
        dot_file = out_dir / f"{net.name}.dot"
        with open(dot_file, "w", encoding="utf-8") as f:
            f.write(dot_str)

        svg_file = out_dir / f"{net.name}.svg"
        png_file = out_dir / f"{net.name}.png"

        formats_to_render = ["svg", "png"] if render_format == "all" else [render_format]

        for fmt in formats_to_render:
            if fmt == "svg":
                rendered = cls.render_via_graphviz(dot_str, str(svg_file), "svg")
                if not rendered:
                    # Fallback to pure-Python SVG
                    cls.render_standalone_svg(net, str(svg_file))
                results["svg"] = str(svg_file)
            elif fmt == "png":
                rendered = cls.render_via_graphviz(dot_str, str(png_file), "png")
                if rendered:
                    results["png"] = str(png_file)

        return results


# ============================================================================
# 5. Serialization and Export
# ============================================================================

def serialize_reference_nets(
    reference_nets: Dict[str, WorkflowNet],
    topology_source: str = "interfaces/social-network.json",
    diagram_dir: str = "interfaces/diagrams",
) -> Dict[str, Any]:
    """Formats all synthesized reference nets into JSON oracle structure."""
    all_valid = all(net.validation.get("is_wf_net", False) for net in reference_nets.values())

    payload: Dict[str, Any] = {
        "_meta": {
            "name": "Social Network GWF Reference Nets",
            "version": "1.0.0",
            "topology_source": topology_source,
            "generated_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
            "all_valid_wf_nets": all_valid,
            "total_workflows": len(reference_nets),
            "diagram_dir": diagram_dir,
        },
        "workflows": {
            wf_name: net.to_dict()
            for wf_name, net in reference_nets.items()
        }
    }
    return payload


# ============================================================================
# 6. CLI Interface
# ============================================================================

def build_cli_parser() -> argparse.ArgumentParser:
    """Constructs the command-line argument parser."""
    parser = argparse.ArgumentParser(
        description="Synthesize, validate, and render Generalized Workflow (GWF) Petri reference nets."
    )
    parser.add_argument(
        "--topology",
        default="interfaces/social-network.json",
        help="Path to enriched topology contract JSON (default: interfaces/social-network.json)",
    )
    parser.add_argument(
        "--output",
        default="interfaces/reference-nets.json",
        help="Path to output reference nets JSON artifact (default: interfaces/reference-nets.json)",
    )
    parser.add_argument(
        "--render",
        action="store_true",
        default=True,
        help="Render SVG and PNG portrait diagrams (default: True)",
    )
    parser.add_argument(
        "--no-render",
        dest="render",
        action="store_false",
        help="Disable diagram rendering",
    )
    parser.add_argument(
        "--render-format",
        choices=["svg", "png", "all"],
        default="all",
        help="Diagram rendering format (default: all)",
    )
    parser.add_argument(
        "--diagram-dir",
        default="interfaces/diagrams",
        help="Directory to save rendered diagrams (default: interfaces/diagrams)",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="Exit with non-zero code if any generated net fails WF-net well-formedness validation",
    )
    return parser


def main() -> int:
    parser = build_cli_parser()
    args = parser.parse_args()

    print("=" * 70)
    print("GWF Reference Net Authoring & Verification Engine")
    print(f"Topology source: {args.topology}")
    print(f"Output artifact: {args.output}")
    print(f"Diagram dir:     {args.diagram_dir}")
    print("=" * 70)

    try:
        builder = ReferenceNetBuilder(topology_path=args.topology)
    except Exception as exc:
        print(f"[-] ERROR: Failed to load topology contract: {exc}", file=sys.stderr)
        return 1

    nets = builder.build_all(diagram_dir=args.diagram_dir)
    print(f"[+] Synthesized {len(nets)} reference nets:")

    all_sound = True
    for name, net in nets.items():
        val = net.validation
        is_wf = val.get("is_wf_net", False)
        status_str = "✓ SOUND WF-NET" if is_wf else "✗ INVALID"
        print(f"    - {name:<35} : {status_str} (Places={len(net.places)}, Transitions={len(net.transitions)}, Arcs={len(net.arcs)})")
        if not is_wf:
            all_sound = False
            for err in val.get("errors", []):
                print(f"        ! {err}")

    # Render diagrams
    if args.render:
        print(f"\n[+] Rendering portrait diagrams ({args.render_format}) to {args.diagram_dir}...")
        for name, net in nets.items():
            rendered = WorkflowNetRenderer.render(net, diagram_dir=args.diagram_dir, render_format=args.render_format)
            rendered_fmts = ", ".join(rendered.keys()) if rendered else "dot only"
            print(f"    - Rendered {name} -> {rendered_fmts}")

    # Serialize JSON
    payload = serialize_reference_nets(
        reference_nets=nets,
        topology_source=args.topology,
        diagram_dir=args.diagram_dir,
    )

    out_path = Path(args.output)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(payload, f, indent=2)

    print(f"\n[+] Reference nets serialized to {out_path}")
    print("=" * 70)

    if args.check and not all_sound:
        print("[-] Check failed: One or more reference nets failed WF-net validation.", file=sys.stderr)
        return 1

    return 0


if __name__ == "__main__":
    sys.exit(main())
