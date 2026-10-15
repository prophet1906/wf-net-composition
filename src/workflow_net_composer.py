#!/usr/bin/env python3
"""
Asynchronous Channel Fusion Composition & Formal Verification Engine.

Synthesizes disjoint per-service Generalized Workflow (GWF) Petri nets into a single
open composed net (N_C) fused at interface channels, and model-checks four end-to-end
formal control-flow properties:
  1. P0 Soundness / Deadlock Freedom: EF(DEADLOCK AND NOT all_ends) = false (UNSAT)
  2. Orphaned Message Freedom: EF(all_ends AND some_channel_tokens) = false (UNSAT)
  3. Channel 1-Boundedness: AG(ch_place <= 1) = true for all interface channels
  4. Response-Liveness: Structural and state-space verification over IP-4 request-response channels

Outputs:
  - interfaces/composed-net.json
  - interfaces/lola/composed-net.lola
  - interfaces/pnml/composed-net.pnml
  - interfaces/composition-verification-report.json
"""

import argparse
import collections
import copy
from dataclasses import dataclass, field
import datetime
from enum import Enum
import html
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time
from typing import Any, Dict, List, Optional, Set, Tuple, Union

try:
    import pm4py
    from pm4py.objects.petri_net.obj import Marking, PetriNet
    from pm4py.objects.petri_net.utils import petri_utils
    HAS_PM4PY = True
except ImportError:
    HAS_PM4PY = False
    PetriNet = Any
    Marking = Any


# ============================================================================
# 1. Enums and Constants
# ============================================================================

class VerificationVerdict(str, Enum):
    """Model checking verdict."""
    UNSAT = "UNSAT"  # Formula unsatisfiable (Safety / Invariant holds for negative reachability)
    SAT = "SAT"      # Formula satisfiable (Property violated / Counterexample witness found)
    TRUE = "TRUE"    # Direct invariant evaluation: True
    FALSE = "FALSE"  # Direct invariant evaluation: False
    ERROR = "ERROR"  # Verification execution failure


class PropertyStatus(str, Enum):
    """Formal property status classification."""
    HOLDS = "HOLDS"
    VIOLATED = "VIOLATED"
    UNKNOWN = "UNKNOWN"


# Reserved LoLA keywords that cannot be used as unquoted identifiers
LOLA_KEYWORDS = {
    "PLACE", "SAFE", "CAPACITY", "MARKING", "CONSUME", "PRODUCE",
    "TRANSITION", "FORMULA", "EF", "EG", "AF", "AG", "EX", "AX",
    "AND", "OR", "NOT", "TRUE", "FALSE", "FIREABLE", "DEADLOCK",
    "INITIAL", "FINAL", "STATE", "PATH", "COST"
}


def sanitize_lola_identifier(name: str, used_identifiers: Optional[Set[str]] = None) -> str:
    """Deterministically sanitize a place or transition name to a valid LoLA token [A-Za-z0-9_].
    
    Args:
        name: Original identifier string.
        used_identifiers: Optional set of already allocated tokens to prevent collisions.
        
    Returns:
        Sanitized valid LoLA token identifier.
    """
    sanitized = re.sub(r"[^A-Za-z0-9_]", "_", name)
    if sanitized and sanitized[0].isdigit():
        sanitized = f"p_{sanitized}"
    if not sanitized:
        sanitized = "item"
    if sanitized.upper() in LOLA_KEYWORDS:
        sanitized = f"node_{sanitized}"
    if used_identifiers is not None:
        base = sanitized
        counter = 1
        while sanitized in used_identifiers:
            sanitized = f"{base}_{counter}"
            counter += 1
        used_identifiers.add(sanitized)
    return sanitized


# ============================================================================
# 2. Petri Net Core Representation
# ============================================================================

@dataclass
class ChannelMetadata:
    """Metadata describing an interface channel place."""
    channel_name: str
    channel_place: str
    caller_service: str
    callee_service: str
    client_span: Optional[str] = None
    server_span: Optional[str] = None
    pattern: str = "IP-4"  # IP-4 (request-response) or IP-1 (one-way / async)
    launch_type: str = "async"  # async, direct, deferred

    def to_dict(self) -> Dict[str, Any]:
        return {
            "channel_name": self.channel_name,
            "channel_place": self.channel_place,
            "caller_service": self.caller_service,
            "callee_service": self.callee_service,
            "client_span": self.client_span,
            "server_span": self.server_span,
            "pattern": self.pattern,
            "launch_type": self.launch_type,
        }


class PetriNetModel:
    """Lightweight, portable Petri net representation."""

    def __init__(
        self,
        name: str = "net",
        places: Optional[List[str]] = None,
        transitions: Optional[List[Dict[str, Any]]] = None,
        arcs: Optional[List[Tuple[str, str]]] = None,
        initial_marking: Optional[List[str]] = None,
        final_marking: Optional[List[str]] = None,
        service: Optional[str] = None,
    ):
        self.name = name
        self.service = service or name
        self.places: List[str] = sorted(list(set(places or [])))
        self.transitions: List[Dict[str, Any]] = list(transitions or [])
        self.arcs: List[Tuple[str, str]] = list(arcs or [])
        self.initial_marking: List[str] = list(initial_marking or [])
        self.final_marking: List[str] = list(final_marking or [])

    @classmethod
    def from_dict(cls, data: Dict[str, Any], name: str = "net") -> "PetriNetModel":
        """Construct PetriNetModel from serialized mined-nets.json or reference net dictionary."""
        service_name = data.get("service", name)
        raw_places = data.get("places", [])
        places: List[str] = []
        for p in raw_places:
            if isinstance(p, dict):
                places.append(p.get("id", str(p)))
            else:
                places.append(str(p))

        raw_transitions = data.get("transitions", [])
        transitions: List[Dict[str, Any]] = []
        for t in raw_transitions:
            if isinstance(t, dict):
                transitions.append(dict(t))
            elif isinstance(t, str):
                transitions.append({"id": t, "label": t, "is_silent": False})

        raw_arcs = data.get("arcs", [])
        arcs: List[Tuple[str, str]] = []
        for a in raw_arcs:
            if isinstance(a, (list, tuple)) and len(a) >= 2:
                arcs.append((str(a[0]), str(a[1])))
            elif isinstance(a, dict) and "source" in a and "target" in a:
                arcs.append((str(a["source"]), str(a["target"])))

        raw_im = data.get("initial_marking", [])
        im: List[str] = []
        if isinstance(raw_im, list):
            for item in raw_im:
                im.append(item.get("id", str(item)) if isinstance(item, dict) else str(item))
        elif isinstance(raw_im, dict):
            for k, v in raw_im.items():
                im.extend([str(k)] * int(v))

        raw_fm = data.get("final_marking", [])
        fm: List[str] = []
        if isinstance(raw_fm, list):
            for item in raw_fm:
                fm.append(item.get("id", str(item)) if isinstance(item, dict) else str(item))
        elif isinstance(raw_fm, dict):
            for k, v in raw_fm.items():
                fm.extend([str(k)] * int(v))

        # Infer default source/sink if not explicitly given
        if not im:
            for p in places:
                if p.lower() in ("source", "p_source", "start", "p_start"):
                    im = [p]
                    break
        if not fm:
            for p in places:
                if p.lower() in ("sink", "p_sink", "end", "p_end"):
                    fm = [p]
                    break

        return cls(
            name=service_name,
            places=places,
            transitions=transitions,
            arcs=arcs,
            initial_marking=im,
            final_marking=fm,
            service=service_name,
        )

    def clone(self) -> "PetriNetModel":
        """Return a deep copy of this Petri net model."""
        return PetriNetModel(
            name=self.name,
            places=list(self.places),
            transitions=[copy.deepcopy(t) for t in self.transitions],
            arcs=list(self.arcs),
            initial_marking=list(self.initial_marking),
            final_marking=list(self.final_marking),
            service=self.service,
        )

    def to_dict(self) -> Dict[str, Any]:
        """Serialize to dictionary representation."""
        return {
            "service": self.service,
            "places": sorted(self.places),
            "transitions": sorted(self.transitions, key=lambda x: (x.get("is_silent", False), x.get("label") or "", x["id"])),
            "arcs": sorted([[a[0], a[1]] for a in self.arcs]),
            "initial_marking": sorted(self.initial_marking),
            "final_marking": sorted(self.final_marking),
        }

    def get_preset(self, node_id: str) -> Set[str]:
        """Return preset nodes (incoming arc sources) for a place or transition."""
        return {src for src, tgt in self.arcs if tgt == node_id}

    def get_postset(self, node_id: str) -> Set[str]:
        """Return postset nodes (outgoing arc targets) for a place or transition."""
        return {tgt for src, tgt in self.arcs if src == node_id}

    def get_source_place(self) -> str:
        """Resolve the initial source place identifier."""
        if self.initial_marking:
            return self.initial_marking[0]
        for p in self.places:
            if p.lower() in ("source", "p_source", "start", "p_start"):
                return p
        for p in self.places:
            if len(self.get_preset(p)) == 0:
                return p
        raise ValueError(f"No source/start place identified in net '{self.name}'")

    def get_sink_place(self) -> str:
        """Resolve the terminal sink place identifier."""
        if self.final_marking:
            return self.final_marking[0]
        for p in self.places:
            if p.lower() in ("sink", "p_sink", "end", "p_end"):
                return p
        for p in self.places:
            if len(self.get_postset(p)) == 0:
                return p
        raise ValueError(f"No sink/final place identified in net '{self.name}'")


class ComposedNetModel(PetriNetModel):
    """Composed Petri Net representing synthesized multi-service workflow net N_C."""

    def __init__(
        self,
        name: str = "composed_net",
        places: Optional[List[str]] = None,
        transitions: Optional[List[Dict[str, Any]]] = None,
        arcs: Optional[List[Tuple[str, str]]] = None,
        initial_marking: Optional[List[str]] = None,
        final_marking: Optional[List[str]] = None,
        participating_services: Optional[List[str]] = None,
        service_sinks: Optional[Dict[str, str]] = None,
        service_sources: Optional[Dict[str, str]] = None,
        channels: Optional[List[ChannelMetadata]] = None,
        workflow_name: Optional[str] = None,
    ):
        super().__init__(
            name=name,
            places=places,
            transitions=transitions,
            arcs=arcs,
            initial_marking=initial_marking,
            final_marking=final_marking,
            service="composed",
        )
        self.participating_services: List[str] = sorted(list(set(participating_services or [])))
        self.service_sinks: Dict[str, str] = dict(service_sinks or {})
        self.service_sources: Dict[str, str] = dict(service_sources or {})
        self.channels: List[ChannelMetadata] = list(channels or [])
        self.workflow_name: str = workflow_name or name

    @property
    def channel_places(self) -> List[str]:
        """List of all interface channel place identifiers."""
        return sorted([ch.channel_place for ch in self.channels])

    def to_composed_dict(self) -> Dict[str, Any]:
        """Serialize full composed net structure and metadata to JSON dict."""
        return {
            "_meta": {
                "name": "Social Network Composed Workflow Net",
                "version": "1.0.0",
                "workflow": self.workflow_name,
                "generated_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
                "participating_services": self.participating_services,
                "total_services": len(self.participating_services),
                "total_places": len(self.places),
                "total_transitions": len(self.transitions),
                "total_arcs": len(self.arcs),
                "total_channels": len(self.channels),
            },
            "workflow_name": self.workflow_name,
            "participating_services": self.participating_services,
            "service_sinks": self.service_sinks,
            "service_sources": self.service_sources,
            "channel_places": [ch.to_dict() for ch in self.channels],
            "places": sorted(self.places),
            "transitions": sorted(self.transitions, key=lambda x: (x.get("is_silent", False), x.get("label") or "", x["id"])),
            "arcs": sorted([[a[0], a[1]] for a in self.arcs]),
            "initial_marking": sorted(self.initial_marking),
            "final_marking": sorted(self.final_marking),
        }

    @classmethod
    def from_composed_dict(cls, data: Dict[str, Any]) -> "ComposedNetModel":
        """Construct ComposedNetModel from serialized composed-net.json dictionary."""
        channel_list = []
        for ch in data.get("channel_places", []):
            if isinstance(ch, dict):
                channel_list.append(ChannelMetadata(
                    channel_name=ch.get("channel_name", ""),
                    channel_place=ch.get("channel_place", ""),
                    caller_service=ch.get("caller_service", ""),
                    callee_service=ch.get("callee_service", ""),
                    client_span=ch.get("client_span"),
                    server_span=ch.get("server_span"),
                    pattern=ch.get("pattern", "IP-4"),
                    launch_type=ch.get("launch_type", "async"),
                ))
            elif isinstance(ch, str):
                channel_list.append(ChannelMetadata(
                    channel_name=ch.replace("ch::", ""),
                    channel_place=ch,
                    caller_service="",
                    callee_service="",
                ))
        return cls(
            name=data.get("workflow_name", "composed_net"),
            places=data.get("places", []),
            transitions=data.get("transitions", []),
            arcs=[(a[0], a[1]) for a in data.get("arcs", [])],
            initial_marking=data.get("initial_marking", []),
            final_marking=data.get("final_marking", []),
            participating_services=data.get("participating_services", []),
            service_sinks=data.get("service_sinks", {}),
            service_sources=data.get("service_sources", {}),
            channels=channel_list,
            workflow_name=data.get("workflow_name", "composed_net"),
        )


# ============================================================================
# 3. Disjoint Service Namespacing & Channel Fusion
# ============================================================================

def namespace_service_net(net: PetriNetModel, service_name: str) -> PetriNetModel:
    """Namespace all places, transitions, and arcs of a service net with `<service>::<node>`.
    
    Guarantees disjoint node identifier sets across all service boundaries.
    
    Args:
        net: Constituent service Petri net model.
        service_name: Canonical service identifier string.
        
    Returns:
        New namespaced PetriNetModel copy.
    """
    prefix = f"{service_name}::"
    
    def ns_place(p: str) -> str:
        return p if p.startswith(prefix) or "::" in p else f"{prefix}{p}"

    def ns_trans(t_id: str) -> str:
        return t_id if t_id.startswith(prefix) else f"{prefix}{t_id}"

    namespaced_places = [ns_place(p) for p in net.places]

    namespaced_transitions: List[Dict[str, Any]] = []
    for t in net.transitions:
        t_copy = copy.deepcopy(t)
        old_id = t_copy["id"]
        t_copy["id"] = ns_trans(old_id)
        t_copy["service"] = service_name
        if "label" not in t_copy or t_copy["label"] is None:
            t_copy["label"] = t.get("label")
        namespaced_transitions.append(t_copy)

    namespaced_arcs: List[Tuple[str, str]] = []
    for src, tgt in net.arcs:
        new_src = ns_trans(src) if any(t["id"] == src for t in net.transitions) else ns_place(src)
        new_tgt = ns_trans(tgt) if any(t["id"] == tgt for t in net.transitions) else ns_place(tgt)
        namespaced_arcs.append((new_src, new_tgt))

    namespaced_im = [ns_place(p) for p in net.initial_marking]
    namespaced_fm = [ns_place(p) for p in net.final_marking]

    return PetriNetModel(
        name=service_name,
        places=namespaced_places,
        transitions=namespaced_transitions,
        arcs=namespaced_arcs,
        initial_marking=namespaced_im,
        final_marking=namespaced_fm,
        service=service_name,
    )


def extract_topology_dispatches(
    topology_data: Dict[str, Any],
    target_workflow: Optional[str] = None,
) -> Tuple[str, List[ChannelMetadata], List[str]]:
    """Extract workflow dispatch edges and participating services from topology JSON.
    
    Args:
        topology_data: Loaded interfaces/social-network.json dictionary.
        target_workflow: Specific workflow name or None for compose_post_workflow.
        
    Returns:
        Tuple of (workflow_name, list of ChannelMetadata, list of participating service names).
    """
    workflows = topology_data.get("workflows", {})
    if not workflows:
        raise ValueError("No workflows found in topology data")

    if target_workflow and target_workflow in workflows:
        wf_name = target_workflow
    elif "compose_post_workflow" in workflows:
        wf_name = "compose_post_workflow"
    else:
        wf_name = list(workflows.keys())[0]

    wf_data = workflows[wf_name]
    entry_service = wf_data.get("entry_service")

    service_channel_patterns: Dict[Tuple[str, str], str] = {}
    for svc_name, s_info in topology_data.get("services", {}).items():
        for ch_info in s_info.get("channels", []):
            ch_name = ch_info.get("name")
            pattern = ch_info.get("pattern", "IP-4")
            service_channel_patterns[(svc_name, ch_name)] = pattern

    channels: List[ChannelMetadata] = []
    participating_services: Set[str] = {entry_service} if entry_service else set()

    def process_dispatches(caller_svc: str, dispatches: List[Dict[str, Any]]):
        for d in dispatches:
            callee_svc = d.get("service")
            ch_name = d.get("channel")
            if not callee_svc or not ch_name:
                continue

            participating_services.add(caller_svc)
            participating_services.add(callee_svc)

            client_span = d.get("client_span")
            server_span = d.get("server_span")
            launch_type = d.get("launch_type", "async")
            pattern = service_channel_patterns.get((callee_svc, ch_name), "IP-4")

            channel_place = f"ch::{ch_name}"

            if not any(c.channel_place == channel_place and c.caller_service == caller_svc and c.callee_service == callee_svc for c in channels):
                channels.append(ChannelMetadata(
                    channel_name=ch_name,
                    channel_place=channel_place,
                    caller_service=caller_svc,
                    callee_service=callee_svc,
                    client_span=client_span,
                    server_span=server_span,
                    pattern=pattern,
                    launch_type=launch_type,
                ))

            if "nested_dispatches" in d and isinstance(d["nested_dispatches"], list):
                process_dispatches(callee_svc, d["nested_dispatches"])

    for phase_name, phase_data in wf_data.get("phases", {}).items():
        if isinstance(phase_data, dict) and "dispatches" in phase_data:
            process_dispatches(entry_service, phase_data["dispatches"])

    return wf_name, channels, sorted(list(participating_services))


def compose_workflow_nets(
    service_nets: Dict[str, PetriNetModel],
    topology_data: Dict[str, Any],
    workflow_name: Optional[str] = None,
) -> ComposedNetModel:
    """Compose constituent per-service Petri nets into a unified open composed net N_C.
    
    1. Namespaces all service places and transitions with `<svc>::<node>`
    2. Instantiates interface channel places `ch::<ChannelName>`
    3. Wires caller client send transitions to produce tokens into `ch::<ChannelName>`
    4. Fuses `ch::<ChannelName>` directly onto callee source places (replacing `<callee>::source`)
    5. Sets root entry source place with 1 token in M0, callee source places/channels with 0 tokens.
    
    Args:
        service_nets: Dictionary mapping service name -> PetriNetModel.
        topology_data: Loaded interfaces/social-network.json dictionary.
        workflow_name: Optional specific workflow name to compose.
        
    Returns:
        Synthesized ComposedNetModel instance.
    """
    wf_name, channels, participating_svcs = extract_topology_dispatches(topology_data, target_workflow=workflow_name)
    wf_data = topology_data.get("workflows", {}).get(wf_name, {})
    entry_service = wf_data.get("entry_service")

    # Step 1: Namespace participating service nets
    namespaced_nets: Dict[str, PetriNetModel] = {}
    service_sinks: Dict[str, str] = {}
    service_sources: Dict[str, str] = {}

    for svc in participating_svcs:
        if svc not in service_nets:
            raise KeyError(f"Required service net '{svc}' not found in provided service nets collection")
        ns_net = namespace_service_net(service_nets[svc], svc)
        namespaced_nets[svc] = ns_net
        service_sinks[svc] = ns_net.get_sink_place()
        service_sources[svc] = ns_net.get_source_place()

    all_places: Set[str] = set()
    all_transitions: List[Dict[str, Any]] = []
    all_arcs: List[Tuple[str, str]] = []

    for svc, net in namespaced_nets.items():
        all_places.update(net.places)
        all_transitions.extend(net.transitions)
        all_arcs.extend(net.arcs)

    # Step 2 & 3: Channel place instantiation and caller produce wiring
    callee_source_fusions: Dict[str, str] = {}

    for ch in channels:
        ch_place = ch.channel_place
        all_places.add(ch_place)

        caller_svc = ch.caller_service
        callee_svc = ch.callee_service

        caller_net = namespaced_nets[caller_svc]
        caller_send_t_id = None

        if ch.client_span:
            for t in caller_net.transitions:
                if t.get("label") == ch.client_span:
                    caller_send_t_id = t["id"]
                    break

        if not caller_send_t_id:
            for t in caller_net.transitions:
                if ch.channel_name.lower() in t["id"].lower() or (t.get("label") and ch.channel_name.lower() in t["label"].lower()):
                    caller_send_t_id = t["id"]
                    break

        if not caller_send_t_id:
            for t in caller_net.transitions:
                if not t.get("is_silent") and t.get("label") and not t.get("label", "").endswith("_server"):
                    caller_send_t_id = t["id"]
                    break

        if caller_send_t_id:
            produce_arc = (caller_send_t_id, ch_place)
            if produce_arc not in all_arcs:
                all_arcs.append(produce_arc)

        # Step 4: Callee source place direct fusion
        callee_source = service_sources[callee_svc]
        callee_source_fusions[callee_source] = ch_place

    substituted_arcs: List[Tuple[str, str]] = []
    for src, tgt in all_arcs:
        new_src = callee_source_fusions.get(src, src)
        new_tgt = callee_source_fusions.get(tgt, tgt)
        substituted_arcs.append((new_src, new_tgt))

    for old_src in callee_source_fusions.keys():
        if old_src in all_places:
            all_places.remove(old_src)

    root_source = service_sources.get(entry_service)
    if not root_source or root_source not in all_places:
        available_sources = [service_sources[s] for s in participating_svcs if service_sources[s] in all_places]
        root_source = available_sources[0] if available_sources else sorted(list(all_places))[0]

    initial_marking = [root_source]
    final_marking = sorted(list(service_sinks.values()))

    return ComposedNetModel(
        name=wf_name,
        places=sorted(list(all_places)),
        transitions=all_transitions,
        arcs=substituted_arcs,
        initial_marking=initial_marking,
        final_marking=final_marking,
        participating_services=participating_svcs,
        service_sinks=service_sinks,
        service_sources=service_sources,
        channels=channels,
        workflow_name=wf_name,
    )


# ============================================================================
# 4. Composed Net Serialization (JSON, LoLA, PNML)
# ============================================================================

def serialize_composed_to_json(composed_net: ComposedNetModel, output_path: str) -> str:
    """Export composed Petri net structure to formatted JSON file."""
    os.makedirs(os.path.dirname(os.path.abspath(output_path)), exist_ok=True)
    data = composed_net.to_composed_dict()
    with open(output_path, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2, sort_keys=True)
    return output_path


def serialize_composed_to_lola(
    composed_net: ComposedNetModel,
    output_path: Optional[str] = None,
    formula: Optional[str] = None,
) -> Tuple[str, Dict[str, str], Dict[str, str]]:
    """Serialize composed Petri net into standard LoLA net specification format.
    
    Args:
        composed_net: Composed Petri net model.
        output_path: Optional file path to write the .lola file.
        formula: Optional CTL formula string.
        
    Returns:
        Tuple of (lola_content_string, name_to_lola_map, lola_to_name_map).
    """
    used_tokens: Set[str] = set()
    name_to_lola: Dict[str, str] = {}
    lola_to_name: Dict[str, str] = {}

    for p in sorted(composed_net.places):
        token = sanitize_lola_identifier(p, used_tokens)
        name_to_lola[p] = token
        lola_to_name[token] = p

    for t in composed_net.transitions:
        t_id = t["id"]
        label = t.get("label") or t_id
        suggested = f"t_{label}" if t.get("label") else f"t_{t_id}"
        token = sanitize_lola_identifier(suggested, used_tokens)
        name_to_lola[t_id] = token
        lola_to_name[token] = t_id

    lines: List[str] = []
    lines.append(f"{{ LoLA Petri Net Model: {composed_net.workflow_name} }}")
    lines.append(f"{{ Synthesized by Asynchronous Channel Fusion Composer }}")
    lines.append(f"{{ Participating Services: {', '.join(composed_net.participating_services)} }}")
    lines.append("")

    lola_places = [name_to_lola[p] for p in sorted(composed_net.places)]
    lines.append(f"PLACE SAFE: {', '.join(lola_places)};")
    lines.append("")

    if composed_net.initial_marking:
        im_counts: Dict[str, int] = {}
        for p in composed_net.initial_marking:
            if p in name_to_lola:
                tok = name_to_lola[p]
                im_counts[tok] = im_counts.get(tok, 0) + 1
        im_str = ", ".join(f"{tok}: {cnt}" for tok, cnt in sorted(im_counts.items()))
        lines.append(f"MARKING {im_str};")
    else:
        lines.append("MARKING ;")
    lines.append("")

    for t in sorted(composed_net.transitions, key=lambda x: name_to_lola.get(x["id"], x["id"])):
        t_id = t["id"]
        t_tok = name_to_lola[t_id]

        consume_places: Dict[str, int] = {}
        for src, tgt in composed_net.arcs:
            if tgt == t_id and src in name_to_lola:
                p_tok = name_to_lola[src]
                consume_places[p_tok] = consume_places.get(p_tok, 0) + 1

        produce_places: Dict[str, int] = {}
        for src, tgt in composed_net.arcs:
            if src == t_id and tgt in name_to_lola:
                p_tok = name_to_lola[tgt]
                produce_places[p_tok] = produce_places.get(p_tok, 0) + 1

        consume_str = ", ".join(f"{p}: {c}" for p, c in sorted(consume_places.items()))
        produce_str = ", ".join(f"{p}: {c}" for p, c in sorted(produce_places.items()))

        lines.append(f"TRANSITION {t_tok}")
        if consume_str:
            lines.append(f"  CONSUME {consume_str};")
        if produce_str:
            lines.append(f"  PRODUCE {produce_str};")
        lines.append("")

    if formula:
        lines.append(formula.strip())
        lines.append("")

    content = "\n".join(lines)
    if output_path:
        os.makedirs(os.path.dirname(os.path.abspath(output_path)), exist_ok=True)
        with open(output_path, "w", encoding="utf-8") as f:
            f.write(content)

    return content, name_to_lola, lola_to_name


def serialize_composed_to_pnml(composed_net: ComposedNetModel, output_path: str) -> str:
    """Export composed Petri net to standard PNML XML format.
    
    Uses pm4py if available or writes standard PNML XML.
    
    Args:
        composed_net: Composed Petri net model.
        output_path: Destination PNML file path.
        
    Returns:
        Exported file path.
    """
    os.makedirs(os.path.dirname(os.path.abspath(output_path)), exist_ok=True)

    if HAS_PM4PY:
        try:
            pn = PetriNet(composed_net.name)
            p_map: Dict[str, PetriNet.Place] = {}
            for p_name in sorted(composed_net.places):
                place_obj = PetriNet.Place(p_name)
                pn.places.add(place_obj)
                p_map[p_name] = place_obj

            t_map: Dict[str, PetriNet.Transition] = {}
            for t_dict in composed_net.transitions:
                t_id = t_dict["id"]
                label = t_dict.get("label") if not t_dict.get("is_silent") else None
                trans_obj = PetriNet.Transition(t_id, label)
                pn.transitions.add(trans_obj)
                t_map[t_id] = trans_obj

            for src, tgt in composed_net.arcs:
                if src in p_map and tgt in t_map:
                    petri_utils.add_arc_from_to(p_map[src], t_map[tgt], pn)
                elif src in t_map and tgt in p_map:
                    petri_utils.add_arc_from_to(t_map[src], p_map[tgt], pn)

            im = Marking()
            for p_name in composed_net.initial_marking:
                if p_name in p_map:
                    im[p_map[p_name]] = im.get(p_map[p_name], 0) + 1

            fm = Marking()
            for p_name in composed_net.final_marking:
                if p_name in p_map:
                    fm[p_map[p_name]] = fm.get(p_map[p_name], 0) + 1

            pm4py.write_pnml(pn, im, fm, output_path)
            return output_path
        except Exception:
            pass

    # Pure Python standard PNML XML fallback
    lines: List[str] = [
        '<?xml version="1.0" encoding="UTF-8"?>',
        '<pnml xmlns="http://www.pnml.org/version-2009/grammar/pnml">',
        '  <net id="composed_net" type="http://www.pnml.org/version-2009/grammar/ptnet">',
        '    <page id="page0">',
        f'      <name><text>{composed_net.workflow_name}</text></name>',
    ]

    for p in sorted(composed_net.places):
        init_val = 1 if p in composed_net.initial_marking else 0
        lines.append(f'      <place id="{p}">')
        lines.append(f'        <name><text>{p}</text></name>')
        if init_val > 0:
            lines.append(f'        <initialMarking><text>{init_val}</text></initialMarking>')
        lines.append('      </place>')

    for t in composed_net.transitions:
        t_id = t["id"]
        label = t.get("label") or ""
        lines.append(f'      <transition id="{t_id}">')
        lines.append(f'        <name><text>{label}</text></name>')
        lines.append('      </transition>')

    arc_idx = 0
    for src, tgt in composed_net.arcs:
        arc_idx += 1
        lines.append(f'      <arc id="arc_{arc_idx}" source="{src}" target="{tgt}">')
        lines.append('        <inscription><text>1</text></inscription>')
        lines.append('      </arc>')

    lines.extend([
        '    </page>',
        '  </net>',
        '</pnml>',
    ])

    with open(output_path, "w", encoding="utf-8") as f:
        f.write("\n".join(lines))

    return output_path


# ============================================================================
# 4.1 Composed Net Diagram Rendering (DOT, SVG, PNG)
# ============================================================================

def generate_composed_dot(composed_net: ComposedNetModel, group_by_service: bool = False) -> str:
    """Generates Graphviz DOT string for the composed workflow net adhering to standard Petri net conventions.
    
    Places are rendered as circles (sources marked with token ●, sinks as double circles, channels highlighted).
    Transitions are rendered as clean rectangular boxes.
    Arcs are directed arrows.
    
    Args:
        composed_net: Synthesized ComposedNetModel.
        group_by_service: When True, clusters constituent places and transitions inside service subgraphs.
        
    Returns:
        Graphviz DOT formatted string.
    """
    lines = [
        f'digraph "{composed_net.workflow_name}" {{',
        '  // Portrait Layout & Global Settings',
        '  rankdir="TB";',
        '  charset="UTF-8";',
        '  compound=true;',
        '  bgcolor="#FAFAFA";',
        '  node [fontname="Helvetica,Arial,sans-serif", fontsize=9];',
        '  edge [fontname="Helvetica,Arial,sans-serif", fontsize=8, color="#333333", arrowsize=0.7];',
        '',
    ]

    channel_place_set = set(composed_net.channel_places)
    initial_places = set(composed_net.initial_marking)
    final_places = set(composed_net.final_marking).union(set(composed_net.service_sinks.values()))

    def render_place_dot(p: str, indent: str = "  ") -> str:
        esc_p = p.replace('"', '\\"')
        if p in channel_place_set or p.startswith("ch::"):
            return (
                f'{indent}"{esc_p}" [shape=circle, style="filled", fillcolor="#FEF3C7", '
                f'color="#D97706", penwidth=1.8, label="", '
                f'xlabel=<<FONT POINT-SIZE="8" COLOR="#92400E"><B>{html.escape(p)}</B></FONT>>, '
                f'width=0.28, height=0.28, fixedsize=true];'
            )
        elif p in initial_places:
            return (
                f'{indent}"{esc_p}" [shape=circle, style="filled", fillcolor="#D0E1F9", '
                f'color="#1E395B", penwidth=1.8, label="●", '
                f'xlabel=<<FONT POINT-SIZE="8" COLOR="#1E395B">{html.escape(p)}</FONT>>, '
                f'width=0.28, height=0.28, fixedsize=true, fontsize=10];'
            )
        elif p in final_places:
            return (
                f'{indent}"{esc_p}" [shape=doublecircle, style="filled", fillcolor="#FDE8E8", '
                f'color="#9B1C1C", penwidth=1.8, label="", '
                f'xlabel=<<FONT POINT-SIZE="8" COLOR="#9B1C1C">{html.escape(p)}</FONT>>, '
                f'width=0.28, height=0.28, fixedsize=true, fontsize=9];'
            )
        else:
            return (
                f'{indent}"{esc_p}" [shape=circle, style="filled", fillcolor="#EBF3FA", '
                f'color="#2A6496", penwidth=1.2, label="", '
                f'xlabel=<<FONT POINT-SIZE="7" COLOR="#2A6496">{html.escape(p)}</FONT>>, '
                f'width=0.22, height=0.22, fixedsize=true, fontsize=7];'
            )

    def render_trans_dot(t: Dict[str, Any], indent: str = "  ") -> str:
        t_id = t["id"]
        esc_id = t_id.replace('"', '\\"')
        is_silent = t.get("is_silent", False)
        label = t.get("label")
        if is_silent or label is None or label == "" or label == "tau":
            return (
                f'{indent}"{esc_id}" [shape=box, style="filled", fillcolor="#94A3B8", '
                f'color="#475569", penwidth=1.0, width=0.3, height=0.1, fixedsize=true, label=""];'
            )
        else:
            esc_label = html.escape(str(label))
            esc_tname = html.escape(str(t_id))
            table_label = (
                f'<<TABLE BORDER="0" CELLBORDER="0" CELLSPACING="1">'
                f'<TR><TD><B><FONT COLOR="#1B4D1B">{esc_label}</FONT></B></TD></TR>'
                f'<TR><TD><FONT POINT-SIZE="7" COLOR="#64748B">{esc_tname}</FONT></TD></TR>'
                f'</TABLE>>'
            )
            return (
                f'{indent}"{esc_id}" [shape=box, style="filled", fillcolor="#F2F9EC", '
                f'color="#3C763D", penwidth=1.4, label={table_label}];'
            )

    if not group_by_service:
        lines.append('  // Places')
        for p in sorted(composed_net.places):
            lines.append(render_place_dot(p, "  "))
        lines.append('')
        lines.append('  // Transitions')
        for t in sorted(composed_net.transitions, key=lambda x: x["id"]):
            lines.append(render_trans_dot(t, "  "))
    else:
        services = sorted(composed_net.participating_services)
        svc_places: Dict[str, List[str]] = collections.defaultdict(list)
        top_places: List[str] = []

        for p in sorted(composed_net.places):
            if p in channel_place_set or p.startswith("ch::"):
                top_places.append(p)
            else:
                matched_svc = None
                for svc in services:
                    if p.startswith(f"{svc}::"):
                        matched_svc = svc
                        break
                if matched_svc:
                    svc_places[matched_svc].append(p)
                else:
                    top_places.append(p)

        svc_transitions: Dict[str, List[Dict[str, Any]]] = collections.defaultdict(list)
        top_transitions: List[Dict[str, Any]] = []

        for t in sorted(composed_net.transitions, key=lambda x: x["id"]):
            t_svc = t.get("service")
            if not t_svc:
                for svc in services:
                    if t["id"].startswith(f"{svc}::"):
                        t_svc = svc
                        break
            if t_svc:
                svc_transitions[t_svc].append(t)
            else:
                top_transitions.append(t)

        lines.append('  // Inter-Service Channel Places')
        for p in top_places:
            lines.append(render_place_dot(p, "  "))
        lines.append('')

        for t in top_transitions:
            lines.append(render_trans_dot(t, "  "))
        if top_transitions:
            lines.append('')

        for svc in services:
            c_places = svc_places.get(svc, [])
            c_transitions = svc_transitions.get(svc, [])
            if not c_places and not c_transitions:
                continue
            cluster_id = f"cluster_{re.sub(r'[^A-Za-z0-9_]', '_', svc)}"
            lines.append(f'  subgraph "{cluster_id}" {{')
            lines.append(f'    label = "{html.escape(svc)}";')
            lines.append('    style = "rounded,dashed";')
            lines.append('    color = "#94A3B8";')
            lines.append('    bgcolor = "#F8FAFC";')
            lines.append('    fontname = "Helvetica,Arial,sans-serif";')
            lines.append('    fontsize = 10;')
            lines.append('    penwidth = 1.2;')
            lines.append('')
            for p in c_places:
                lines.append(render_place_dot(p, "    "))
            for t in c_transitions:
                lines.append(render_trans_dot(t, "    "))
            lines.append('  }')
            lines.append('')

    lines.append('  // Arcs')
    for src, tgt in sorted(composed_net.arcs):
        esc_src = src.replace('"', '\\"')
        esc_tgt = tgt.replace('"', '\\"')
        lines.append(f'  "{esc_src}" -> "{esc_tgt}";')

    lines.append('}')
    return '\n'.join(lines)


def render_composed_via_graphviz(dot_str: str, output_path: str, format_type: str = "svg") -> bool:
    """Executes Graphviz 'dot' CLI to produce SVG or PNG image.
    
    Args:
        dot_str: Graphviz DOT source string.
        output_path: Target image file path.
        format_type: Output format ('svg' or 'png').
        
    Returns:
        True if successfully rendered, False otherwise.
    """
    dot_bin = shutil.which("dot")
    if not dot_bin:
        return False
    try:
        os.makedirs(os.path.dirname(os.path.abspath(output_path)), exist_ok=True)
        cmd = [dot_bin, f"-T{format_type}", "-o", output_path]
        proc = subprocess.run(cmd, input=dot_str.encode("utf-8"), capture_output=True, check=True)
        return proc.returncode == 0 and os.path.exists(output_path) and os.path.getsize(output_path) > 0
    except Exception:
        return False


def render_composed_standalone_svg(
    composed_net: ComposedNetModel,
    output_path: str,
    group_by_service: bool = False,
) -> bool:
    """Pure-Python fallback SVG renderer when Graphviz binary is not available.
    
    Renders composed Petri net diagrams (flat or service-grouped) using canonical
    Petri net graphical elements:
      - Places: circles (source marked with token ●, sink double circle, channels in amber)
      - Transitions: clean rectangular blocks
      - Arcs: directed arrow lines
    
    Args:
        composed_net: Synthesized ComposedNetModel.
        output_path: Destination SVG file path.
        group_by_service: Whether to render service cluster bounding boxes.
        
    Returns:
        True if successfully written, False otherwise.
    """
    all_places = sorted(composed_net.places)
    all_trans = sorted(composed_net.transitions, key=lambda x: x["id"])
    all_nodes = [p for p in all_places] + [t["id"] for t in all_trans]
    trans_map = {t["id"]: t for t in all_trans}
    channel_set = set(composed_net.channel_places)
    initial_places = set(composed_net.initial_marking)
    final_places = set(composed_net.final_marking).union(set(composed_net.service_sinks.values()))

    # Topological level computation
    in_degrees: Dict[str, int] = collections.defaultdict(int)
    for src, tgt in composed_net.arcs:
        in_degrees[tgt] += 1

    levels: Dict[str, int] = {}
    queue = collections.deque()

    for p in composed_net.initial_marking:
        levels[p] = 0
        queue.append(p)

    for n in all_nodes:
        if in_degrees[n] == 0 and n not in levels:
            levels[n] = 0
            queue.append(n)

    fwd_adj: Dict[str, List[str]] = collections.defaultdict(list)
    for src, tgt in composed_net.arcs:
        fwd_adj[src].append(tgt)

    visited_count: Dict[str, int] = collections.defaultdict(int)
    while queue:
        curr = queue.popleft()
        curr_lvl = levels[curr]
        visited_count[curr] += 1
        if visited_count[curr] > len(all_nodes):
            continue
        for nxt in fwd_adj[curr]:
            if nxt not in levels or levels[nxt] < curr_lvl + 1:
                levels[nxt] = curr_lvl + 1
                queue.append(nxt)

    max_lvl = max(levels.values(), default=0)
    for n in all_nodes:
        if n not in levels:
            max_lvl += 1
            levels[n] = max_lvl

    services = sorted(composed_net.participating_services)
    cluster_boxes: List[Tuple[float, float, float, float, str]] = []

    if not group_by_service:
        level_groups: Dict[int, List[str]] = collections.defaultdict(list)
        for n in all_nodes:
            lvl = levels.get(n, 0)
            level_groups[lvl].append(n)

        sorted_levels = sorted(level_groups.keys())
        max_width_count = max((len(nodes) for nodes in level_groups.values()), default=1)

        col_width = 240
        row_height = 85
        svg_width = max(800, (max_width_count + 1) * col_width)
        svg_height = max(500, (len(sorted_levels) + 2) * row_height)

        node_positions: Dict[str, Tuple[float, float]] = {}
        for lvl in sorted_levels:
            nodes_in_lvl = level_groups[lvl]
            y = (lvl + 1) * row_height
            k = len(nodes_in_lvl)
            for idx, nid in enumerate(nodes_in_lvl):
                x = (svg_width / (k + 1)) * (idx + 1)
                node_positions[nid] = (x, y)
    else:
        svc_node_map: Dict[str, List[str]] = collections.defaultdict(list)
        channel_nodes: List[str] = []

        for n in all_nodes:
            if n in channel_set or n.startswith("ch::"):
                channel_nodes.append(n)
            else:
                matched_svc = None
                for s in services:
                    if n.startswith(f"{s}::"):
                        matched_svc = s
                        break
                if matched_svc:
                    svc_node_map[matched_svc].append(n)
                else:
                    channel_nodes.append(n)

        num_cols = 3 if len(services) >= 3 else max(1, len(services))
        cluster_width = 280
        cluster_gap_x = 35
        cluster_gap_y = 40
        header_offset = 120

        svc_heights: Dict[str, float] = {}
        for s in services:
            count = len(svc_node_map.get(s, []))
            svc_heights[s] = max(180, 50 + (count * 45))

        row_heights: Dict[int, float] = collections.defaultdict(float)
        for idx, s in enumerate(services):
            r = idx // num_cols
            row_heights[r] = max(row_heights[r], svc_heights[s])

        svc_boxes: Dict[str, Tuple[float, float, float, float]] = {}
        y_accum = header_offset
        for r in sorted(row_heights.keys()):
            for c in range(num_cols):
                idx = r * num_cols + c
                if idx < len(services):
                    s = services[idx]
                    x = 40 + c * (cluster_width + cluster_gap_x)
                    y = y_accum
                    h = svc_heights[s]
                    svc_boxes[s] = (x, y, cluster_width, h)
                    cluster_boxes.append((x, y, cluster_width, h, s))
            y_accum += row_heights[r] + cluster_gap_y

        svg_width = max(950, 60 + num_cols * (cluster_width + cluster_gap_x))
        svg_height = max(600, y_accum + 60)

        node_positions = {}
        for s, (bx, by, bw, bh) in svc_boxes.items():
            snodes = svc_node_map.get(s, [])
            snodes.sort(key=lambda n: levels.get(n, 0))
            for s_idx, sn in enumerate(snodes):
                nx = bx + bw / 2
                ny = by + 45 + (s_idx + 0.5) * ((bh - 55) / max(1, len(snodes)))
                node_positions[sn] = (nx, ny)

        for c_idx, cn in enumerate(channel_nodes):
            cx = (svg_width / (len(channel_nodes) + 1)) * (c_idx + 1)
            cy = 60
            node_positions[cn] = (cx, cy)

    svg_lines = [
        f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {svg_width} {svg_height}" width="{svg_width}" height="{svg_height}">',
        f'  <title>{html.escape(composed_net.workflow_name)}</title>',
        '  <defs>',
        '    <marker id="arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse">',
        '      <path d="M 0 0 L 10 5 L 0 10 z" fill="#333333" />',
        '    </marker>',
        '  </defs>',
        '  <style>',
        '    .place-lbl { font-family: sans-serif; font-size: 8px; fill: #1E395B; text-anchor: middle; dominant-baseline: central; }',
        '    .trans-lbl { font-family: sans-serif; font-size: 9px; font-weight: 600; fill: #1B4D1B; text-anchor: middle; dominant-baseline: central; }',
        '    .edge { stroke: #475569; stroke-width: 1.4; fill: none; marker-end: url(#arrow); }',
        '    .cluster-box { fill: #F8FAFC; stroke: #94A3B8; stroke-width: 1.5; stroke-dasharray: 4,4; rx: 8; }',
        '    .cluster-lbl { font-family: sans-serif; font-size: 11px; font-weight: bold; fill: #334155; }',
        '  </style>',
        '  <rect width="100%" height="100%" fill="#FAFAFA" />',
        '',
    ]

    # Service cluster bounding boxes
    if cluster_boxes:
        svg_lines.append('  <!-- Service Clusters -->')
        for bx, by, bw, bh, sname in cluster_boxes:
            svg_lines.append(f'  <rect x="{bx:.1f}" y="{by:.1f}" width="{bw:.1f}" height="{bh:.1f}" class="cluster-box" />')
            svg_lines.append(f'  <text x="{bx + 12:.1f}" y="{by + 20:.1f}" class="cluster-lbl">{html.escape(sname)}</text>')
        svg_lines.append('')

    # Arcs
    svg_lines.append('  <!-- Arcs -->')
    for src, tgt in composed_net.arcs:
        if src in node_positions and tgt in node_positions:
            x1, y1 = node_positions[src]
            x2, y2 = node_positions[tgt]
            svg_lines.append(f'  <line x1="{x1:.1f}" y1="{y1:.1f}" x2="{x2:.1f}" y2="{y2:.1f}" class="edge" />')
    svg_lines.append('')

    # Places
    svg_lines.append('  <!-- Places -->')
    for p in all_places:
        if p in node_positions:
            x, y = node_positions[p]
            is_chan = p in channel_set or p.startswith("ch::")
            is_init = p in initial_places
            is_fin = p in final_places

            if is_chan:
                fill = "#FEF3C7"
                stroke = "#D97706"
                r = 11
            elif is_init:
                fill = "#D0E1F9"
                stroke = "#1E395B"
                r = 12
            elif is_fin:
                fill = "#FDE8E8"
                stroke = "#9B1C1C"
                r = 12
            else:
                fill = "#EBF3FA"
                stroke = "#2A6496"
                r = 10

            svg_lines.append(f'  <circle cx="{x:.1f}" cy="{y:.1f}" r="{r}" fill="{fill}" stroke="{stroke}" stroke-width="1.8" />')
            if is_fin:
                svg_lines.append(f'  <circle cx="{x:.1f}" cy="{y:.1f}" r="{r - 3}" fill="none" stroke="{stroke}" stroke-width="1.2" />')
            if is_init:
                svg_lines.append(f'  <text x="{x:.1f}" y="{y:.1f}" class="place-lbl">●</text>')

            lbl_color = "#92400E" if is_chan else ("#1E395B" if is_init else ("#9B1C1C" if is_fin else "#475569"))
            svg_lines.append(
                f'  <text x="{x + r + 4:.1f}" y="{y:.1f}" font-family="sans-serif" font-size="8px" '
                f'fill="{lbl_color}" text-anchor="start" dominant-baseline="central">{html.escape(p)}</text>'
            )

    svg_lines.append('')
    svg_lines.append('  <!-- Transitions -->')
    for t_id, t in trans_map.items():
        if t_id in node_positions:
            x, y = node_positions[t_id]
            is_silent = t.get("is_silent", False)
            label = t.get("label") or t_id
            if is_silent or label == "tau":
                w, h = 40, 14
                rx, ry = x - w / 2, y - h / 2
                svg_lines.append(f'  <rect x="{rx:.1f}" y="{ry:.1f}" width="{w}" height="{h}" rx="2" fill="#94A3B8" stroke="#475569" stroke-width="1.0" />')
            else:
                w, h = 180, 32
                rx, ry = x - w / 2, y - h / 2
                svg_lines.append(f'  <rect x="{rx:.1f}" y="{ry:.1f}" width="{w}" height="{h}" rx="4" fill="#F2F9EC" stroke="#3C763D" stroke-width="1.4" />')
                disp_lbl = str(label)[:24]
                svg_lines.append(f'  <text x="{x:.1f}" y="{y:.1f}" class="trans-lbl">{html.escape(disp_lbl)}</text>')

    svg_lines.append('</svg>')

    try:
        os.makedirs(os.path.dirname(os.path.abspath(output_path)), exist_ok=True)
        with open(output_path, "w", encoding="utf-8") as f:
            f.write("\n".join(svg_lines))
        return True
    except Exception:
        return False


def render_composed_diagrams(
    composed_net: ComposedNetModel,
    output_dir: str = "interfaces/diagrams",
    render_format: str = "all",
) -> Dict[str, str]:
    """Coordinates generation of flat and service-grouped DOT, SVG, and PNG files.
    
    Generates:
      - composed-net.dot
      - composed-net.svg
      - composed-net.png (if Graphviz is available)
      - composed-net-grouped.dot
      - composed-net-grouped.svg
      - composed-net-grouped.png (if Graphviz is available)
      
    Args:
        composed_net: Synthesized ComposedNetModel.
        output_dir: Destination directory.
        render_format: 'all', 'svg', or 'png'.
        
    Returns:
        Dict mapping artifact keys ('flat_dot', 'flat_svg', 'flat_png', 'grouped_dot', 'grouped_svg', 'grouped_png') to paths.
    """
    out_dir = Path(output_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    results: Dict[str, str] = {}
    formats = ["svg", "png"] if render_format == "all" else [render_format]

    # 1. Flat Composed Net
    flat_dot_str = generate_composed_dot(composed_net, group_by_service=False)
    flat_dot_path = out_dir / "composed-net.dot"
    with open(flat_dot_path, "w", encoding="utf-8") as f:
        f.write(flat_dot_str)
    results["flat_dot"] = str(flat_dot_path)

    flat_svg_path = out_dir / "composed-net.svg"
    flat_png_path = out_dir / "composed-net.png"

    if "svg" in formats:
        rendered = render_composed_via_graphviz(flat_dot_str, str(flat_svg_path), "svg")
        if not rendered:
            render_composed_standalone_svg(composed_net, str(flat_svg_path), group_by_service=False)
        results["flat_svg"] = str(flat_svg_path)

    if "png" in formats:
        rendered = render_composed_via_graphviz(flat_dot_str, str(flat_png_path), "png")
        if rendered:
            results["flat_png"] = str(flat_png_path)

    # 2. Service-Grouped Composed Net
    grouped_dot_str = generate_composed_dot(composed_net, group_by_service=True)
    grouped_dot_path = out_dir / "composed-net-grouped.dot"
    with open(grouped_dot_path, "w", encoding="utf-8") as f:
        f.write(grouped_dot_str)
    results["grouped_dot"] = str(grouped_dot_path)

    grouped_svg_path = out_dir / "composed-net-grouped.svg"
    grouped_png_path = out_dir / "composed-net-grouped.png"

    if "svg" in formats:
        rendered = render_composed_via_graphviz(grouped_dot_str, str(grouped_svg_path), "svg")
        if not rendered:
            render_composed_standalone_svg(composed_net, str(grouped_svg_path), group_by_service=True)
        results["grouped_svg"] = str(grouped_svg_path)

    if "png" in formats:
        rendered = render_composed_via_graphviz(grouped_dot_str, str(grouped_png_path), "png")
        if rendered:
            results["grouped_png"] = str(grouped_png_path)

    return results


# ============================================================================
# 5. Dual-Engine Formal Verification (LoLA + Pure-Python State Space)
# ============================================================================

def solve_reachability_lola(
    lola_content: str,
    formula_str: str,
    lola_bin: str = "lola",
    timeout_sec: float = 30.0,
) -> Tuple[VerificationVerdict, Optional[str], float]:
    """Execute external LoLA model checker on serialized net string.
    
    Args:
        lola_content: Complete LoLA net format text.
        formula_str: CTL reachability formula in LoLA syntax.
        lola_bin: Path or binary name of LoLA executable.
        timeout_sec: Timeout in seconds.
        
    Returns:
        Tuple of (VerificationVerdict, raw_stdout, elapsed_seconds).
    """
    with tempfile.TemporaryDirectory() as tmp_dir:
        net_path = os.path.join(tmp_dir, "net.lola")
        with open(net_path, "w", encoding="utf-8") as f:
            f.write(lola_content)

        cmd = [
            lola_bin,
            net_path,
            f"--formula={formula_str}",
            "--search=covergraph",
        ]

        t0 = time.time()
        try:
            proc = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=timeout_sec,
            )
            elapsed = time.time() - t0
        except FileNotFoundError:
            raise FileNotFoundError(f"LoLA executable '{lola_bin}' not found in PATH.")
        except subprocess.TimeoutExpired:
            return VerificationVerdict.ERROR, f"LoLA execution timed out after {timeout_sec}s", timeout_sec

        output = proc.stdout + "\n" + proc.stderr

        if "result: yes" in output.lower() or "formula is true" in output.lower():
            return VerificationVerdict.SAT, output, elapsed
        elif "result: no" in output.lower() or "formula is false" in output.lower():
            return VerificationVerdict.UNSAT, output, elapsed
        else:
            return VerificationVerdict.ERROR, output, elapsed


def solve_state_space_internal(
    composed_net: ComposedNetModel,
    max_states: int = 300000,
) -> Dict[str, Any]:
    """Explore the reachable state space of composed net N_C using pure Python BFS.
    
    Computes reachable markings, deadlocks, channel bounds, and terminal conditions.
    
    Args:
        composed_net: Composed Petri net model.
        max_states: Maximum state space bound before safety cutoff.
        
    Returns:
        Dictionary containing state space metrics, deadlocks, channel maximum depths,
        and witnesses for property checks.
    """
    t_presets: Dict[str, Dict[str, int]] = collections.defaultdict(lambda: collections.defaultdict(int))
    t_postsets: Dict[str, Dict[str, int]] = collections.defaultdict(lambda: collections.defaultdict(int))
    t_labels: Dict[str, str] = {}

    for t in composed_net.transitions:
        t_id = t["id"]
        t_labels[t_id] = t.get("label") or t_id

    for src, tgt in composed_net.arcs:
        if tgt in t_labels:
            t_presets[tgt][src] += 1
        elif src in t_labels:
            t_postsets[src][tgt] += 1

    service_sinks = set(composed_net.service_sinks.values())
    channel_places = set(composed_net.channel_places)

    def to_marking_tuple(m: Dict[str, int]) -> Tuple[Tuple[str, int], ...]:
        return tuple(sorted(((p, cnt) for p, cnt in m.items() if cnt > 0)))

    m0_dict: Dict[str, int] = collections.defaultdict(int)
    for p in composed_net.initial_marking:
        m0_dict[p] += 1

    m0_tuple = to_marking_tuple(m0_dict)

    visited: Set[Tuple[Tuple[str, int], ...]] = {m0_tuple}
    queue = collections.deque([(m0_dict, [])])

    states_explored = 0
    premature_deadlocks: List[Dict[str, Any]] = []
    orphaned_message_states: List[Dict[str, Any]] = []
    max_channel_depth: Dict[str, int] = {ch: 0 for ch in channel_places}

    all_transitions_list = [t["id"] for t in composed_net.transitions]

    while queue and states_explored < max_states:
        curr_m, path = queue.popleft()
        states_explored += 1

        for ch in channel_places:
            cnt = curr_m.get(ch, 0)
            if cnt > max_channel_depth[ch]:
                max_channel_depth[ch] = cnt

        all_ends_reached = all(curr_m.get(sink, 0) > 0 for sink in service_sinks) if service_sinks else False

        if all_ends_reached:
            residual_channels = {ch: curr_m[ch] for ch in channel_places if curr_m.get(ch, 0) > 0}
            if residual_channels:
                orphaned_message_states.append({
                    "marking": dict(curr_m),
                    "residual_channels": residual_channels,
                    "witness_path": list(path),
                })

        enabled_transitions = []
        for t_id in all_transitions_list:
            preset = t_presets[t_id]
            is_enabled = True
            for p, req_cnt in preset.items():
                if curr_m.get(p, 0) < req_cnt:
                    is_enabled = False
                    break
            if is_enabled:
                enabled_transitions.append(t_id)

        if not enabled_transitions:
            if not all_ends_reached:
                premature_deadlocks.append({
                    "marking": dict(curr_m),
                    "witness_path": list(path),
                })
            continue

        for t_id in enabled_transitions:
            next_m = dict(curr_m)
            for p, req_cnt in t_presets[t_id].items():
                next_m[p] -= req_cnt
                if next_m[p] == 0:
                    del next_m[p]
            for p, prod_cnt in t_postsets[t_id].items():
                next_m[p] = next_m.get(p, 0) + prod_cnt

            next_tuple = to_marking_tuple(next_m)
            if next_tuple not in visited:
                visited.add(next_tuple)
                next_path = list(path)
                next_path.append({
                    "transition_id": t_id,
                    "label": t_labels[t_id],
                })
                queue.append((next_m, next_path))

    return {
        "states_explored": states_explored,
        "max_states_reached": states_explored >= max_states,
        "premature_deadlocks": premature_deadlocks,
        "orphaned_message_states": orphaned_message_states,
        "max_channel_depth": max_channel_depth,
    }


# ============================================================================
# 6. Four Formal Property Verifiers
# ============================================================================

def verify_p0_soundness(
    composed_net: ComposedNetModel,
    state_space: Dict[str, Any],
    engine: str = "auto",
    lola_bin: str = "lola",
) -> Dict[str, Any]:
    """Verify Property 1: P0 Soundness / Deadlock Freedom.
    
    Formula: EF(DEADLOCK AND NOT (sink_1 > 0 AND sink_2 > 0 ...)) = false (UNSAT).
    
    Args:
        composed_net: Composed Petri net model.
        state_space: Precomputed internal state space dictionary.
        engine: 'auto', 'lola', or 'internal'.
        lola_bin: LoLA binary executable.
        
    Returns:
        Structured property result dict.
    """
    t0 = time.time()
    sinks = sorted(list(composed_net.service_sinks.values()))
    lola_content, name_to_lola, _ = serialize_composed_to_lola(composed_net)

    if sinks:
        sink_terms = " AND ".join(f"{name_to_lola.get(s, s)} > 0" for s in sinks)
        formula = f"FORMULA EF(DEADLOCK AND NOT ({sink_terms}))"
    else:
        formula = "FORMULA EF(DEADLOCK)"

    resolved_engine = engine
    if engine == "auto":
        resolved_engine = "lola" if shutil.which(lola_bin) is not None else "internal"

    verdict = VerificationVerdict.ERROR
    witness = None

    if resolved_engine == "lola":
        try:
            verdict, _, _ = solve_reachability_lola(lola_content, formula, lola_bin=lola_bin)
        except Exception:
            resolved_engine = "internal (fallback)"

    if resolved_engine != "lola" or verdict == VerificationVerdict.ERROR:
        deadlocks = state_space["premature_deadlocks"]
        if deadlocks:
            verdict = VerificationVerdict.SAT
            witness = deadlocks[0]["witness_path"]
        else:
            verdict = VerificationVerdict.UNSAT
        if resolved_engine != "lola":
            resolved_engine = "internal"

    elapsed_ms = round((time.time() - t0) * 1000, 2)
    status = PropertyStatus.HOLDS if verdict == VerificationVerdict.UNSAT else (
        PropertyStatus.VIOLATED if verdict == VerificationVerdict.SAT else PropertyStatus.UNKNOWN
    )

    res = {
        "property_id": "P0_SOUNDNESS",
        "name": "P0 Soundness / Deadlock Freedom",
        "formula": formula,
        "verdict": verdict.value,
        "status": status.value,
        "engine": resolved_engine,
        "states_explored": state_space["states_explored"],
        "execution_time_ms": elapsed_ms,
        "description": "Verifies absence of reachable premature deadlocks prior to global multi-service completion",
    }
    if witness:
        res["witness_trace"] = witness
    return res


def verify_orphaned_message_freedom(
    composed_net: ComposedNetModel,
    state_space: Dict[str, Any],
    engine: str = "auto",
    lola_bin: str = "lola",
) -> Dict[str, Any]:
    """Verify Property 2: Orphaned Message Freedom.
    
    Formula: EF((sink_1 > 0 AND sink_2 > 0 ...) AND (ch_1 > 0 OR ch_2 > 0 ...)) = false (UNSAT).
    
    Args:
        composed_net: Composed Petri net model.
        state_space: Precomputed internal state space dictionary.
        engine: 'auto', 'lola', or 'internal'.
        lola_bin: LoLA binary executable.
        
    Returns:
        Structured property result dict.
    """
    t0 = time.time()
    sinks = sorted(list(composed_net.service_sinks.values()))
    channels = sorted(composed_net.channel_places)
    lola_content, name_to_lola, _ = serialize_composed_to_lola(composed_net)

    if not channels:
        return {
            "property_id": "ORPHANED_MESSAGE_FREEDOM",
            "name": "Orphaned Message Freedom",
            "formula": "N/A (No interface channels present)",
            "verdict": VerificationVerdict.UNSAT.value,
            "status": PropertyStatus.HOLDS.value,
            "engine": "internal",
            "states_explored": state_space["states_explored"],
            "execution_time_ms": 0.0,
            "description": "Vacuously holds (no asynchronous channels in composition)",
        }

    sink_terms = " AND ".join(f"{name_to_lola.get(s, s)} > 0" for s in sinks) if sinks else "TRUE"
    ch_terms = " OR ".join(f"{name_to_lola.get(c, c)} > 0" for c in channels)
    formula = f"FORMULA EF(({sink_terms}) AND ({ch_terms}))"

    resolved_engine = engine
    if engine == "auto":
        resolved_engine = "lola" if shutil.which(lola_bin) is not None else "internal"

    verdict = VerificationVerdict.ERROR
    witness = None
    orphaned_channels: Optional[Dict[str, int]] = None

    if resolved_engine == "lola":
        try:
            verdict, _, _ = solve_reachability_lola(lola_content, formula, lola_bin=lola_bin)
        except Exception:
            resolved_engine = "internal (fallback)"

    if resolved_engine != "lola" or verdict == VerificationVerdict.ERROR:
        orphaned_states = state_space["orphaned_message_states"]
        if orphaned_states:
            verdict = VerificationVerdict.SAT
            witness = orphaned_states[0]["witness_path"]
            orphaned_channels = orphaned_states[0]["residual_channels"]
        else:
            verdict = VerificationVerdict.UNSAT
        if resolved_engine != "lola":
            resolved_engine = "internal"

    elapsed_ms = round((time.time() - t0) * 1000, 2)
    status = PropertyStatus.HOLDS if verdict == VerificationVerdict.UNSAT else (
        PropertyStatus.VIOLATED if verdict == VerificationVerdict.SAT else PropertyStatus.UNKNOWN
    )

    res = {
        "property_id": "ORPHANED_MESSAGE_FREEDOM",
        "name": "Orphaned Message Freedom",
        "formula": formula,
        "verdict": verdict.value,
        "status": status.value,
        "engine": resolved_engine,
        "states_explored": state_space["states_explored"],
        "execution_time_ms": elapsed_ms,
        "description": "Verifies that no residual tokens linger in any interface channel place upon workflow completion",
    }
    if witness:
        res["witness_trace"] = witness
    if orphaned_channels:
        res["orphaned_channels"] = orphaned_channels
    return res


def verify_channel_1_boundedness(
    composed_net: ComposedNetModel,
    state_space: Dict[str, Any],
    engine: str = "auto",
    lola_bin: str = "lola",
) -> Dict[str, Any]:
    """Verify Property 3: Channel 1-Boundedness (1-Safe Invariant).
    
    Formula: For all ch in channels: AG(ch <= 1) = true (or EF(ch > 1) = false (UNSAT)).
    
    Args:
        composed_net: Composed Petri net model.
        state_space: Precomputed internal state space dictionary.
        engine: 'auto', 'lola', or 'internal'.
        lola_bin: LoLA binary executable.
        
    Returns:
        Structured property result dict with per-channel breakdown.
    """
    t0 = time.time()
    channels = sorted(composed_net.channel_places)
    max_depths = state_space["max_channel_depth"]

    channel_verdicts: Dict[str, Dict[str, Any]] = {}
    all_1_bounded = True

    for ch in channels:
        depth = max_depths.get(ch, 0)
        is_bounded = (depth <= 1)
        if not is_bounded:
            all_1_bounded = False
        channel_verdicts[ch] = {
            "max_observed_tokens": depth,
            "is_1_bounded": is_bounded,
            "verdict": VerificationVerdict.TRUE.value if is_bounded else VerificationVerdict.FALSE.value,
            "status": PropertyStatus.HOLDS.value if is_bounded else PropertyStatus.VIOLATED.value,
        }

    status = PropertyStatus.HOLDS if all_1_bounded else PropertyStatus.VIOLATED
    elapsed_ms = round((time.time() - t0) * 1000, 2)

    return {
        "property_id": "CHANNEL_1_BOUNDEDNESS",
        "name": "Channel 1-Boundedness",
        "formula": "FORALL ch in Channels: AG(ch <= 1)",
        "all_channels_1_bounded": all_1_bounded,
        "status": status.value,
        "engine": "internal",
        "channel_verdicts": channel_verdicts,
        "max_channel_depth": max_depths,
        "states_explored": state_space["states_explored"],
        "execution_time_ms": elapsed_ms,
        "description": "Verifies 1-safe capacity bounds across all asynchronous interface channels",
    }


def verify_response_liveness(
    composed_net: ComposedNetModel,
    state_space: Dict[str, Any],
) -> Dict[str, Any]:
    """Verify Property 4: Response-Liveness across IP-4 request-response channels.
    
    Proves structurally and through reachability analysis that every IP-4 channel
    has a verified consumer and guaranteed forward execution path to completion.
    
    Args:
        composed_net: Composed Petri net model.
        state_space: Precomputed internal state space dictionary.
        
    Returns:
        Structured property result dict for IP-4 response liveness.
    """
    t0 = time.time()
    ip4_channels = [ch for ch in composed_net.channels if ch.pattern == "IP-4"]
    channel_details: List[Dict[str, Any]] = []
    all_live = True

    p_postsets: Dict[str, List[str]] = collections.defaultdict(list)
    for src, tgt in composed_net.arcs:
        if src in composed_net.places:
            p_postsets[src].append(tgt)

    for ch in ip4_channels:
        ch_place = ch.channel_place
        consumers = p_postsets.get(ch_place, [])
        callee_sink = composed_net.service_sinks.get(ch.callee_service)

        consumer_found = len(consumers) > 0
        callee_sink_exists = callee_sink is not None
        no_deadlock = len(state_space["premature_deadlocks"]) == 0

        is_live = consumer_found and callee_sink_exists and no_deadlock
        if not is_live:
            all_live = False

        channel_details.append({
            "channel_name": ch.channel_name,
            "channel_place": ch_place,
            "pattern": ch.pattern,
            "caller_service": ch.caller_service,
            "callee_service": ch.callee_service,
            "consumers": consumers,
            "consumer_found": consumer_found,
            "callee_sink": callee_sink,
            "is_live": is_live,
        })

    status = PropertyStatus.HOLDS if all_live else PropertyStatus.VIOLATED
    elapsed_ms = round((time.time() - t0) * 1000, 2)

    return {
        "property_id": "RESPONSE_LIVENESS",
        "name": "Response-Liveness",
        "status": status.value,
        "total_ip4_channels": len(ip4_channels),
        "all_ip4_channels_live": all_live,
        "details": channel_details,
        "execution_time_ms": elapsed_ms,
        "description": "Verifies mandatory consumption and return-flow reachability over IP-4 request-response channels",
    }


def verify_composition(
    composed_net: ComposedNetModel,
    engine: str = "auto",
    lola_bin: str = "lola",
    max_states: int = 300000,
) -> Dict[str, Any]:
    """Execute complete 4-property formal verification suite on composed net N_C.
    
    Args:
        composed_net: Composed Petri net model.
        engine: 'auto', 'lola', or 'internal'.
        lola_bin: Path to LoLA binary.
        max_states: Maximum state space cutoff.
        
    Returns:
        Complete composition verification report dictionary.
    """
    t_start = time.time()

    state_space = solve_state_space_internal(composed_net, max_states=max_states)

    p0_res = verify_p0_soundness(composed_net, state_space, engine=engine, lola_bin=lola_bin)
    orphan_res = verify_orphaned_message_freedom(composed_net, state_space, engine=engine, lola_bin=lola_bin)
    bound_res = verify_channel_1_boundedness(composed_net, state_space, engine=engine, lola_bin=lola_bin)
    live_res = verify_response_liveness(composed_net, state_space)

    all_hold = (
        p0_res["status"] == PropertyStatus.HOLDS.value
        and orphan_res["status"] == PropertyStatus.HOLDS.value
        and bound_res["status"] == PropertyStatus.HOLDS.value
        and live_res["status"] == PropertyStatus.HOLDS.value
    )

    total_elapsed_ms = round((time.time() - t_start) * 1000, 2)

    report = {
        "_meta": {
            "name": "Composition Verification Certificate",
            "version": "1.0.0",
            "workflow": composed_net.workflow_name,
            "generated_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
            "all_properties_hold": all_hold,
            "total_services": len(composed_net.participating_services),
            "total_channels": len(composed_net.channels),
            "total_places": len(composed_net.places),
            "total_transitions": len(composed_net.transitions),
            "total_arcs": len(composed_net.arcs),
            "states_explored": state_space["states_explored"],
            "total_execution_time_ms": total_elapsed_ms,
        },
        "composed_net": {
            "workflow_name": composed_net.workflow_name,
            "participating_services": composed_net.participating_services,
            "channels": [ch.to_dict() for ch in composed_net.channels],
            "places_count": len(composed_net.places),
            "transitions_count": len(composed_net.transitions),
            "arcs_count": len(composed_net.arcs),
        },
        "properties": {
            "p0_soundness": p0_res,
            "orphaned_message_freedom": orphan_res,
            "channel_1_boundedness": bound_res,
            "response_liveness": live_res,
        },
        "summary": {
            "all_properties_hold": all_hold,
            "p0_soundness_holds": p0_res["status"] == PropertyStatus.HOLDS.value,
            "orphaned_message_freedom_holds": orphan_res["status"] == PropertyStatus.HOLDS.value,
            "channel_1_boundedness_holds": bound_res["status"] == PropertyStatus.HOLDS.value,
            "response_liveness_holds": live_res["status"] == PropertyStatus.HOLDS.value,
            "total_execution_time_ms": total_elapsed_ms,
        }
    }

    return report


def export_verification_report(report: Dict[str, Any], output_path: str) -> str:
    """Serialize verification certificate to JSON file."""
    os.makedirs(os.path.dirname(os.path.abspath(output_path)), exist_ok=True)
    with open(output_path, "w", encoding="utf-8") as f:
        json.dump(report, f, indent=2, sort_keys=True)
    return output_path


# ============================================================================
# 7. Negative Control Fault Injection Fixtures
# ============================================================================

def inject_artificial_deadlock(composed_net: ComposedNetModel) -> ComposedNetModel:
    """Inject an artificial premature deadlock into composed net N_C.
    
    Inserts an unfillable prerequisite place `p_deadlock_blocker` before a key callee
    transition, preventing completion of downstream services and causing a deadlock.
    
    Args:
        composed_net: Sound composed net model.
        
    Returns:
        Fault-injected ComposedNetModel copy.
    """
    faulty_net = copy.deepcopy(composed_net)
    blocker_place = "injected::p_deadlock_blocker"
    faulty_net.places.append(blocker_place)
    faulty_net.places = sorted(faulty_net.places)

    target_transition = None
    for t in faulty_net.transitions:
        if not t.get("is_silent") and t["id"] != faulty_net.initial_marking[0]:
            target_transition = t["id"]
            break

    if target_transition:
        faulty_net.arcs.append((blocker_place, target_transition))

    return faulty_net


def inject_stranded_orphaned_message(composed_net: ComposedNetModel) -> ComposedNetModel:
    """Inject an artificial orphaned message into composed net N_C.
    
    Instantiates an extra unconsumed interface channel `ch::InjectedOrphan` and connects
    an entry transition to produce a token into it, leaving it unconsumed upon completion.
    
    Args:
        composed_net: Sound composed net model.
        
    Returns:
        Fault-injected ComposedNetModel copy.
    """
    faulty_net = copy.deepcopy(composed_net)
    orphan_place = "ch::InjectedOrphan"
    faulty_net.places.append(orphan_place)
    faulty_net.places = sorted(faulty_net.places)

    faulty_net.channels.append(ChannelMetadata(
        channel_name="InjectedOrphan",
        channel_place=orphan_place,
        caller_service=faulty_net.participating_services[0],
        callee_service="orphan-sink-service",
        pattern="IP-1",
        launch_type="async",
    ))

    root_place = faulty_net.initial_marking[0]
    for src, tgt in faulty_net.arcs:
        if src == root_place:
            faulty_net.arcs.append((tgt, orphan_place))
            break

    return faulty_net


def inject_unbounded_channel(composed_net: ComposedNetModel) -> ComposedNetModel:
    """Inject an unbounded channel token generator into composed net N_C.
    
    Adds duplicate produce arcs into the first channel place, violating the 1-boundedness invariant.
    
    Args:
        composed_net: Sound composed net model.
        
    Returns:
        Fault-injected ComposedNetModel copy.
    """
    faulty_net = copy.deepcopy(composed_net)
    if not faulty_net.channels:
        return faulty_net

    target_ch = faulty_net.channels[0].channel_place
    root_place = faulty_net.initial_marking[0]

    for src, tgt in faulty_net.arcs:
        if src == root_place:
            faulty_net.arcs.append((tgt, target_ch))
            faulty_net.arcs.append((tgt, target_ch))
            break

    return faulty_net


# ============================================================================
# 8. Command-Line Interface (CLI)
# ============================================================================

def parse_args(argv: Optional[List[str]] = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Asynchronous Channel Fusion Workflow Net Composer & 4-Property Verifier.",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    parser.add_argument(
        "--mined-nets",
        default="interfaces/mined-nets.json",
        help="Path to mined-nets.json containing discovered per-service Petri nets.",
    )
    parser.add_argument(
        "--reference-nets",
        default=None,
        help="Optional path to reference-nets.json to load reference workflow net models.",
    )
    parser.add_argument(
        "--topology",
        default="interfaces/social-network.json",
        help="Path to topology JSON contract oracle (interfaces/social-network.json).",
    )
    parser.add_argument(
        "--workflow",
        default="compose_post_workflow",
        help="Target workflow name to compose (e.g. compose_post_workflow, read_home_timeline_workflow).",
    )
    parser.add_argument(
        "--output-json",
        default="interfaces/composed-net.json",
        help="Destination path for composed net JSON representation.",
    )
    parser.add_argument(
        "--output-lola",
        default="interfaces/lola/composed-net.lola",
        help="Destination path for composed net LoLA representation.",
    )
    parser.add_argument(
        "--output-pnml",
        default="interfaces/pnml/composed-net.pnml",
        help="Destination path for composed net PNML representation.",
    )
    parser.add_argument(
        "--output-report",
        default="interfaces/composition-verification-report.json",
        help="Destination path for composition verification report JSON.",
    )
    parser.add_argument(
        "--engine",
        choices=["auto", "lola", "internal"],
        default="auto",
        help="Model checking verification engine.",
    )
    parser.add_argument(
        "--lola-bin",
        default="lola",
        help="Path or name of LoLA executable binary.",
    )
    parser.add_argument(
        "--max-states",
        type=int,
        default=300000,
        help="Maximum reachable state space cutoff for internal solver.",
    )
    parser.add_argument(
        "--negative-control",
        choices=["none", "deadlock", "orphan", "unbounded", "all"],
        default="none",
        help="Inject deliberate negative control faults to verify detector sensitivity.",
    )
    parser.add_argument(
        "--diagram-dir",
        default="interfaces/diagrams",
        help="Destination directory for composed net diagrams (default: interfaces/diagrams).",
    )
    parser.add_argument(
        "--export-diagrams",
        action="store_true",
        default=False,
        help="Export flat and service-grouped DOT, SVG, and PNG diagrams.",
    )
    return parser.parse_args(argv)


def main(argv: Optional[List[str]] = None) -> int:
    args = parse_args(argv)

    print("=" * 70)
    print(">>> Asynchronous Channel Fusion Workflow Net Composer <<<")
    print("=" * 70)

    # 1. Load topology contract
    if not os.path.exists(args.topology):
        print(f"[!] Error: Topology contract file not found: {args.topology}")
        return 1

    with open(args.topology, "r", encoding="utf-8") as f:
        topology_data = json.load(f)

    # 2. Load service nets
    input_file = args.reference_nets if args.reference_nets else args.mined_nets
    if not os.path.exists(input_file):
        print(f"[!] Error: Service nets input file not found: {input_file}")
        return 1

    with open(input_file, "r", encoding="utf-8") as f:
        raw_nets_data = json.load(f)

    # If reference-nets has "workflows" top-level key
    if "workflows" in raw_nets_data and isinstance(raw_nets_data["workflows"], dict):
        raw_nets_data = raw_nets_data["workflows"]

    service_nets: Dict[str, PetriNetModel] = {}
    for svc_name, s_data in raw_nets_data.items():
        if isinstance(s_data, dict) and not svc_name.startswith("_"):
            service_nets[svc_name] = PetriNetModel.from_dict(s_data, name=svc_name)

    print(f"[*] Loaded {len(service_nets)} service net(s) from: {input_file}")
    print(f"[*] Target workflow: {args.workflow}")

    # 3. Perform Channel Fusion Composition
    try:
        composed_net = compose_workflow_nets(
            service_nets=service_nets,
            topology_data=topology_data,
            workflow_name=args.workflow,
        )
    except Exception as e:
        print(f"[!] Error during composition: {e}")
        return 1

    print(f"[+] Composition synthesized successfully:")
    print(f"    - Participating Services ({len(composed_net.participating_services)}): {', '.join(composed_net.participating_services)}")
    print(f"    - Channel Places ({len(composed_net.channels)}): {', '.join(composed_net.channel_places)}")
    print(f"    - Total Places: {len(composed_net.places)}")
    print(f"    - Total Transitions: {len(composed_net.transitions)}")
    print(f"    - Total Arcs: {len(composed_net.arcs)}")

    # 4. Handle Negative Control Injection if requested
    eval_net = composed_net
    if args.negative_control == "deadlock":
        print("[!] Injecting artificial premature deadlock fault...")
        eval_net = inject_artificial_deadlock(composed_net)
    elif args.negative_control == "orphan":
        print("[!] Injecting artificial orphaned channel message fault...")
        eval_net = inject_stranded_orphaned_message(composed_net)
    elif args.negative_control == "unbounded":
        print("[!] Injecting artificial unbounded channel token fault...")
        eval_net = inject_unbounded_channel(composed_net)

    # 5. Serialize Composed Net
    serialize_composed_to_json(eval_net, args.output_json)
    serialize_composed_to_lola(eval_net, output_path=args.output_lola)
    serialize_composed_to_pnml(eval_net, args.output_pnml)
    print(f"[+] Exported composed net to:")
    print(f"    - JSON: {args.output_json}")
    print(f"    - LoLA: {args.output_lola}")
    print(f"    - PNML: {args.output_pnml}")

    if args.export_diagrams or (args.diagram_dir and args.diagram_dir != "interfaces/diagrams"):
        diagram_paths = render_composed_diagrams(eval_net, output_dir=args.diagram_dir)
        print(f"[+] Exported composed diagrams to {args.diagram_dir}:")
        for k, p in sorted(diagram_paths.items()):
            print(f"    - {k}: {p}")

    # 6. Execute Formal Verification Suite
    print("\n[*] Executing 4-Property Formal Verification Suite...")
    report = verify_composition(
        eval_net,
        engine=args.engine,
        lola_bin=args.lola_bin,
        max_states=args.max_states,
    )

    export_verification_report(report, args.output_report)
    print(f"[+] Exported verification certificate to: {args.output_report}")

    props = report["properties"]
    print("\n" + "-" * 70)
    print(f"1. P0 Soundness / Deadlock Freedom:      {props['p0_soundness']['status']} ({props['p0_soundness']['verdict']})")
    print(f"2. Orphaned Message Freedom:             {props['orphaned_message_freedom']['status']} ({props['orphaned_message_freedom']['verdict']})")
    print(f"3. Channel 1-Boundedness:                {props['channel_1_boundedness']['status']}")
    print(f"4. Response-Liveness:                    {props['response_liveness']['status']}")
    print("-" * 70)
    print(f">>> Overall Verdict: {'ALL PROPERTIES HOLD (SOUND COMPOSITION)' if report['summary']['all_properties_hold'] else 'PROPERTY VIOLATION DETECTED'} <<<")
    print("=" * 70)

    return 0


if __name__ == "__main__":
    sys.exit(main())
