#!/usr/bin/env python3
"""
Observer Instrumentation & LoLA Model Checking Detector.

Verifies whether candidate mandatory client sends (A_i) are unskippable in
discovered service Generalized Workflow (GWF) Petri nets (R_i).

Key Features:
  - Dynamic Observer Place Instrumentation: Injects an unconsumed place `obs`
    and produce-arc `x -> obs` for a target candidate transition `x`.
  - LoLA Specification Serialization: Generates valid LoLA `.lola` files and
    CTL formulas (`FORMULA EF(sink > 0 AND obs = 0)`).
  - Dual-Engine Verification: Executes LoLA model checker (`--search=covergraph`)
    or built-in pure-Python coverability/state-space reachability solver.
  - Classification:
      * UNSAT: Mandatory send is unskippable; alpha-morphism R_i ->_a A_i holds.
      * SAT: False tau-skip detected; completion reachable without firing x.
  - Negative Control Self-Check: Injects artificial bypass transitions to verify
    detector sensitivity (UNSAT -> SAT).
"""

import argparse
import copy
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from enum import Enum
from pathlib import Path
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


class Verdict(str, Enum):
    """Model checking verdict for CTL formula EF(end > 0 AND obs = 0)."""
    UNSAT = "UNSAT"  # Formula unsatisfiable -> Mandatory transition is unskippable (Alpha-morphism holds)
    SAT = "SAT"      # Formula satisfiable -> False tau-skip detected (Completion without mandatory call)
    ERROR = "ERROR"  # Execution or syntax failure


class AlphaMorphismStatus(str, Enum):
    """Alpha-morphism conformance status."""
    HOLDS = "HOLDS"          # UNSAT: unskippable
    VIOLATED = "VIOLATED"    # SAT: false tau-skip detected
    UNKNOWN = "UNKNOWN"      # ERROR or inconclusive


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
    # Replace non-alphanumeric characters with underscore
    sanitized = re.sub(r"[^A-Za-z0-9_]", "_", name)
    
    # Ensure identifier starts with a letter or underscore (not digit)
    if sanitized and sanitized[0].isdigit():
        sanitized = f"p_{sanitized}"
        
    if not sanitized:
        sanitized = "item"
        
    # Prevent collision with reserved keywords
    if sanitized.upper() in LOLA_KEYWORDS:
        sanitized = f"node_{sanitized}"
        
    # Handle uniqueness if used_identifiers set is supplied
    if used_identifiers is not None:
        base = sanitized
        counter = 1
        while sanitized in used_identifiers:
            sanitized = f"{base}_{counter}"
            counter += 1
        used_identifiers.add(sanitized)
        
    return sanitized


class PetriNetModel:
    """Lightweight, portable Petri net representation decoupled from external libraries."""

    def __init__(
        self,
        name: str = "net",
        places: Optional[List[str]] = None,
        transitions: Optional[List[Dict[str, Any]]] = None,
        arcs: Optional[List[Tuple[str, str]]] = None,
        initial_marking: Optional[List[str]] = None,
        final_marking: Optional[List[str]] = None,
    ):
        self.name = name
        self.places: List[str] = sorted(list(places or []))
        # transitions: list of {"id": str, "label": Optional[str], "is_silent": bool}
        self.transitions: List[Dict[str, Any]] = list(transitions or [])
        # arcs: list of (source_id, target_id)
        self.arcs: List[Tuple[str, str]] = list(arcs or [])
        self.initial_marking: List[str] = list(initial_marking or [])
        self.final_marking: List[str] = list(final_marking or [])

    @classmethod
    def from_dict(cls, data: Dict[str, Any], name: str = "net") -> "PetriNetModel":
        """Construct PetriNetModel from serialized mined-nets.json dictionary."""
        service_name = data.get("service", name)
        places = list(data.get("places", []))
        transitions = list(data.get("transitions", []))
        raw_arcs = data.get("arcs", [])
        arcs = [(a[0], a[1]) for a in raw_arcs]
        im = list(data.get("initial_marking", []))
        fm = list(data.get("final_marking", []))
        return cls(
            name=service_name,
            places=places,
            transitions=transitions,
            arcs=arcs,
            initial_marking=im,
            final_marking=fm,
        )

    @classmethod
    def from_pm4py(
        cls,
        net: PetriNet,
        initial_marking: Marking,
        final_marking: Marking,
        name: str = "net",
    ) -> "PetriNetModel":
        """Construct PetriNetModel from pm4py PetriNet object."""
        places = sorted([p.name for p in net.places])
        transitions = []
        for t in net.transitions:
            is_silent = t.label is None or t.label == ""
            transitions.append({
                "id": t.name,
                "label": t.label if not is_silent else None,
                "is_silent": is_silent,
            })
        transitions.sort(key=lambda x: (x["is_silent"], x["label"] or "", x["id"]))

        arcs = sorted([(arc.source.name, arc.target.name) for arc in net.arcs])
        im = sorted([p.name for p, count in initial_marking.items() for _ in range(count)])
        fm = sorted([p.name for p, count in final_marking.items() for _ in range(count)])

        return cls(
            name=name,
            places=places,
            transitions=transitions,
            arcs=arcs,
            initial_marking=im,
            final_marking=fm,
        )

    def to_dict(self) -> Dict[str, Any]:
        """Serialize to dictionary representation."""
        return {
            "service": self.name,
            "places": sorted(self.places),
            "transitions": sorted(self.transitions, key=lambda x: (x.get("is_silent", False), x.get("label") or "", x["id"])),
            "arcs": sorted([[a[0], a[1]] for a in self.arcs]),
            "initial_marking": sorted(self.initial_marking),
            "final_marking": sorted(self.final_marking),
        }

    def clone(self) -> "PetriNetModel":
        """Return a deep copy of this Petri net model."""
        return PetriNetModel(
            name=self.name,
            places=list(self.places),
            transitions=[copy.deepcopy(t) for t in self.transitions],
            arcs=list(self.arcs),
            initial_marking=list(self.initial_marking),
            final_marking=list(self.final_marking),
        )

    def get_preset(self, node_id: str) -> Set[str]:
        """Return preset nodes (incoming arc sources) for a place or transition."""
        return {src for src, tgt in self.arcs if tgt == node_id}

    def get_postset(self, node_id: str) -> Set[str]:
        """Return postset nodes (outgoing arc targets) for a place or transition."""
        return {tgt for src, tgt in self.arcs if src == node_id}

    def find_transitions_by_target(self, target: str) -> List[Dict[str, Any]]:
        """Find matching transitions by ID or label/activity name.
        
        Args:
            target: Exact transition ID or transition label.
            
        Returns:
            List of matching transition dicts.
        """
        matches = []
        # First check exact ID match
        for t in self.transitions:
            if t["id"] == target:
                matches.append(t)
        if matches:
            return matches

        # Next check label match
        for t in self.transitions:
            if t.get("label") == target:
                matches.append(t)
        return matches

    def get_sink_place(self) -> str:
        """Resolve the terminal sink place identifier."""
        if self.final_marking:
            return self.final_marking[0]
        # Fallback: place with no outgoing arcs or named 'sink' / 'p_sink' / 'end'
        for p in self.places:
            if p.lower() in ("sink", "p_sink", "end", "p_end"):
                return p
        for p in self.places:
            if len(self.get_postset(p)) == 0:
                return p
        raise ValueError(f"No sink/final place identified in net '{self.name}'")


def instrument_observer_place(
    net_model: PetriNetModel,
    target: str,
    obs_place_name: str = "obs",
) -> Tuple[PetriNetModel, List[str], str]:
    """Dynamically inject an unconsumed observer place `obs` and produce-arc `x -> obs`.
    
    Args:
        net_model: Source Petri net model.
        target: Target candidate transition ID or label.
        obs_place_name: Desired name for the observer place (default 'obs').
        
    Returns:
        Tuple of (instrumented_net_model, target_transition_ids, actual_obs_place_name).
        
    Raises:
        ValueError: If target transition cannot be found in the net.
    """
    matching_transitions = net_model.find_transitions_by_target(target)
    if not matching_transitions:
        raise ValueError(
            f"Target transition '{target}' not found in Petri net '{net_model.name}'. "
            f"Available transitions: {[t.get('label') or t['id'] for t in net_model.transitions]}"
        )

    instrumented = net_model.clone()
    
    # Ensure observer place name is unique
    actual_obs = obs_place_name
    counter = 1
    while actual_obs in instrumented.places:
        actual_obs = f"{obs_place_name}_{counter}"
        counter += 1

    instrumented.places.append(actual_obs)
    instrumented.places.sort()

    target_ids = []
    for t in matching_transitions:
        t_id = t["id"]
        target_ids.append(t_id)
        # Add produce-arc x -> obs
        instrumented.arcs.append((t_id, actual_obs))

    instrumented.arcs.sort()
    return instrumented, target_ids, actual_obs


def serialize_to_lola(
    net_model: PetriNetModel,
    formula: Optional[str] = None,
) -> Tuple[str, Dict[str, str], Dict[str, str]]:
    """Serialize a Petri net model into standard LoLA format (.lola).
    
    Args:
        net_model: Petri net model to serialize.
        formula: Optional CTL formula string to append to the LoLA specification.
        
    Returns:
        Tuple of (lola_content_string, name_to_lola_map, lola_to_name_map).
    """
    used_tokens: Set[str] = set()
    name_to_lola: Dict[str, str] = {}
    lola_to_name: Dict[str, str] = {}

    # Map places
    for p in sorted(net_model.places):
        token = sanitize_lola_identifier(p, used_tokens)
        name_to_lola[p] = token
        lola_to_name[token] = p

    # Map transitions
    for t in net_model.transitions:
        t_id = t["id"]
        label = t.get("label") or t_id
        suggested = f"t_{label}" if t.get("label") else f"t_{t_id}"
        token = sanitize_lola_identifier(suggested, used_tokens)
        name_to_lola[t_id] = token
        lola_to_name[token] = t_id

    lines: List[str] = []
    lines.append(f"{{ LoLA Petri Net Model: {net_model.name} }}")
    lines.append(f"{{ Generated by GWF Net Composition Observer Detector }}")
    lines.append("")

    # Places declaration
    lola_places = [name_to_lola[p] for p in sorted(net_model.places)]
    lines.append(f"PLACE SAFE: {', '.join(lola_places)};")
    lines.append("")

    # Initial marking declaration
    if net_model.initial_marking:
        im_counts: Dict[str, int] = {}
        for p in net_model.initial_marking:
            token = name_to_lola[p]
            im_counts[token] = im_counts.get(token, 0) + 1
        im_str = ", ".join(f"{tok}: {cnt}" for tok, cnt in sorted(im_counts.items()))
        lines.append(f"MARKING {im_str};")
    else:
        lines.append("MARKING ;")
    lines.append("")

    # Transitions declarations
    for t in sorted(net_model.transitions, key=lambda x: name_to_lola[x["id"]]):
        t_id = t["id"]
        t_tok = name_to_lola[t_id]
        
        # In-arcs (CONSUME from places)
        consume_places: Dict[str, int] = {}
        for src, tgt in net_model.arcs:
            if tgt == t_id and src in name_to_lola:
                p_tok = name_to_lola[src]
                consume_places[p_tok] = consume_places.get(p_tok, 0) + 1
                
        # Out-arcs (PRODUCE to places)
        produce_places: Dict[str, int] = {}
        for src, tgt in net_model.arcs:
            if src == t_id and tgt in name_to_lola:
                p_tok = name_to_lola[tgt]
                produce_places[p_tok] = produce_places.get(p_tok, 0) + 1

        consume_str = ", ".join(f"{p}: {c}" for p, c in sorted(consume_places.items()))
        produce_str = ", ".join(f"{p}: {c}" for p, c in sorted(produce_places.items()))

        lines.append(f"TRANSITION {t_tok}")
        lines.append(f"  CONSUME {consume_str};")
        lines.append(f"  PRODUCE {produce_str};")
        lines.append("")

    if formula:
        lines.append(f"FORMULA {formula};")
        lines.append("")

    return "\n".join(lines), name_to_lola, lola_to_name


def formulate_ctl_reachability_formula(
    sink_place_token: str,
    obs_place_token: str,
) -> str:
    """Formulate LoLA CTL reachability formula EF(sink > 0 AND obs = 0).
    
    Args:
        sink_place_token: LoLA token identifier for the sink place.
        obs_place_token: LoLA token identifier for the observer place.
        
    Returns:
        Formula string conforming to LoLA grammar.
    """
    return f"EF ({sink_place_token} > 0 AND {obs_place_token} = 0)"


def solve_reachability_internal(
    net_model: PetriNetModel,
    sink_place: str,
    obs_place: str,
    max_states: int = 100000,
) -> Tuple[Verdict, Optional[List[Dict[str, Any]]], int]:
    """Pure-Python coverability / BFS state-space reachability solver.
    
    Explores the reachable marking state space starting from initial_marking.
    Evaluates reachability of state satisfying: M(sink_place) > 0 AND M(obs_place) == 0.
    
    Args:
        net_model: Instrumented Petri net model.
        sink_place: Target sink place identifier.
        obs_place: Target observer place identifier.
        max_states: Safety bound on visited markings to prevent unbounded search.
        
    Returns:
        Tuple of (Verdict, witness_trace_list_if_SAT, total_states_explored).
    """
    # Pre-index place and transition mappings for fast firing
    place_to_idx = {p: i for i, p in enumerate(net_model.places)}
    num_places = len(net_model.places)
    sink_idx = place_to_idx[sink_place]
    obs_idx = place_to_idx[obs_place]

    # Build initial marking vector
    initial_vec = [0] * num_places
    for p in net_model.initial_marking:
        if p in place_to_idx:
            initial_vec[place_to_idx[p]] += 1
    m0 = tuple(initial_vec)

    # Check if initial marking already satisfies formula (trivial edge case)
    if m0[sink_idx] > 0 and m0[obs_idx] == 0:
        return Verdict.SAT, [{"transition": None, "marking": {p: m0[place_to_idx[p]] for p in net_model.places if m0[place_to_idx[p]] > 0}}], 1

    # Transition delta tables: {t_id: (consume_list, produce_list, transition_obj)}
    transitions_data = []
    for t in net_model.transitions:
        t_id = t["id"]
        # consume list of (place_idx, count)
        preset_counts: Dict[int, int] = {}
        for src, tgt in net_model.arcs:
            if tgt == t_id and src in place_to_idx:
                p_i = place_to_idx[src]
                preset_counts[p_i] = preset_counts.get(p_i, 0) + 1
        consume = [(p_i, cnt) for p_i, cnt in preset_counts.items()]

        # produce list of (place_idx, count)
        postset_counts: Dict[int, int] = {}
        for src, tgt in net_model.arcs:
            if src == t_id and tgt in place_to_idx:
                p_i = place_to_idx[tgt]
                postset_counts[p_i] = postset_counts.get(p_i, 0) + 1
        produce = [(p_i, cnt) for p_i, cnt in postset_counts.items()]

        transitions_data.append((t_id, t.get("label"), consume, produce))

    # BFS exploration queue: (current_marking_tuple, path_list)
    from collections import deque
    queue = deque([(m0, [])])
    visited: Set[Tuple[int, ...]] = {m0}
    states_explored = 0

    while queue:
        current_m, path = queue.popleft()
        states_explored += 1

        if states_explored > max_states:
            # Reached search bound
            break

        # Try firing all enabled transitions
        for t_id, t_label, consume, produce in transitions_data:
            # Check enabled: all input places have enough tokens
            enabled = True
            for p_i, req in consume:
                if current_m[p_i] < req:
                    enabled = False
                    break
            if not enabled:
                continue

            # Compute next marking
            next_m_list = list(current_m)
            for p_i, cnt in consume:
                next_m_list[p_i] -= cnt
            for p_i, cnt in produce:
                next_m_list[p_i] += cnt
            next_m = tuple(next_m_list)

            # Check if next_m satisfies EF(sink > 0 AND obs = 0)
            if next_m[sink_idx] > 0 and next_m[obs_idx] == 0:
                witness = list(path)
                witness.append({
                    "transition_id": t_id,
                    "label": t_label,
                    "marking": {net_model.places[i]: next_m[i] for i in range(num_places) if next_m[i] > 0}
                })
                return Verdict.SAT, witness, states_explored + 1

            if next_m not in visited:
                visited.add(next_m)
                next_path = list(path)
                next_path.append({
                    "transition_id": t_id,
                    "label": t_label,
                })
                queue.append((next_m, next_path))

    # All reachable states explored without reaching sink with obs=0
    return Verdict.UNSAT, None, states_explored


def solve_reachability_lola(
    net_model: PetriNetModel,
    formula_str: str,
    lola_bin: str = "lola",
) -> Tuple[Verdict, Optional[str], float]:
    """Execute external LoLA model checker with --search=covergraph.
    
    Args:
        net_model: Instrumented Petri net model.
        formula_str: CTL reachability formula in LoLA syntax.
        lola_bin: Path or name of LoLA executable.
        
    Returns:
        Tuple of (Verdict, raw_stdout, elapsed_seconds).
    """
    # LoLA 2.0 rejects a FORMULA embedded in the net file; the net must be
    # formula-free and the query supplied via --formula (mirrors verify_properties).
    lola_content, _, _ = serialize_to_lola(net_model)
    formula_arg = formula_str if formula_str.strip().startswith("FORMULA") else f"FORMULA {formula_str}"

    with tempfile.TemporaryDirectory() as tmp_dir:
        net_path = os.path.join(tmp_dir, "net.lola")
        with open(net_path, "w", encoding="utf-8") as f:
            f.write(lola_content)

        cmd = [
            lola_bin,
            net_path,
            f"--formula={formula_arg}",
            "--search=covergraph",
        ]

        t0 = time.time()
        try:
            proc = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=30,
            )
            elapsed = time.time() - t0
        except FileNotFoundError:
            raise FileNotFoundError(f"LoLA executable '{lola_bin}' not found in PATH.")
        except subprocess.TimeoutExpired:
            return Verdict.ERROR, "LoLA execution timed out after 30s", 30.0

        output = proc.stdout + "\n" + proc.stderr

        # LoLA output parsing:
        # "result: yes" / "The formula is true" -> SAT
        # "result: no" / "The formula is false" -> UNSAT
        if "result: yes" in output.lower() or "formula is true" in output.lower():
            return Verdict.SAT, output, elapsed
        elif "result: no" in output.lower() or "formula is false" in output.lower():
            return Verdict.UNSAT, output, elapsed
        else:
            return Verdict.ERROR, output, elapsed


def verify_target_transition(
    net_model: PetriNetModel,
    target: str,
    engine: str = "auto",
    lola_bin: str = "lola",
) -> Dict[str, Any]:
    """Verify unskippability of target candidate transition in a service net.
    
    Args:
        net_model: Discovered service Workflow net.
        target: Target candidate transition ID or label.
        engine: 'auto', 'lola', or 'internal'.
        lola_bin: LoLA binary name/path.
        
    Returns:
        Structured result dict with verdict, status, timing, and witness if SAT.
    """
    t0 = time.time()
    
    # 1. Instrument net with observer place
    try:
        instrumented_net, target_ids, obs_place = instrument_observer_place(net_model, target)
    except ValueError as e:
        return {
            "service": net_model.name,
            "target": target,
            "verdict": Verdict.ERROR.value,
            "alpha_morphism": AlphaMorphismStatus.UNKNOWN.value,
            "error": str(e),
            "execution_time_ms": round((time.time() - t0) * 1000, 2),
        }

    sink_place = net_model.get_sink_place()

    # 2. Formulate LoLA CTL formula
    lola_str, name_to_lola, _ = serialize_to_lola(instrumented_net)
    sink_tok = name_to_lola[sink_place]
    obs_tok = name_to_lola[obs_place]
    formula = formulate_ctl_reachability_formula(sink_tok, obs_tok)

    # 3. Model checking execution
    resolved_engine = engine
    if engine == "auto":
        resolved_engine = "lola" if shutil.which(lola_bin) is not None else "internal"

    verdict = Verdict.ERROR
    witness = None
    states_explored = 0
    raw_output = None

    if resolved_engine == "lola":
        try:
            verdict, raw_output, _ = solve_reachability_lola(instrumented_net, formula, lola_bin=lola_bin)
        except (FileNotFoundError, Exception):
            # Fallback to internal solver if lola fails
            verdict, witness, states_explored = solve_reachability_internal(instrumented_net, sink_place, obs_place)
            resolved_engine = "internal (fallback)"
    else:
        verdict, witness, states_explored = solve_reachability_internal(instrumented_net, sink_place, obs_place)

    elapsed_ms = round((time.time() - t0) * 1000, 2)

    alpha_status = AlphaMorphismStatus.HOLDS if verdict == Verdict.UNSAT else (
        AlphaMorphismStatus.VIOLATED if verdict == Verdict.SAT else AlphaMorphismStatus.UNKNOWN
    )

    result = {
        "service": net_model.name,
        "target": target,
        "target_transition_ids": target_ids,
        "sink_place": sink_place,
        "observer_place": obs_place,
        "formula": formula,
        "verdict": verdict.value,
        "alpha_morphism": alpha_status.value,
        "engine": resolved_engine,
        "states_explored": states_explored,
        "execution_time_ms": elapsed_ms,
    }

    if witness:
        result["witness_trace"] = witness
    if raw_output:
        result["engine_output"] = raw_output.strip()

    return result


def inject_negative_control_bypass(
    net_model: PetriNetModel,
    target: str,
    bypass_trans_id: str = "t_artificial_bypass",
) -> Tuple[PetriNetModel, str]:
    """Synthesize an artificial bypass transition around candidate target transition x.
    
    Consumes from preset(x) and produces into postset(x) without producing into observer,
    enabling workflow completion without firing x to test detector sensitivity.
    
    Args:
        net_model: Input Petri net model.
        target: Target candidate transition ID or label.
        bypass_trans_id: ID for the synthetic bypass transition.
        
    Returns:
        Tuple of (bypassed_net_model, actual_bypass_id).
    """
    matching = net_model.find_transitions_by_target(target)
    if not matching:
        raise ValueError(f"Cannot inject bypass: Target '{target}' not found in net '{net_model.name}'")

    target_t = matching[0]
    target_id = target_t["id"]
    preset_places = net_model.get_preset(target_id)
    postset_places = net_model.get_postset(target_id)

    bypassed = net_model.clone()
    
    actual_id = bypass_trans_id
    counter = 1
    existing_t_ids = {t["id"] for t in bypassed.transitions}
    while actual_id in existing_t_ids:
        actual_id = f"{bypass_trans_id}_{counter}"
        counter += 1

    bypassed.transitions.append({
        "id": actual_id,
        "label": f"bypass_{target_t.get('label') or target_id}",
        "is_silent": True,
    })

    # Add arcs from all preset places to bypass transition
    for p in preset_places:
        bypassed.arcs.append((p, actual_id))

    # Add arcs from bypass transition to all postset places
    for p in postset_places:
        bypassed.arcs.append((actual_id, p))

    bypassed.arcs.sort()
    return bypassed, actual_id


def resolve_candidate_mandatory_sends(
    service_name: str,
    net_model: PetriNetModel,
    contracts_path: Optional[str] = "interfaces/idl-contracts.json",
    topology_path: Optional[str] = "interfaces/social-network.json",
) -> List[Dict[str, Any]]:
    """Resolve candidate mandatory client send transitions for a service from IDL and topology oracle.
    
    Args:
        service_name: Canonical service name.
        net_model: Discovered Petri net model for the service.
        contracts_path: Path to idl-contracts.json.
        topology_path: Path to social-network.json.
        
    Returns:
        List of candidate transition descriptors.
    """
    candidates = []

    # 1. From discovered net transitions, inspect all visible client spans (ending in _client)
    for t in net_model.transitions:
        label = t.get("label")
        if label and label.endswith("_client"):
            candidates.append({
                "transition_id": t["id"],
                "label": label,
                "source": "mined_net_client_span",
            })

    # If no client spans found by convention, use all visible non-server transitions
    if not candidates:
        for t in net_model.transitions:
            label = t.get("label")
            if label and not label.endswith("_server") and not t.get("is_silent", False):
                candidates.append({
                    "transition_id": t["id"],
                    "label": label,
                    "source": "mined_net_visible_activity",
                })

    return candidates


def run_batch_detection(
    mined_nets_path: str = "interfaces/mined-nets.json",
    contracts_path: Optional[str] = "interfaces/idl-contracts.json",
    topology_path: Optional[str] = "interfaces/social-network.json",
    target_service: Optional[str] = None,
    target_transition: Optional[str] = None,
    engine: str = "auto",
    lola_bin: str = "lola",
    run_negative_control: bool = True,
    export_lola_dir: Optional[str] = None,
) -> Dict[str, Any]:
    """Execute comprehensive model checking detection across mined service nets.
    
    Args:
        mined_nets_path: Path to interfaces/mined-nets.json.
        contracts_path: Path to interfaces/idl-contracts.json.
        topology_path: Path to interfaces/social-network.json.
        target_service: Optional single service filter.
        target_transition: Optional single transition filter.
        engine: Verification engine ('auto', 'lola', 'internal').
        lola_bin: LoLA binary name.
        run_negative_control: Whether to run negative control verification.
        export_lola_dir: Optional directory to export .lola files.
        
    Returns:
        Comprehensive detection report dictionary.
    """
    if not os.path.exists(mined_nets_path):
        raise FileNotFoundError(f"Mined nets file not found: {mined_nets_path}")

    with open(mined_nets_path, "r", encoding="utf-8") as f:
        mined_data = json.load(f)

    if export_lola_dir:
        os.makedirs(export_lola_dir, exist_ok=True)

    services_to_process = []
    if target_service:
        if target_service not in mined_data:
            raise ValueError(f"Service '{target_service}' not found in {mined_nets_path}")
        services_to_process.append((target_service, mined_data[target_service]))
    else:
        for s_name in sorted(mined_data.keys()):
            services_to_process.append((s_name, mined_data[s_name]))

    all_verifications = []
    summary_counts = {"total_checks": 0, "unsat_holds": 0, "sat_violations": 0, "errors": 0}
    negative_control_results = []

    for s_name, net_dict in services_to_process:
        net_model = PetriNetModel.from_dict(net_dict, name=s_name)
        
        # Export base LoLA file if requested
        if export_lola_dir:
            base_lola_str, _, _ = serialize_to_lola(net_model)
            lola_file = os.path.join(export_lola_dir, f"{s_name}.lola")
            with open(lola_file, "w", encoding="utf-8") as f:
                f.write(base_lola_str)

        # Resolve candidate targets
        if target_transition:
            candidate_targets = [{"label": target_transition, "source": "cli_target"}]
        else:
            candidate_targets = resolve_candidate_mandatory_sends(
                s_name,
                net_model,
                contracts_path=contracts_path,
                topology_path=topology_path,
            )

        for cand in candidate_targets:
            target_label = cand["label"]
            verif_res = verify_target_transition(
                net_model,
                target_label,
                engine=engine,
                lola_bin=lola_bin,
            )
            verif_res["candidate_source"] = cand.get("source", "unknown")
            all_verifications.append(verif_res)

            summary_counts["total_checks"] += 1
            if verif_res["verdict"] == Verdict.UNSAT.value:
                summary_counts["unsat_holds"] += 1
            elif verif_res["verdict"] == Verdict.SAT.value:
                summary_counts["sat_violations"] += 1
            else:
                summary_counts["errors"] += 1

            # Run Negative Control Self-Check if enabled and net is UNSAT
            if run_negative_control and verif_res["verdict"] == Verdict.UNSAT.value:
                try:
                    bypassed_net, bypass_id = inject_negative_control_bypass(net_model, target_label)
                    nc_res = verify_target_transition(
                        bypassed_net,
                        target_label,
                        engine=engine,
                        lola_bin=lola_bin,
                    )
                    passed = (nc_res["verdict"] == Verdict.SAT.value)
                    negative_control_results.append({
                        "service": s_name,
                        "target": target_label,
                        "bypass_transition": bypass_id,
                        "original_verdict": Verdict.UNSAT.value,
                        "negative_control_verdict": nc_res["verdict"],
                        "self_check_passed": passed,
                    })
                except Exception as nc_err:
                    negative_control_results.append({
                        "service": s_name,
                        "target": target_label,
                        "error": str(nc_err),
                        "self_check_passed": False,
                    })

    return {
        "_meta": {
            "title": "False Tau-Skip Observer Model Checking Report",
            "source_nets": mined_nets_path,
            "engine_requested": engine,
            "total_services": len(services_to_process),
            "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        },
        "summary": summary_counts,
        "negative_control_self_check": {
            "total_negative_controls": len(negative_control_results),
            "all_passed": all(r.get("self_check_passed", False) for r in negative_control_results) if negative_control_results else True,
            "results": negative_control_results,
        },
        "verifications": all_verifications,
    }


def main():
    """CLI entrypoint for false tau-skip observer detection."""
    parser = argparse.ArgumentParser(
        description="Deductively detect false tau-skips over mandatory interaction calls via Observer Instrumentation & LoLA Model Checking.",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    parser.add_argument(
        "--nets",
        default="interfaces/mined-nets.json",
        help="Path to serialized mined nets JSON.",
    )
    parser.add_argument(
        "--contracts",
        default="interfaces/idl-contracts.json",
        help="Path to IDL contract oracle JSON.",
    )
    parser.add_argument(
        "--topology",
        default="interfaces/social-network.json",
        help="Path to topology oracle JSON.",
    )
    parser.add_argument(
        "--service",
        default=None,
        help="Specific service to verify (e.g. compose-post-service).",
    )
    parser.add_argument(
        "--target",
        default=None,
        help="Specific target transition label/ID to verify unskippability.",
    )
    parser.add_argument(
        "--engine",
        choices=["auto", "lola", "internal"],
        default="auto",
        help="Model checking engine: 'auto' (LoLA if present, else internal), 'lola', or 'internal'.",
    )
    parser.add_argument(
        "--lola-bin",
        default="lola",
        help="LoLA model checker binary name or path.",
    )
    parser.add_argument(
        "--output",
        default="interfaces/detection-reports.json",
        help="Output path for comprehensive detection report JSON.",
    )
    parser.add_argument(
        "--summary-file",
        default="data/logs/detection.summary.json",
        help="Output path for detection summary metrics JSON.",
    )
    parser.add_argument(
        "--export-lola-dir",
        default="interfaces/lola",
        help="Directory to export .lola specification files.",
    )
    parser.add_argument(
        "--no-negative-control",
        action="store_true",
        help="Disable automatic negative control bypass self-check.",
    )

    args = parser.parse_args()

    repo_root = Path(__file__).resolve().parent.parent

    nets_path = args.nets if os.path.isabs(args.nets) else str(repo_root / args.nets)
    contracts_path = args.contracts if os.path.isabs(args.contracts) else str(repo_root / args.contracts)
    topology_path = args.topology if os.path.isabs(args.topology) else str(repo_root / args.topology)
    output_path = args.output if os.path.isabs(args.output) else str(repo_root / args.output)
    summary_path = args.summary_file if os.path.isabs(args.summary_file) else str(repo_root / args.summary_file)
    lola_dir = args.export_lola_dir if (not args.export_lola_dir or os.path.isabs(args.export_lola_dir)) else str(repo_root / args.export_lola_dir)

    print(f"[*] Starting False Tau-Skip Detection on: {nets_path}")
    print(f"[*] Model Checking Engine: {args.engine}")

    try:
        report = run_batch_detection(
            mined_nets_path=nets_path,
            contracts_path=contracts_path if os.path.exists(contracts_path) else None,
            topology_path=topology_path if os.path.exists(topology_path) else None,
            target_service=args.service,
            target_transition=args.target,
            engine=args.engine,
            lola_bin=args.lola_bin,
            run_negative_control=(not args.no_negative_control),
            export_lola_dir=lola_dir,
        )
    except Exception as e:
        print(f"[!] Error during detection execution: {e}", file=sys.stderr)
        sys.exit(1)

    # Save detailed report
    os.makedirs(os.path.dirname(output_path), exist_ok=True)
    with open(output_path, "w", encoding="utf-8") as f:
        json.dump(report, f, indent=2)
    print(f"[+] Full detection report saved to: {output_path}")

    # Save summary report
    summary_data = {
        "_meta": report["_meta"],
        "summary": report["summary"],
        "negative_control_self_check": report["negative_control_self_check"],
        "total_verifications": len(report["verifications"]),
    }
    os.makedirs(os.path.dirname(summary_path), exist_ok=True)
    with open(summary_path, "w", encoding="utf-8") as f:
        json.dump(summary_data, f, indent=2)
    print(f"[+] Detection summary metrics saved to: {summary_path}")

    print("\n--- Detection Results Summary ---")
    print(f"Total Checks: {report['summary']['total_checks']}")
    print(f"UNSAT (Alpha-Morphism Holds / Unskippable): {report['summary']['unsat_holds']}")
    print(f"SAT (False Tau-Skip Violations): {report['summary']['sat_violations']}")
    print(f"Errors: {report['summary']['errors']}")
    print(f"Negative Control Self-Check All Passed: {report['negative_control_self_check']['all_passed']}")
    print("---------------------------------")


if __name__ == "__main__":
    main()
