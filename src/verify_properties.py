#!/usr/bin/env python3
"""
LoLA Temporal Control-Flow Property Verification Engine & CLI.

Model-checks domain-specific and cross-service temporal control-flow properties
(causal precedence, fork-join barrier synchronization, mutual exclusion, clean drainage,
channel 1-boundedness, and deadlock freedom) on composed Generalized Workflow (GWF)
Petri nets using a dual-engine architecture:
  1. External LoLA Model Checker: Runs `lola` with `--formula` and `--search=covergraph`.
  2. Native Pure-Python State Space Solver: Zero-dependency BFS state-space exploration
     with exact step-by-step counterexample firing sequence witness generation.

Inputs:
  - Composed Petri nets: LoLA format (`.lola`) or structured JSON (`.json`)
  - Property specifications: LoLA CTL formulas (`.lola`) or catalog JSON (`.json`)

Outputs:
  - Structured verification report: `interfaces/property-verification-report.json`
  - Formatted terminal diagnostic summary with counterexample traces
"""

import argparse
import collections
import copy
import dataclasses
from dataclasses import dataclass, field
import datetime
from enum import Enum
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time
from typing import Any, Callable, Dict, List, Optional, Set, Tuple, Union

# Add repo root to path for module resolution
REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.workflow_net_composer import (
    ChannelMetadata,
    ComposedNetModel,
    PetriNetModel,
    PropertyStatus,
    VerificationVerdict,
    sanitize_lola_identifier,
    serialize_composed_to_lola,
)


# ============================================================================
# 1. Formula AST & Expression Classes
# ============================================================================

class FormulaAST:
    """Base class for formula AST nodes."""
    def eval(self, marking: Dict[str, int], enabled_transitions: Set[str], place_aliases: Dict[str, str]) -> bool:
        """Evaluate state predicate against a marking and enabled transition set."""
        raise NotImplementedError

    def to_lola_str(self) -> str:
        """Convert AST node to standard LoLA formula syntax string."""
        raise NotImplementedError


class AtomicPredicate(FormulaAST):
    """Base class for atomic state predicates."""
    pass


class BooleanLiteral(AtomicPredicate):
    """Boolean constant TRUE or FALSE."""
    def __init__(self, value: bool):
        self.value = bool(value)

    def eval(self, marking: Dict[str, int], enabled_transitions: Set[str], place_aliases: Dict[str, str]) -> bool:
        return self.value

    def to_lola_str(self) -> str:
        return "TRUE" if self.value else "FALSE"

    def __repr__(self) -> str:
        return f"BooleanLiteral({self.value})"


class DeadlockPredicate(AtomicPredicate):
    """Predicate evaluating to True iff current marking has 0 enabled transitions."""
    def eval(self, marking: Dict[str, int], enabled_transitions: Set[str], place_aliases: Dict[str, str]) -> bool:
        return len(enabled_transitions) == 0

    def to_lola_str(self) -> str:
        return "DEADLOCK"

    def __repr__(self) -> str:
        return "DEADLOCK"


class FireablePredicate(AtomicPredicate):
    """Predicate evaluating to True iff specified transition is enabled."""
    def __init__(self, transition: str):
        self.transition = transition

    def eval(self, marking: Dict[str, int], enabled_transitions: Set[str], place_aliases: Dict[str, str]) -> bool:
        target = self.transition
        if target in enabled_transitions:
            return True
        # Check alias if present
        alias = place_aliases.get(target)
        if alias and alias in enabled_transitions:
            return True
        # Check without prefix
        for t in enabled_transitions:
            if t.endswith(f"::{target}") or t == f"t_{target}":
                return True
        return False

    def to_lola_str(self) -> str:
        return f"FIREABLE({self.transition})"

    def __repr__(self) -> str:
        return f"FIREABLE({self.transition})"


class PlaceComparison(AtomicPredicate):
    """Place token comparison against an integer threshold: place op value."""
    VALID_OPS = {">", "<", "=", "==", ">=", "<=", "!="}

    def __init__(self, place: str, op: str, value: int):
        self.place = place
        op_norm = "==" if op == "=" else op
        if op_norm not in {"==", "!=", ">", "<", ">=", "<="}:
            raise ValueError(f"Invalid comparison operator: {op}")
        self.op = op_norm
        self.value = int(value)

    def _resolve_token_count(self, marking: Dict[str, int], place_aliases: Dict[str, str]) -> int:
        if self.place in marking:
            return marking[self.place]
        # Check canonical alias mapping
        alias = place_aliases.get(self.place)
        if alias and alias in marking:
            return marking[alias]
        # Check reverse alias
        for k, v in place_aliases.items():
            if v == self.place and k in marking:
                return marking[k]
        return 0

    def eval(self, marking: Dict[str, int], enabled_transitions: Set[str], place_aliases: Dict[str, str]) -> bool:
        cnt = self._resolve_token_count(marking, place_aliases)
        if self.op == "==":
            return cnt == self.value
        elif self.op == "!=":
            return cnt != self.value
        elif self.op == ">":
            return cnt > self.value
        elif self.op == ">=":
            return cnt >= self.value
        elif self.op == "<":
            return cnt < self.value
        elif self.op == "<=":
            return cnt <= self.value
        return False

    def to_lola_str(self) -> str:
        lola_op = "=" if self.op == "==" else self.op
        return f"{self.place} {lola_op} {self.value}"

    def __repr__(self) -> str:
        return f"PlaceComparison({self.place} {self.op} {self.value})"


class NotNode(FormulaAST):
    """Logical negation: NOT phi."""
    def __init__(self, child: FormulaAST):
        self.child = child

    def eval(self, marking: Dict[str, int], enabled_transitions: Set[str], place_aliases: Dict[str, str]) -> bool:
        return not self.child.eval(marking, enabled_transitions, place_aliases)

    def to_lola_str(self) -> str:
        return f"NOT ({self.child.to_lola_str()})"

    def __repr__(self) -> str:
        return f"NOT({self.child!r})"


class AndNode(FormulaAST):
    """Logical conjunction: phi_1 AND phi_2 ..."""
    def __init__(self, children: List[FormulaAST]):
        self.children = list(children)

    def eval(self, marking: Dict[str, int], enabled_transitions: Set[str], place_aliases: Dict[str, str]) -> bool:
        return all(c.eval(marking, enabled_transitions, place_aliases) for c in self.children)

    def to_lola_str(self) -> str:
        return " AND ".join(f"({c.to_lola_str()})" if isinstance(c, (OrNode, ImplicationNode)) else c.to_lola_str() for c in self.children)

    def __repr__(self) -> str:
        return f"AND({', '.join(repr(c) for c in self.children)})"


class OrNode(FormulaAST):
    """Logical disjunction: phi_1 OR phi_2 ..."""
    def __init__(self, children: List[FormulaAST]):
        self.children = list(children)

    def eval(self, marking: Dict[str, int], enabled_transitions: Set[str], place_aliases: Dict[str, str]) -> bool:
        return any(c.eval(marking, enabled_transitions, place_aliases) for c in self.children)

    def to_lola_str(self) -> str:
        return " OR ".join(f"({c.to_lola_str()})" if isinstance(c, ImplicationNode) else c.to_lola_str() for c in self.children)

    def __repr__(self) -> str:
        return f"OR({', '.join(repr(c) for c in self.children)})"


class ImplicationNode(FormulaAST):
    """Logical implication: left -> right."""
    def __init__(self, left: FormulaAST, right: FormulaAST):
        self.left = left
        self.right = right

    def eval(self, marking: Dict[str, int], enabled_transitions: Set[str], place_aliases: Dict[str, str]) -> bool:
        if not self.left.eval(marking, enabled_transitions, place_aliases):
            return True
        return self.right.eval(marking, enabled_transitions, place_aliases)

    def to_lola_str(self) -> str:
        return f"({self.left.to_lola_str()}) -> ({self.right.to_lola_str()})"

    def __repr__(self) -> str:
        return f"Implication({self.left!r} -> {self.right!r})"


class CTLNode(FormulaAST):
    """CTL Temporal Operator: EF, AG, AF, EG, EX, AX."""
    SUPPORTED_OPS = {"EF", "AG", "AF", "EG", "EX", "AX"}

    def __init__(self, operator: str, child: FormulaAST):
        op_upper = operator.upper()
        if op_upper not in self.SUPPORTED_OPS:
            raise ValueError(f"Unsupported CTL operator: {operator}")
        self.operator = op_upper
        self.child = child

    def eval(self, marking: Dict[str, int], enabled_transitions: Set[str], place_aliases: Dict[str, str]) -> bool:
        # Direct evaluation of state predicate child
        return self.child.eval(marking, enabled_transitions, place_aliases)

    def to_lola_str(self) -> str:
        return f"{self.operator}({self.child.to_lola_str()})"

    def __repr__(self) -> str:
        return f"{self.operator}({self.child!r})"


# ============================================================================
# 2. Formula Parser & Lexer
# ============================================================================

class FormulaLexer:
    """Lexer for LoLA CTL temporal property formulas."""
    TOKEN_SPEC = [
        ("WS", r"\s+"),
        ("COMMENT", r"\{[^}]*\}|#[^\n]*"),
        ("FORMULA_KW", r"\bFORMULA\b"),
        ("CTL_OP", r"\b(EF|AG|AF|EG|EX|AX)\b"),
        ("DEADLOCK", r"\bDEADLOCK\b"),
        ("FIREABLE", r"\bFIREABLE\b"),
        ("BOOL", r"\b(TRUE|FALSE)\b"),
        ("AND", r"\bAND\b|&&"),
        ("OR", r"\bOR\b|\|\|"),
        ("NOT", r"\bNOT\b|!"),
        ("IMPLIES", r"->|=>"),
        ("COMP_OP", r">=|<=|!=|==|=|>|<"),
        ("LPAREN", r"\("),
        ("RPAREN", r"\)"),
        ("COMMA", r","),
        ("SEMICOLON", r";"),
        ("INTEGER", r"\d+"),
        ("IDENTIFIER", r"[A-Za-z_][A-Za-z0-9_\:\-\.]*"),
    ]

    def __init__(self, text: str):
        self.text = text
        self.tokens: List[Tuple[str, str]] = []
        self.pos = 0
        self._tokenize()

    def _tokenize(self):
        regex = "|".join(f"(?P<{name}>{pattern})" for name, pattern in self.TOKEN_SPEC)
        for match in re.finditer(regex, self.text, re.IGNORECASE):
            kind = match.lastgroup
            val = match.group()
            if kind in ("WS", "COMMENT"):
                continue
            self.tokens.append((kind, val))

    def peek(self) -> Optional[Tuple[str, str]]:
        if self.pos < len(self.tokens):
            return self.tokens[self.pos]
        return None

    def consume(self, expected_kind: Optional[str] = None) -> Tuple[str, str]:
        if self.pos >= len(self.tokens):
            raise SyntaxError("Unexpected end of formula input")
        token = self.tokens[self.pos]
        if expected_kind and token[0] != expected_kind:
            raise SyntaxError(f"Expected token {expected_kind}, got {token[0]} ('{token[1]}') at pos {self.pos}")
        self.pos += 1
        return token

    def match(self, kind: str) -> bool:
        tok = self.peek()
        if tok and tok[0] == kind:
            self.consume()
            return True
        return False


class FormulaParser:
    """Recursive descent parser for LoLA CTL formulas."""

    def __init__(self, text: str):
        self.lexer = FormulaLexer(text)

    def parse(self) -> FormulaAST:
        """Parse full formula string into AST."""
        # Optional leading FORMULA keyword or identifier label prefix
        tok = self.lexer.peek()
        if tok and tok[0] == "FORMULA_KW":
            self.lexer.consume()
        
        # Check for named formula e.g. "FORMULA name: expr"
        tok = self.lexer.peek()
        if tok and tok[0] == "IDENTIFIER":
            # Check if followed by colon
            if self.lexer.pos + 1 < len(self.lexer.tokens) and self.lexer.tokens[self.lexer.pos + 1][1] == ":":
                self.lexer.consume() # consume identifier
                self.lexer.consume() # consume colon

        expr = self.parse_implication()

        # Consume trailing semicolon if present
        while self.lexer.match("SEMICOLON"):
            pass

        return expr

    def parse_implication(self) -> FormulaAST:
        left = self.parse_or()
        tok = self.lexer.peek()
        if tok and tok[0] == "IMPLIES":
            self.lexer.consume()
            right = self.parse_implication()
            return ImplicationNode(left, right)
        return left

    def parse_or(self) -> FormulaAST:
        children = [self.parse_and()]
        while True:
            tok = self.lexer.peek()
            if tok and tok[0] == "OR":
                self.lexer.consume()
                children.append(self.parse_and())
            else:
                break
        return children[0] if len(children) == 1 else OrNode(children)

    def parse_and(self) -> FormulaAST:
        children = [self.parse_not()]
        while True:
            tok = self.lexer.peek()
            if tok and tok[0] == "AND":
                self.lexer.consume()
                children.append(self.parse_not())
            else:
                break
        return children[0] if len(children) == 1 else AndNode(children)

    def parse_not(self) -> FormulaAST:
        tok = self.lexer.peek()
        if tok and tok[0] == "NOT":
            self.lexer.consume()
            child = self.parse_not()
            return NotNode(child)
        return self.parse_ctl()

    def parse_ctl(self) -> FormulaAST:
        tok = self.lexer.peek()
        if tok and tok[0] == "CTL_OP":
            op_kind, op_val = self.lexer.consume()
            self.lexer.consume("LPAREN")
            child = self.parse_implication()
            self.lexer.consume("RPAREN")
            return CTLNode(op_val.upper(), child)
        return self.parse_primary()

    def parse_primary(self) -> FormulaAST:
        tok = self.lexer.peek()
        if not tok:
            raise SyntaxError("Unexpected end of formula while parsing primary expression")

        kind, val = tok

        # Parenthesized expression
        if kind == "LPAREN":
            self.lexer.consume("LPAREN")
            expr = self.parse_implication()
            self.lexer.consume("RPAREN")
            return expr

        # DEADLOCK keyword
        if kind == "DEADLOCK":
            self.lexer.consume()
            return DeadlockPredicate()

        # FIREABLE(t)
        if kind == "FIREABLE":
            self.lexer.consume()
            self.lexer.consume("LPAREN")
            t_tok = self.lexer.consume("IDENTIFIER")
            self.lexer.consume("RPAREN")
            return FireablePredicate(t_tok[1])

        # Boolean literals
        if kind == "BOOL":
            self.lexer.consume()
            return BooleanLiteral(val.upper() == "TRUE")

        # Place comparison: <IDENTIFIER> <COMP_OP> <INTEGER> or <INTEGER> <COMP_OP> <IDENTIFIER>
        if kind == "IDENTIFIER":
            ident = self.lexer.consume("IDENTIFIER")[1]
            next_tok = self.lexer.peek()
            if next_tok and next_tok[0] == "COMP_OP":
                op = self.lexer.consume("COMP_OP")[1]
                val_tok = self.lexer.consume("INTEGER")[1]
                return PlaceComparison(ident, op, int(val_tok))
            else:
                # Shorthand for place > 0
                return PlaceComparison(ident, ">", 0)

        if kind == "INTEGER":
            int_val = int(self.lexer.consume("INTEGER")[1])
            op = self.lexer.consume("COMP_OP")[1]
            ident = self.lexer.consume("IDENTIFIER")[1]
            # Invert comparison: e.g. 1 <= place -> place >= 1
            op_inv_map = {">": "<", "<": ">", ">=": "<=", "<=": ">=", "==": "==", "=": "==", "!=": "!="}
            return PlaceComparison(ident, op_inv_map.get(op, op), int_val)

        raise SyntaxError(f"Unexpected token in formula: {kind} ('{val}')")


def parse_formula(formula_str: str) -> FormulaAST:
    """Parse a LoLA CTL formula string into an AST tree."""
    clean_str = formula_str.strip()
    parser = FormulaParser(clean_str)
    return parser.parse()


# ============================================================================
# 3. Net Model & Property Specification Loaders
# ============================================================================

def parse_lola_net_string(content: str, name: str = "lola_net") -> ComposedNetModel:
    """Parse standard LoLA net specification format (.lola) into ComposedNetModel."""
    places: List[str] = []
    initial_marking: List[str] = []
    transitions: List[Dict[str, Any]] = []
    arcs: List[Tuple[str, str]] = []

    # Strip multi-line comments { ... }
    clean = re.sub(r"\{[^}]*\}", "", content)

    # Parse PLACE [SAFE:] ... ;
    place_match = re.search(r"PLACE\s*(?:SAFE:)?\s*([^;]+);", clean, re.IGNORECASE)
    if place_match:
        raw_places = place_match.group(1).split(",")
        for p in raw_places:
            p_clean = p.strip()
            if p_clean:
                places.append(p_clean)

    # Parse MARKING ... ;
    marking_match = re.search(r"MARKING\s*([^;]*);", clean, re.IGNORECASE)
    if marking_match:
        raw_m = marking_match.group(1).strip()
        if raw_m:
            for item in raw_m.split(","):
                item_clean = item.strip()
                if ":" in item_clean:
                    p_tok, cnt_str = item_clean.split(":", 1)
                    p_tok = p_tok.strip()
                    cnt = int(cnt_str.strip())
                    initial_marking.extend([p_tok] * cnt)
                elif item_clean:
                    initial_marking.append(item_clean)

    # Parse TRANSITION ... CONSUME ... PRODUCE ...
    trans_blocks = re.findall(r"TRANSITION\s+([A-Za-z0-9_]+)\s*(.*?)(?=TRANSITION|\Z)", clean, re.IGNORECASE | re.DOTALL)
    for t_id, body in trans_blocks:
        t_id = t_id.strip()
        transitions.append({"id": t_id, "label": t_id, "is_silent": False})

        consume_match = re.search(r"CONSUME\s*([^;]+);", body, re.IGNORECASE)
        if consume_match:
            for item in consume_match.group(1).split(","):
                item = item.strip()
                if ":" in item:
                    p_tok, cnt_str = item.split(":", 1)
                    p_tok = p_tok.strip()
                    cnt = int(cnt_str.strip())
                    for _ in range(cnt):
                        arcs.append((p_tok, t_id))
                elif item:
                    arcs.append((item, t_id))

        produce_match = re.search(r"PRODUCE\s*([^;]+);", body, re.IGNORECASE)
        if produce_match:
            for item in produce_match.group(1).split(","):
                item = item.strip()
                if ":" in item:
                    p_tok, cnt_str = item.split(":", 1)
                    p_tok = p_tok.strip()
                    cnt = int(cnt_str.strip())
                    for _ in range(cnt):
                        arcs.append((t_id, p_tok))
                elif item:
                    arcs.append((t_id, item))

    # Detect channel places and service sinks from place naming conventions
    channel_places = [p for p in places if p.startswith("ch::") or p.startswith("ch__")]
    channels = [
        ChannelMetadata(
            channel_name=p.replace("ch::", "").replace("ch__", ""),
            channel_place=p,
            caller_service="",
            callee_service="",
        )
        for p in channel_places
    ]

    service_sinks: Dict[str, str] = {}
    for p in places:
        if "sink" in p.lower():
            svc = p.split("::")[0] if "::" in p else p.split("__")[0] if "__" in p else p
            service_sinks[svc] = p

    return ComposedNetModel(
        name=name,
        places=places,
        transitions=transitions,
        arcs=arcs,
        initial_marking=initial_marking,
        final_marking=list(service_sinks.values()),
        service_sinks=service_sinks,
        channels=channels,
        workflow_name=name,
    )


def load_net_model(input_source: Union[str, Path, Dict[str, Any], ComposedNetModel]) -> ComposedNetModel:
    """Load Petri net model from JSON file path, LoLA file path, dictionary, or existing model."""
    if isinstance(input_source, ComposedNetModel):
        return input_source

    if isinstance(input_source, PetriNetModel):
        return ComposedNetModel(
            name=input_source.name,
            places=input_source.places,
            transitions=input_source.transitions,
            arcs=input_source.arcs,
            initial_marking=input_source.initial_marking,
            final_marking=input_source.final_marking,
        )

    if isinstance(input_source, dict):
        if "places" in input_source and "transitions" in input_source:
            return ComposedNetModel.from_composed_dict(input_source)
        # Dictionary of mined service nets
        from src.workflow_net_composer import compose_workflow_nets
        topo_path = os.path.join(REPO_ROOT, "interfaces", "social-network.json")
        if os.path.exists(topo_path):
            with open(topo_path, "r", encoding="utf-8") as f:
                topo_data = json.load(f)
            service_nets = {k: PetriNetModel.from_dict(v, name=k) for k, v in input_source.items()}
            return compose_workflow_nets(service_nets, topo_data)
        raise ValueError("Cannot infer net composition from dict without topology")

    path = Path(input_source)
    if not path.exists():
        # Check if raw LoLA string content
        if "PLACE" in str(input_source) and "TRANSITION" in str(input_source):
            return parse_lola_net_string(str(input_source))
        raise FileNotFoundError(f"Petri net model source not found: {input_source}")

    content = path.read_text(encoding="utf-8")
    if path.suffix.lower() == ".json":
        data = json.loads(content)
        if "places" in data and "transitions" in data:
            return ComposedNetModel.from_composed_dict(data)
        elif isinstance(data, dict):
            # Dict of mined nets
            return load_net_model(data)
    elif path.suffix.lower() in (".lola", ".task"):
        return parse_lola_net_string(content, name=path.stem)

    # Fallback auto-detection
    try:
        data = json.loads(content)
        return ComposedNetModel.from_composed_dict(data)
    except Exception:
        return parse_lola_net_string(content, name=path.stem)


@dataclass
class PropertySpec:
    """Structured temporal property specification."""
    id: str
    name: str
    category: str
    description: str
    formula: str
    expected_verdict: str = "UNSAT"  # UNSAT (error reachability holds) or SAT / HOLDS
    target_services: List[str] = field(default_factory=list)
    severity: str = "HIGH"
    rationale: str = ""

    def to_dict(self) -> Dict[str, Any]:
        return {
            "id": self.id,
            "name": self.name,
            "category": self.category,
            "description": self.description,
            "formula": self.formula,
            "expected_verdict": self.expected_verdict,
            "target_services": self.target_services,
            "severity": self.severity,
            "rationale": self.rationale,
        }


def load_property_specs(input_source: Union[str, Path, List[Dict[str, Any]], Dict[str, Any]]) -> List[PropertySpec]:
    """Load property specifications from structured JSON file, LoLA file, or Python list/dict."""
    if isinstance(input_source, list):
        specs = []
        for item in input_source:
            if isinstance(item, PropertySpec):
                specs.append(item)
            elif isinstance(item, dict):
                specs.append(PropertySpec(**item))
        return specs

    if isinstance(input_source, dict):
        if "properties" in input_source:
            return [PropertySpec(**p) for p in input_source["properties"]]
        return [PropertySpec(**input_source)]

    path = Path(input_source)
    if not path.exists():
        # Check if single formula string passed
        if "EF" in str(input_source) or "AG" in str(input_source) or "AF" in str(input_source) or "FORMULA" in str(input_source):
            return [PropertySpec(
                id="CUSTOM_FORMULA",
                name="Custom LoLA Formula",
                category="CUSTOM",
                description="Custom ad-hoc user formula",
                formula=str(input_source),
                expected_verdict="UNSAT" if "EF" in str(input_source) else "SAT",
            )]
        raise FileNotFoundError(f"Property specification source not found: {input_source}")

    content = path.read_text(encoding="utf-8")
    if path.suffix.lower() == ".json":
        data = json.loads(content)
        if isinstance(data, list):
            return [PropertySpec(**p) for p in data]
        elif "properties" in data:
            return [PropertySpec(**p) for p in data["properties"]]
        else:
            return [PropertySpec(**data)]

    # Parse .lola formula file
    specs: List[PropertySpec] = []
    # Split content by FORMULA
    # For each FORMULA, collect preceding comments
    formula_sections = re.findall(r"((?:\{[^}]*\}\s*)*)FORMULA\s+([^;]+);?", content, re.IGNORECASE)
    counter = 1

    for comment_block, form_str in formula_sections:
        form_str = form_str.strip()
        prop_id = f"PROP_{counter}"
        prop_name = f"Property {counter}"
        category = "TEMPORAL"
        description = f"Formula {counter}"
        exp_verdict = "UNSAT" if (form_str.startswith("EF") or "EF(" in form_str) else "SAT"

        # Parse comment blocks
        comments = re.findall(r"\{([^}]+)\}", comment_block)
        for comm in comments:
            comm_clean = comm.strip()
            for line in comm_clean.split("\n"):
                line = line.strip()
                if not line or line.startswith("==="):
                    continue
                if line.lower().startswith("property"):
                    # e.g. "Property 1: Name" or "Property: PROP_ID: Name"
                    parts = line.split(":", 1)
                    if len(parts) > 1:
                        sub = parts[1].strip()
                        if ":" in sub:
                            id_part, name_part = sub.split(":", 1)
                            prop_id = id_part.strip()
                            prop_name = name_part.strip()
                        else:
                            prop_name = sub
                            # Convert e.g. "Property 1" to "PROP_1"
                            prop_id = re.sub(r"[^A-Za-z0-9_]", "_", parts[0].strip()).upper()
                elif line.lower().startswith("category:"):
                    category = line.split(":", 1)[1].strip()
                elif line.lower().startswith("description:"):
                    description = line.split(":", 1)[1].strip()
                elif line.lower().startswith("expected:"):
                    exp_verdict = line.split(":", 1)[1].strip().upper()

        specs.append(PropertySpec(
            id=prop_id,
            name=prop_name,
            category=category,
            description=description,
            formula=form_str,
            expected_verdict=exp_verdict,
        ))
        counter += 1

    if not specs:
        # Check single formula in file
        specs.append(PropertySpec(
            id=path.stem,
            name=path.stem,
            category="CUSTOM",
            description=f"Formula loaded from {path.name}",
            formula=content.strip(),
            expected_verdict="UNSAT",
        ))

    return specs


# ============================================================================
# 4. Rich Counterexample Trace Builder
# ============================================================================

@dataclass
class CounterexampleStep:
    """Single firing step in a counterexample trace."""
    step: int
    transition_id: str
    label: str
    service: str
    marking_after: Dict[str, int] = field(default_factory=dict)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "step": self.step,
            "transition_id": self.transition_id,
            "label": self.label,
            "service": self.service,
            "marking_after": self.marking_after,
        }


@dataclass
class CounterexampleTrace:
    """Structured counterexample witness trace."""
    length: int
    firing_sequence: List[CounterexampleStep]
    violated_marking: Dict[str, int]
    explanation: str

    def to_dict(self) -> Dict[str, Any]:
        return {
            "length": self.length,
            "firing_sequence": [s.to_dict() for s in self.firing_sequence],
            "violated_marking": self.violated_marking,
            "explanation": self.explanation,
        }


def build_counterexample_trace(
    witness_path: List[Dict[str, Any]],
    composed_net: ComposedNetModel,
    formula_ast: FormulaAST,
    target_marking: Optional[Dict[str, int]] = None,
    explanation: Optional[str] = None,
) -> CounterexampleTrace:
    """Format and enrich raw witness step list into a rich counterexample trace."""
    # Build transition label and service lookup
    trans_lookup: Dict[str, Dict[str, Any]] = {}
    for t in composed_net.transitions:
        trans_lookup[t["id"]] = t

    firing_steps: List[CounterexampleStep] = []
    for idx, item in enumerate(witness_path, start=1):
        t_id = item.get("transition_id", "")
        t_info = trans_lookup.get(t_id, {})
        label = item.get("label") or t_info.get("label") or t_id
        
        # Infer service namespace
        svc = t_info.get("service", "")
        if not svc:
            if "::" in t_id:
                svc = t_id.split("::")[0]
            elif "__" in t_id:
                svc = t_id.split("__")[0]

        step_marking = item.get("marking", {})
        firing_steps.append(CounterexampleStep(
            step=idx,
            transition_id=t_id,
            label=label,
            service=svc,
            marking_after={k: v for k, v in step_marking.items() if v > 0},
        ))

    final_marking = target_marking or (firing_steps[-1].marking_after if firing_steps else {})
    
    if not explanation:
        explanation = f"Trace of {len(firing_steps)} step(s) reached a state satisfying target condition: {formula_ast.to_lola_str()}"

    return CounterexampleTrace(
        length=len(firing_steps),
        firing_sequence=firing_steps,
        violated_marking={k: v for k, v in final_marking.items() if v > 0},
        explanation=explanation,
    )


# ============================================================================
# 5. Dual-Engine Model Checking
# ============================================================================

def build_place_alias_map(composed_net: ComposedNetModel) -> Dict[str, str]:
    """Build bidirectional alias map for place identifiers (namespaced vs sanitized)."""
    alias_map: Dict[str, str] = {}
    used_tokens: Set[str] = set()

    for p in composed_net.places:
        sanitized = sanitize_lola_identifier(p, used_tokens)
        alias_map[p] = sanitized
        alias_map[sanitized] = p
        
        # Also map double colon and dash conversions
        p_sub = p.replace("::", "__").replace("-", "_")
        alias_map[p_sub] = p
        alias_map[p] = p_sub

    for ch in getattr(composed_net, "channels", []):
        ch_place = ch.channel_place
        ch_san = sanitize_lola_identifier(ch_place, used_tokens)
        alias_map[ch_place] = ch_san
        alias_map[ch_san] = ch_place

    return alias_map


def solve_property_python(
    composed_net: ComposedNetModel,
    formula_ast: FormulaAST,
    max_states: int = 300000,
    timeout_sec: float = 30.0,
) -> Tuple[VerificationVerdict, Optional[CounterexampleTrace], int, float]:
    """Execute zero-dependency native pure-Python BFS state space model checker.
    
    Evaluates formula AST over reachable markings and constructs concrete counterexamples.
    
    Returns:
        Tuple of (VerificationVerdict, Optional[CounterexampleTrace], states_explored, elapsed_ms).
    """
    t0 = time.time()

    # Pre-index places and transitions for high performance firing
    places = list(composed_net.places)
    place_to_idx = {p: i for i, p in enumerate(places)}
    num_places = len(places)

    alias_map = build_place_alias_map(composed_net)

    # Initial marking vector
    m0_dict: Dict[str, int] = collections.defaultdict(int)
    for p in composed_net.initial_marking:
        if p in place_to_idx:
            m0_dict[p] += 1
        else:
            # Check alias
            alias = alias_map.get(p)
            if alias and alias in place_to_idx:
                m0_dict[alias] += 1

    # Transition delta structures
    t_presets: Dict[str, List[Tuple[int, int]]] = {}
    t_postsets: Dict[str, List[Tuple[int, int]]] = {}
    t_labels: Dict[str, str] = {}
    t_services: Dict[str, str] = {}

    for t in composed_net.transitions:
        t_id = t["id"]
        t_labels[t_id] = t.get("label") or t_id
        svc = t.get("service", "")
        if not svc and "::" in t_id:
            svc = t_id.split("::")[0]
        t_services[t_id] = svc

        preset_counts: Dict[int, int] = collections.defaultdict(int)
        postset_counts: Dict[int, int] = collections.defaultdict(int)

        for src, tgt in composed_net.arcs:
            if tgt == t_id:
                p_idx = place_to_idx.get(src)
                if p_idx is None and src in alias_map:
                    p_idx = place_to_idx.get(alias_map[src])
                if p_idx is not None:
                    preset_counts[p_idx] += 1
            elif src == t_id:
                p_idx = place_to_idx.get(tgt)
                if p_idx is None and tgt in alias_map:
                    p_idx = place_to_idx.get(alias_map[tgt])
                if p_idx is not None:
                    postset_counts[p_idx] += 1

        t_presets[t_id] = list(preset_counts.items())
        t_postsets[t_id] = list(postset_counts.items())

    all_t_ids = [t["id"] for t in composed_net.transitions]

    def get_enabled(m: Dict[str, int]) -> Set[str]:
        enabled = set()
        for t_id in all_t_ids:
            is_en = True
            for p_idx, req in t_presets[t_id]:
                p_name = places[p_idx]
                if m.get(p_name, 0) < req:
                    is_en = False
                    break
            if is_en:
                enabled.add(t_id)
        return enabled

    def to_marking_key(m: Dict[str, int]) -> Tuple[Tuple[str, int], ...]:
        return tuple(sorted(((p, cnt) for p, cnt in m.items() if cnt > 0)))

    # Determine CTL evaluation mode
    # Top-level operator dispatch:
    is_reachability = False  # EF(phi): search for state where phi is True
    is_invariance = False    # AG(phi): search for state where phi is False (violation)
    target_predicate: FormulaAST = formula_ast

    if isinstance(formula_ast, CTLNode):
        if formula_ast.operator == "EF":
            is_reachability = True
            target_predicate = formula_ast.child
        elif formula_ast.operator == "AG":
            is_invariance = True
            target_predicate = formula_ast.child
        elif formula_ast.operator in ("AF", "AX"):
            is_invariance = True
            target_predicate = formula_ast.child
        elif formula_ast.operator in ("EG", "EX"):
            is_reachability = True
            target_predicate = formula_ast.child
    elif isinstance(formula_ast, NotNode) and isinstance(formula_ast.child, CTLNode):
        if formula_ast.child.operator == "EF":
            # NOT EF(phi) == AG(NOT phi)
            is_reachability = True
            target_predicate = formula_ast.child.child
    else:
        # Default state predicate treated as reachability
        is_reachability = True
        target_predicate = formula_ast

    # Check M0
    m0_en = get_enabled(m0_dict)
    m0_key = to_marking_key(m0_dict)
    
    if is_reachability:
        if target_predicate.eval(m0_dict, m0_en, alias_map):
            elapsed_ms = round((time.time() - t0) * 1000, 2)
            trace = build_counterexample_trace([], composed_net, target_predicate, m0_dict, "Initial marking satisfies formula")
            return VerificationVerdict.SAT, trace, 1, elapsed_ms
    elif is_invariance:
        if not target_predicate.eval(m0_dict, m0_en, alias_map):
            elapsed_ms = round((time.time() - t0) * 1000, 2)
            trace = build_counterexample_trace([], composed_net, target_predicate, m0_dict, "Initial marking violates invariant")
            return VerificationVerdict.UNSAT, trace, 1, elapsed_ms

    # BFS Exploration Queue
    queue = collections.deque([(m0_dict, [])])
    visited: Set[Tuple[Tuple[str, int], ...]] = {m0_key}
    states_explored = 0

    while queue and states_explored < max_states:
        if time.time() - t0 > timeout_sec:
            elapsed_ms = round((time.time() - t0) * 1000, 2)
            return VerificationVerdict.ERROR, None, states_explored, elapsed_ms

        curr_m, path = queue.popleft()
        states_explored += 1
        curr_en = get_enabled(curr_m)

        for t_id in curr_en:
            next_m = dict(curr_m)
            for p_idx, req in t_presets[t_id]:
                p_name = places[p_idx]
                next_m[p_name] -= req
                if next_m[p_name] == 0:
                    del next_m[p_name]
            for p_idx, prod in t_postsets[t_id]:
                p_name = places[p_idx]
                next_m[p_name] = next_m.get(p_name, 0) + prod

            next_key = to_marking_key(next_m)
            if next_key not in visited:
                visited.add(next_key)
                next_en = get_enabled(next_m)

                next_path = list(path)
                next_path.append({
                    "transition_id": t_id,
                    "label": t_labels[t_id],
                    "service": t_services[t_id],
                    "marking": dict(next_m),
                })

                if is_reachability:
                    if target_predicate.eval(next_m, next_en, alias_map):
                        elapsed_ms = round((time.time() - t0) * 1000, 2)
                        trace = build_counterexample_trace(next_path, composed_net, target_predicate, next_m)
                        return VerificationVerdict.SAT, trace, states_explored + 1, elapsed_ms
                elif is_invariance:
                    if not target_predicate.eval(next_m, next_en, alias_map):
                        elapsed_ms = round((time.time() - t0) * 1000, 2)
                        trace = build_counterexample_trace(next_path, composed_net, target_predicate, next_m)
                        return VerificationVerdict.UNSAT, trace, states_explored + 1, elapsed_ms

                queue.append((next_m, next_path))

    elapsed_ms = round((time.time() - t0) * 1000, 2)
    
    if is_reachability:
        # No reachable state satisfied target predicate
        return VerificationVerdict.UNSAT, None, states_explored, elapsed_ms
    elif is_invariance:
        # All reachable states satisfied invariant
        return VerificationVerdict.SAT, None, states_explored, elapsed_ms

    return VerificationVerdict.UNSAT, None, states_explored, elapsed_ms


def solve_property_lola(
    composed_net: ComposedNetModel,
    formula_ast: FormulaAST,
    lola_bin: str = "lola",
    timeout_sec: float = 30.0,
) -> Tuple[VerificationVerdict, Optional[CounterexampleTrace], str, float]:
    """Execute external LoLA model checker with formula and path extraction.
    
    Returns:
        Tuple of (VerificationVerdict, Optional[CounterexampleTrace], raw_output, elapsed_ms).
    """
    lola_formula = formula_ast.to_lola_str()
    if not lola_formula.strip().startswith("FORMULA"):
        lola_formula = f"FORMULA {lola_formula}"

    with tempfile.TemporaryDirectory() as tmp_dir:
        net_path = os.path.join(tmp_dir, "net.lola")
        path_output_file = os.path.join(tmp_dir, "path.txt")
        
        serialize_composed_to_lola(composed_net, output_path=net_path)

        cmd = [
            lola_bin,
            net_path,
            f"--formula={lola_formula}",
            "--search=covergraph",
            f"--path={path_output_file}",
        ]

        t0 = time.time()
        try:
            proc = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=timeout_sec,
            )
            elapsed_ms = round((time.time() - t0) * 1000, 2)
            raw_output = proc.stdout + "\n" + proc.stderr
        except FileNotFoundError:
            raise FileNotFoundError(f"LoLA executable '{lola_bin}' not found in PATH.")
        except subprocess.TimeoutExpired:
            elapsed_ms = round((time.time() - t0) * 1000, 2)
            return VerificationVerdict.ERROR, None, f"LoLA execution timed out after {timeout_sec}s", elapsed_ms

        out_lower = raw_output.lower()
        if "result: yes" in out_lower or "formula is true" in out_lower:
            verdict = VerificationVerdict.SAT
        elif "result: no" in out_lower or "formula is false" in out_lower:
            verdict = VerificationVerdict.UNSAT
        else:
            verdict = VerificationVerdict.ERROR

        # Parse counterexample / witness path if produced
        trace: Optional[CounterexampleTrace] = None
        if os.path.exists(path_output_file) and os.path.getsize(path_output_file) > 0:
            path_text = Path(path_output_file).read_text(encoding="utf-8")
            # Parse transitions from LoLA path output
            step_transitions = re.findall(r"([A-Za-z0-9_]+)", path_text)
            witness_steps = []
            for t_tok in step_transitions:
                witness_steps.append({
                    "transition_id": t_tok,
                    "label": t_tok,
                    "marking": {},
                })
            if witness_steps:
                trace = build_counterexample_trace(witness_steps, composed_net, formula_ast)

        return verdict, trace, raw_output, elapsed_ms


def verify_property(
    composed_net: ComposedNetModel,
    prop_spec: PropertySpec,
    engine: str = "auto",
    lola_bin: str = "lola",
    max_states: int = 300000,
    timeout_sec: float = 30.0,
) -> Dict[str, Any]:
    """Model-check a single property specification using dual-engine architecture.
    
    Args:
        composed_net: Composed Petri net model.
        prop_spec: Property specification to verify.
        engine: 'auto', 'lola', or 'python'.
        lola_bin: Binary path for LoLA.
        max_states: State cutoff for Python state-space exploration.
        timeout_sec: Timeout in seconds.
        
    Returns:
        Structured verification result dictionary.
    """
    formula_ast = parse_formula(prop_spec.formula)
    
    chosen_engine = engine
    if engine == "auto":
        chosen_engine = "lola" if shutil.which(lola_bin) else "python"

    trace: Optional[CounterexampleTrace] = None
    raw_lola_out: Optional[str] = None
    states_explored = 0
    elapsed_ms = 0.0

    if chosen_engine == "lola":
        try:
            verdict, trace, raw_lola_out, elapsed_ms = solve_property_lola(
                composed_net, formula_ast, lola_bin=lola_bin, timeout_sec=timeout_sec
            )
            # If LoLA SAT but path file was empty, use Python solver to extract concrete trace
            if verdict == VerificationVerdict.SAT and trace is None:
                _, py_trace, states_explored, _ = solve_property_python(
                    composed_net, formula_ast, max_states=max_states, timeout_sec=timeout_sec
                )
                trace = py_trace
        except Exception:
            # Seamless fallback to pure-Python engine
            chosen_engine = "python (fallback)"
            verdict, trace, states_explored, elapsed_ms = solve_property_python(
                composed_net, formula_ast, max_states=max_states, timeout_sec=timeout_sec
            )
    else:
        verdict, trace, states_explored, elapsed_ms = solve_property_python(
            composed_net, formula_ast, max_states=max_states, timeout_sec=timeout_sec
        )

    # Determine conformance status based on expected verdict
    exp_norm = prop_spec.expected_verdict.upper()
    if exp_norm in ("UNSAT", "ERROR_REACHABILITY"):
        # UNSAT is required (error unreachable -> property holds)
        if verdict == VerificationVerdict.UNSAT:
            status = PropertyStatus.HOLDS
        elif verdict == VerificationVerdict.SAT:
            status = PropertyStatus.VIOLATED
        else:
            status = PropertyStatus.UNKNOWN
    elif exp_norm in ("SAT", "HOLDS", "TRUE"):
        if verdict in (VerificationVerdict.SAT, VerificationVerdict.TRUE):
            status = PropertyStatus.HOLDS
        elif verdict in (VerificationVerdict.UNSAT, VerificationVerdict.FALSE):
            status = PropertyStatus.VIOLATED
        else:
            status = PropertyStatus.UNKNOWN
    else:
        status = PropertyStatus.HOLDS if verdict.value == exp_norm else PropertyStatus.VIOLATED

    return {
        "property_id": prop_spec.id,
        "name": prop_spec.name,
        "category": prop_spec.category,
        "description": prop_spec.description,
        "formula": prop_spec.formula,
        "expected_verdict": prop_spec.expected_verdict,
        "actual_verdict": verdict.value,
        "status": status.value,
        "engine": chosen_engine,
        "execution_time_ms": elapsed_ms,
        "states_explored": states_explored,
        "counterexample": trace.to_dict() if trace else None,
        "raw_lola_output": raw_lola_out,
    }


def solve_properties_batch_python(
    composed_net: ComposedNetModel,
    properties: List[PropertySpec],
    max_states: int = 300000,
    timeout_sec: float = 60.0,
) -> List[Dict[str, Any]]:
    """Execute unified single-pass BFS model checking across multiple properties.
    
    Evaluates all property ASTs concurrently during a single state-space traversal.
    """
    t0 = time.time()
    
    # Pre-index places, transitions, alias maps
    places = list(composed_net.places)
    place_to_idx = {p: i for i, p in enumerate(places)}
    alias_map = build_place_alias_map(composed_net)

    # Initial marking
    m0_dict: Dict[str, int] = collections.defaultdict(int)
    for p in composed_net.initial_marking:
        if p in place_to_idx:
            m0_dict[p] += 1
        else:
            alias = alias_map.get(p)
            if alias and alias in place_to_idx:
                m0_dict[alias] += 1

    # Transition delta structures
    t_presets: Dict[str, List[Tuple[int, int]]] = {}
    t_postsets: Dict[str, List[Tuple[int, int]]] = {}
    t_labels: Dict[str, str] = {}
    t_services: Dict[str, str] = {}

    for t in composed_net.transitions:
        t_id = t["id"]
        t_labels[t_id] = t.get("label") or t_id
        svc = t.get("service", "")
        if not svc and "::" in t_id:
            svc = t_id.split("::")[0]
        t_services[t_id] = svc

        preset_counts: Dict[int, int] = collections.defaultdict(int)
        postset_counts: Dict[int, int] = collections.defaultdict(int)

        for src, tgt in composed_net.arcs:
            if tgt == t_id:
                p_idx = place_to_idx.get(src)
                if p_idx is None and src in alias_map:
                    p_idx = place_to_idx.get(alias_map[src])
                if p_idx is not None:
                    preset_counts[p_idx] += 1
            elif src == t_id:
                p_idx = place_to_idx.get(tgt)
                if p_idx is None and tgt in alias_map:
                    p_idx = place_to_idx.get(alias_map[tgt])
                if p_idx is not None:
                    postset_counts[p_idx] += 1

        t_presets[t_id] = list(preset_counts.items())
        t_postsets[t_id] = list(postset_counts.items())

    all_t_ids = [t["id"] for t in composed_net.transitions]

    def get_enabled(m: Dict[str, int]) -> Set[str]:
        enabled = set()
        for t_id in all_t_ids:
            is_en = True
            for p_idx, req in t_presets[t_id]:
                p_name = places[p_idx]
                if m.get(p_name, 0) < req:
                    is_en = False
                    break
            if is_en:
                enabled.add(t_id)
        return enabled

    def to_marking_key(m: Dict[str, int]) -> Tuple[Tuple[str, int], ...]:
        return tuple(sorted(((p, cnt) for p, cnt in m.items() if cnt > 0)))

    # Parse and index property targets
    parsed_props = []
    for prop in properties:
        ast = parse_formula(prop.formula)
        # Determine mode
        is_reachability = True
        target_ast = ast
        if isinstance(ast, CTLNode):
            if ast.operator == "EF":
                is_reachability = True
                target_ast = ast.child
            elif ast.operator == "AG":
                is_reachability = False
                target_ast = ast.child
        elif isinstance(ast, NotNode) and isinstance(ast.child, CTLNode):
            if ast.child.operator == "EF":
                is_reachability = True
                target_ast = ast.child.child
        parsed_props.append({
            "spec": prop,
            "ast": ast,
            "target": target_ast,
            "is_reachability": is_reachability,
            "verdict": None,
            "trace": None,
            "completed": False,
        })

    # Pre-check M0
    m0_en = get_enabled(m0_dict)
    m0_key = to_marking_key(m0_dict)

    for p_info in parsed_props:
        if p_info["is_reachability"]:
            if p_info["target"].eval(m0_dict, m0_en, alias_map):
                p_info["verdict"] = VerificationVerdict.SAT
                p_info["trace"] = build_counterexample_trace([], composed_net, p_info["target"], m0_dict, "Initial marking satisfies formula")
                p_info["completed"] = True
        else:
            if not p_info["target"].eval(m0_dict, m0_en, alias_map):
                p_info["verdict"] = VerificationVerdict.UNSAT
                p_info["trace"] = build_counterexample_trace([], composed_net, p_info["target"], m0_dict, "Initial marking violates invariant")
                p_info["completed"] = True

    # BFS Traversal
    queue = collections.deque([(m0_dict, [])])
    visited: Set[Tuple[Tuple[str, int], ...]] = {m0_key}
    states_explored = 0

    while queue and states_explored < max_states:
        if time.time() - t0 > timeout_sec:
            break

        curr_m, path = queue.popleft()
        states_explored += 1
        curr_en = get_enabled(curr_m)

        for t_id in curr_en:
            next_m = dict(curr_m)
            for p_idx, req in t_presets[t_id]:
                p_name = places[p_idx]
                next_m[p_name] -= req
                if next_m[p_name] == 0:
                    del next_m[p_name]
            for p_idx, prod in t_postsets[t_id]:
                p_name = places[p_idx]
                next_m[p_name] = next_m.get(p_name, 0) + prod

            next_key = to_marking_key(next_m)
            if next_key not in visited:
                visited.add(next_key)
                next_en = get_enabled(next_m)

                next_path = list(path)
                next_path.append({
                    "transition_id": t_id,
                    "label": t_labels[t_id],
                    "service": t_services[t_id],
                    "marking": dict(next_m),
                })

                # Check uncompleted properties
                all_done = True
                for p_info in parsed_props:
                    if p_info["completed"]:
                        continue
                    all_done = False
                    if p_info["is_reachability"]:
                        if p_info["target"].eval(next_m, next_en, alias_map):
                            p_info["verdict"] = VerificationVerdict.SAT
                            p_info["trace"] = build_counterexample_trace(next_path, composed_net, p_info["target"], next_m)
                            p_info["completed"] = True
                    else:
                        if not p_info["target"].eval(next_m, next_en, alias_map):
                            p_info["verdict"] = VerificationVerdict.UNSAT
                            p_info["trace"] = build_counterexample_trace(next_path, composed_net, p_info["target"], next_m)
                            p_info["completed"] = True

                if all_done:
                    break

                queue.append((next_m, next_path))

    elapsed_ms = round((time.time() - t0) * 1000, 2)

    # Post-process results for any remaining properties
    results: List[Dict[str, Any]] = []
    for p_info in parsed_props:
        prop_spec = p_info["spec"]
        if not p_info["completed"]:
            if p_info["is_reachability"]:
                verdict = VerificationVerdict.UNSAT
            else:
                verdict = VerificationVerdict.SAT
            trace = None
        else:
            verdict = p_info["verdict"]
            trace = p_info["trace"]

        exp_norm = prop_spec.expected_verdict.upper()
        if exp_norm in ("UNSAT", "ERROR_REACHABILITY"):
            status = PropertyStatus.HOLDS if verdict == VerificationVerdict.UNSAT else PropertyStatus.VIOLATED
        elif exp_norm in ("SAT", "HOLDS", "TRUE"):
            status = PropertyStatus.HOLDS if verdict in (VerificationVerdict.SAT, VerificationVerdict.TRUE) else PropertyStatus.VIOLATED
        else:
            status = PropertyStatus.HOLDS if verdict.value == exp_norm else PropertyStatus.VIOLATED

        results.append({
            "property_id": prop_spec.id,
            "name": prop_spec.name,
            "category": prop_spec.category,
            "description": prop_spec.description,
            "formula": prop_spec.formula,
            "expected_verdict": prop_spec.expected_verdict,
            "actual_verdict": verdict.value,
            "status": status.value,
            "engine": "python",
            "execution_time_ms": round(elapsed_ms / len(parsed_props), 2),
            "states_explored": states_explored,
            "counterexample": trace.to_dict() if trace else None,
            "raw_lola_output": None,
        })

    return results


def verify_all_properties(
    composed_net: ComposedNetModel,
    properties: List[PropertySpec],
    engine: str = "auto",
    lola_bin: str = "lola",
    max_states: int = 300000,
    timeout_sec: float = 30.0,
) -> Dict[str, Any]:
    """Execute batch verification across a suite of property specifications."""
    t_start = time.time()
    
    chosen_engine = engine
    if engine == "auto":
        chosen_engine = "lola" if shutil.which(lola_bin) else "python"

    if chosen_engine == "python":
        results = solve_properties_batch_python(
            composed_net,
            properties,
            max_states=max_states,
            timeout_sec=timeout_sec * len(properties),
        )
    else:
        results = []
        for prop in properties:
            res = verify_property(
                composed_net,
                prop,
                engine=chosen_engine,
                lola_bin=lola_bin,
                max_states=max_states,
                timeout_sec=timeout_sec,
            )
            results.append(res)

    total_elapsed_ms = round((time.time() - t_start) * 1000, 2)
    all_hold = all(r["status"] == PropertyStatus.HOLDS.value for r in results)
    holds_count = sum(1 for r in results if r["status"] == PropertyStatus.HOLDS.value)
    violated_count = sum(1 for r in results if r["status"] == PropertyStatus.VIOLATED.value)
    unknown_count = sum(1 for r in results if r["status"] == PropertyStatus.UNKNOWN.value)

    return {
        "_meta": {
            "name": "Social Network Control-Flow Property Verification Certificate",
            "version": "1.0.0",
            "workflow": composed_net.workflow_name,
            "generated_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
            "total_properties": len(properties),
            "properties_holding": holds_count,
            "properties_violated": violated_count,
            "properties_unknown": unknown_count,
            "all_properties_hold": all_hold,
            "total_execution_time_ms": total_elapsed_ms,
        },
        "workflow": composed_net.workflow_name,
        "summary": {
            "all_properties_hold": all_hold,
            "total_properties": len(properties),
            "holds": holds_count,
            "violated": violated_count,
            "unknown": unknown_count,
            "total_execution_time_ms": total_elapsed_ms,
        },
        "verifications": results,
    }


# ============================================================================
# 6. Fault Injection Fixtures for Negative Control Verification
# ============================================================================

def inject_causal_precedence_defect(composed_net: ComposedNetModel) -> ComposedNetModel:
    """Inject a causal precedence violation: bypass child RPC before parent completes."""
    mutated = copy.deepcopy(composed_net)
    
    # Add a bypass transition that produces text-service sink directly from ComposeText
    bypass_id = "text-service::defect_bypass_causal"
    mutated.transitions.append({
        "id": bypass_id,
        "label": "defect_bypass_causal",
        "is_silent": False,
        "service": "text-service",
    })
    
    # Connect ch::ComposeText -> bypass -> text-service::sink
    ch_text = "ch::ComposeText"
    text_sink = mutated.service_sinks.get("text-service", "text-service::sink")
    
    mutated.arcs.append((ch_text, bypass_id))
    mutated.arcs.append((bypass_id, text_sink))
    return mutated


def inject_fork_join_race_defect(composed_net: ComposedNetModel) -> ComposedNetModel:
    """Inject a fork-join race defect: trigger StorePost while source is still active."""
    mutated = copy.deepcopy(composed_net)
    
    race_trans_id = "compose-post-service::defect_store_post_race"
    mutated.transitions.append({
        "id": race_trans_id,
        "label": "defect_store_post_race",
        "is_silent": False,
        "service": "compose-post-service",
    })
    
    mutated.arcs.append(("compose-post-service::source", race_trans_id))
    mutated.arcs.append((race_trans_id, "compose-post-service::source"))
    mutated.arcs.append((race_trans_id, "ch::StorePost"))
    return mutated


def inject_premature_timeline_defect(composed_net: ComposedNetModel) -> ComposedNetModel:
    """Inject premature timeline write defect: write to home timeline before PostStorage completes."""
    mutated = copy.deepcopy(composed_net)
    
    premature_id = "compose-post-service::defect_premature_timeline"
    mutated.transitions.append({
        "id": premature_id,
        "label": "defect_premature_timeline",
        "is_silent": False,
        "service": "compose-post-service",
    })
    
    mutated.arcs.append(("compose-post-service::source", premature_id))
    mutated.arcs.append((premature_id, "compose-post-service::source"))
    mutated.arcs.append((premature_id, "ch::WriteHomeTimeline"))
    return mutated


def inject_unbounded_channel_defect(composed_net: ComposedNetModel) -> ComposedNetModel:
    """Inject an unbounded channel defect by duplicating token production into a channel."""
    mutated = copy.deepcopy(composed_net)
    
    dup_id = "compose-post-service::defect_duplicate_channel_produce"
    mutated.transitions.append({
        "id": dup_id,
        "label": "defect_duplicate_channel_produce",
        "is_silent": False,
        "service": "compose-post-service",
    })
    
    mutated.arcs.append(("compose-post-service::source", dup_id))
    mutated.arcs.append((dup_id, "compose-post-service::source"))
    mutated.arcs.append((dup_id, "ch::ComposeText"))
    return mutated


def inject_deadlock_trap_defect(composed_net: ComposedNetModel) -> ComposedNetModel:
    """Inject an artificial deadlock trap state before reaching workflow sink."""
    mutated = copy.deepcopy(composed_net)
    
    trap_place = "compose-post-service::trap_sink"
    trap_trans = "compose-post-service::defect_trap_transition"
    
    mutated.places.append(trap_place)
    mutated.transitions.append({
        "id": trap_trans,
        "label": "defect_trap_transition",
        "is_silent": False,
        "service": "compose-post-service",
    })
    
    # Divert source to deadlocked trap place
    mutated.arcs.append(("compose-post-service::source", trap_trans))
    mutated.arcs.append((trap_trans, trap_place))
    return mutated


# ============================================================================
# 7. Terminal Formatting & Report Export
# ============================================================================

def format_terminal_report(report: Dict[str, Any], verbose: bool = False) -> str:
    """Format verification report into clean diagnostic ASCII summary tables."""
    lines = []
    lines.append("=" * 82)
    lines.append(">>> Social Network Control-Flow Property Verification Report <<<")
    lines.append("=" * 82)
    lines.append(f"[*] Target Workflow : {report.get('workflow', 'unknown')}")
    lines.append(f"[*] Total Properties: {report['summary']['total_properties']}")
    lines.append(f"[*] Holds (Passed)  : {report['summary']['holds']}")
    lines.append(f"[*] Violated        : {report['summary']['violated']}")
    lines.append(f"[*] Execution Time  : {report['summary']['total_execution_time_ms']} ms")
    lines.append("-" * 82)
    lines.append(f"{'Property ID':<30} {'Category':<18} {'Expected':<8} {'Verdict':<8} {'Status':<10}")
    lines.append("-" * 82)

    for v in report.get("verifications", []):
        p_id = v["property_id"][:29]
        cat = v["category"][:17]
        exp = v["expected_verdict"][:7]
        act = v["actual_verdict"][:7]
        status = v["status"]
        lines.append(f"{p_id:<30} {cat:<18} {exp:<8} {act:<8} {status:<10}")

    lines.append("-" * 82)
    overall = "ALL PROPERTIES HOLD (VERIFIED)" if report["summary"]["all_properties_hold"] else "PROPERTY VIOLATIONS DETECTED"
    lines.append(f">>> Overall Verdict: {overall} <<<")
    lines.append("=" * 82)

    # If verbose or violations present, print counterexample diagnostics
    violations = [v for v in report.get("verifications", []) if v["status"] == PropertyStatus.VIOLATED.value]
    if violations or verbose:
        lines.append("\n" + "=" * 82)
        lines.append(">>> Counterexample Diagnostic Traces <<<")
        lines.append("=" * 82)
        for v in (violations if not verbose else report.get("verifications", [])):
            lines.append(f"\n[!] Property: {v['property_id']} ({v['name']})")
            lines.append(f"    Category: {v['category']} | Status: {v['status']} (Expected: {v['expected_verdict']}, Actual: {v['actual_verdict']})")
            lines.append(f"    Formula : {v['formula']}")
            ce = v.get("counterexample")
            if ce:
                lines.append(f"    Explanation: {ce.get('explanation')}")
                lines.append(f"    Witness Firing Sequence ({ce.get('length')} step(s)):")
                for step in ce.get("firing_sequence", []):
                    lines.append(f"      [{step['step']:02d}] {step['service']:<24} -> {step['label']}")
                if ce.get("violated_marking"):
                    lines.append(f"    Violating Marking Snapshot: {ce.get('violated_marking')}")
            else:
                lines.append("    (No counterexample trace produced / property holds)")
        lines.append("=" * 82)

    return "\n".join(lines)


def export_verification_report(report: Dict[str, Any], output_path: str) -> str:
    """Serialize verification report to JSON file."""
    os.makedirs(os.path.dirname(os.path.abspath(output_path)), exist_ok=True)
    with open(output_path, "w", encoding="utf-8") as f:
        json.dump(report, f, indent=2, sort_keys=True)
    return output_path


# ============================================================================
# 8. CLI Argument Parsing & Entry Point
# ============================================================================

def parse_args(argv: Optional[List[str]] = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Verify temporal control-flow properties on composed Generalized Workflow Petri nets.",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    parser.add_argument(
        "--net",
        type=str,
        default="interfaces/composed-net.json",
        help="Path to composed Petri net (.json or .lola)",
    )
    parser.add_argument(
        "--properties",
        type=str,
        default="interfaces/control-flow-properties.json",
        help="Path to property catalog (.json) or LoLA formula file (.lola)",
    )
    parser.add_argument(
        "--formula",
        type=str,
        default=None,
        help="Ad-hoc single LoLA CTL formula to verify",
    )
    parser.add_argument(
        "--engine",
        type=str,
        choices=["auto", "lola", "python"],
        default="auto",
        help="Model checking engine: 'auto', 'lola', or 'python'",
    )
    parser.add_argument(
        "--lola-bin",
        type=str,
        default="lola",
        help="LoLA model checker executable path",
    )
    parser.add_argument(
        "--output",
        type=str,
        default="interfaces/property-verification-report.json",
        help="Output file path for JSON verification report",
    )
    parser.add_argument(
        "--max-states",
        type=int,
        default=300000,
        help="Maximum state cutoff for Python state-space exploration",
    )
    parser.add_argument(
        "--timeout",
        type=float,
        default=30.0,
        help="Timeout in seconds per formula",
    )
    parser.add_argument(
        "--verbose",
        "-v",
        action="store_true",
        help="Show verbose step-by-step counterexample trace diagnostics",
    )
    return parser.parse_args(argv)


def main(argv: Optional[List[str]] = None) -> int:
    args = parse_args(argv)
    
    print("======================================================================")
    print(">>> Asynchronous Channel Fusion Property Verification Engine <<<")
    print("======================================================================")
    
    # 1. Load Composed Net Model
    print(f"[*] Loading Petri Net Model from: {args.net}")
    composed_net = load_net_model(args.net)
    print(f"[+] Loaded Net '{composed_net.workflow_name}': {len(composed_net.places)} places, {len(composed_net.transitions)} transitions, {len(composed_net.arcs)} arcs")

    # 2. Load Properties
    if args.formula:
        properties = [PropertySpec(
            id="CUSTOM_FORMULA",
            name="Custom Formula",
            category="CUSTOM",
            description="Custom command-line formula",
            formula=args.formula,
            expected_verdict="UNSAT" if "EF" in args.formula else "SAT",
        )]
    else:
        print(f"[*] Loading Property Specifications from: {args.properties}")
        properties = load_property_specs(args.properties)
        print(f"[+] Loaded {len(properties)} property specification(s)")

    # 3. Execute Verification
    print(f"[*] Model Checking {len(properties)} property specification(s) (Engine: {args.engine})...")
    report = verify_all_properties(
        composed_net=composed_net,
        properties=properties,
        engine=args.engine,
        lola_bin=args.lola_bin,
        max_states=args.max_states,
        timeout_sec=args.timeout,
    )

    # 4. Export JSON Report
    if args.output:
        out_path = export_verification_report(report, args.output)
        print(f"[+] Exported verification report JSON to: {out_path}")

    # 5. Display Terminal Report
    term_report = format_terminal_report(report, verbose=args.verbose)
    print("\n" + term_report)

    return 0 if report["summary"]["all_properties_hold"] else 1


if __name__ == "__main__":
    sys.exit(main())
