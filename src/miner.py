#!/usr/bin/env python3
"""
Noise-Unfiltered Inductive Petri Net Discovery Module & CLI.

Discovers sound Generalized Workflow (GWF) Petri nets from normalized service event logs
using pm4py's Inductive Miner algorithm with noise filtering strictly disabled (noise_threshold = 0.0).
This guarantees 100% trace variant retention to expose microservice data-loss artifacts,
concurrency interleavings, and anomalous execution sequences.
"""

import argparse
import collections
import csv
import json
import os
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple

import pandas as pd
import pm4py
from pm4py.objects.petri_net.obj import Marking, PetriNet

try:
    from src.generate_mixed_logs import infer_mixed_tag
except ImportError:
    try:
        from generate_mixed_logs import infer_mixed_tag
    except ImportError:
        def infer_mixed_tag(path_or_name: str) -> Optional[str]:
            import re
            if not path_or_name:
                return None
            m = re.search(r"mixed_drift_\d+(?:_\d+)?_partial_\d+(?:_\d+)?", str(path_or_name))
            return m.group(0) if m else None

try:
    from src.generate_partial_logs import infer_partial_tag
except ImportError:
    try:
        from generate_partial_logs import infer_partial_tag
    except ImportError:
        def infer_partial_tag(path_or_name: str) -> Optional[str]:
            import re
            if not path_or_name:
                return None
            m = re.search(r"partial_\d+(?:_\d+)?", str(path_or_name))
            return m.group(0) if m else None

try:
    from src.generate_drift_logs import infer_drift_tag
except ImportError:
    try:
        from generate_drift_logs import infer_drift_tag
    except ImportError:
        def infer_drift_tag(path_or_name: str) -> Optional[str]:
            import re
            if not path_or_name:
                return None
            m = re.search(r"drift_\d+(?:_\d+)?", str(path_or_name))
            return m.group(0) if m else None


def infer_artifact_tag(path_or_name: str) -> Optional[str]:
    """Extract mixed, partial, or drift tag from path or name."""
    tag = infer_mixed_tag(path_or_name)
    if tag:
        return tag
    tag = infer_partial_tag(path_or_name)
    if tag:
        return tag
    return infer_drift_tag(path_or_name)


def load_event_log(csv_path: str) -> pd.DataFrame:
    """Load a CSV service event log into a canonical format for pm4py.
    
    Preserves exact row ordering while mapping:
      - case_id -> case:concept:name
      - activity -> concept:name
      - timestamp -> time:timestamp
    
    Args:
        csv_path: Path to the service CSV event log.
        
    Returns:
        Formatted pandas DataFrame ready for inductive discovery.
        
    Raises:
        FileNotFoundError: If csv_path does not exist.
        ValueError: If required columns are missing or the event log is empty.
    """
    if not os.path.exists(csv_path):
        raise FileNotFoundError(f"Event log file not found: {csv_path}")

    df = pd.read_csv(csv_path)
    if df.empty:
        raise ValueError(f"Event log is empty: {csv_path}")

    required_cols = {"case_id", "activity", "timestamp"}
    missing = required_cols - set(df.columns)
    if missing:
        raise ValueError(f"Missing required columns in {csv_path}: {sorted(missing)}")

    # Convert timestamps: check if numeric (e.g. microseconds or seconds) or datetime strings
    if pd.api.types.is_numeric_dtype(df["timestamp"]):
        # Detect if timestamps are microseconds (large integer > 1e12) or standard seconds
        max_ts = df["timestamp"].max()
        if max_ts > 1e14:
            df["timestamp"] = pd.to_datetime(df["timestamp"], unit="us")
        elif max_ts > 1e11:
            df["timestamp"] = pd.to_datetime(df["timestamp"], unit="ms")
        elif max_ts > 1e8:
            df["timestamp"] = pd.to_datetime(df["timestamp"], unit="s")
        else:
            df["timestamp"] = pd.to_datetime(df["timestamp"])
    else:
        df["timestamp"] = pd.to_datetime(df["timestamp"])

    formatted_df = pm4py.format_dataframe(
        df,
        case_id="case_id",
        activity_key="activity",
        timestamp_key="timestamp",
    )
    return formatted_df


def get_log_statistics(df: pd.DataFrame) -> Tuple[int, int, int]:
    """Calculate case count, event count, and distinct trace variant count.
    
    Args:
        df: Canonical pm4py event log DataFrame.
        
    Returns:
        Tuple of (case_count, event_count, variant_count).
    """
    case_count = int(df["case:concept:name"].nunique())
    event_count = len(df)
    variants = pm4py.get_variants_as_tuples(df)
    variant_count = len(variants)
    return case_count, event_count, variant_count


def discover_service_net(
    df: pd.DataFrame,
    noise_threshold: float = 0.0,
) -> Tuple[PetriNet, Marking, Marking]:
    """Discover a sound Generalized Workflow Petri net using Inductive Miner with noise_threshold = 0.0.
    
    Enforces the strict invariant that noise_threshold must equal 0.0 to prevent
    dropping infrequent trace variants or masking data-loss artifacts.
    
    Args:
        df: Formatted event log DataFrame.
        noise_threshold: Noise filtering threshold (must be strictly 0.0).
        
    Returns:
        Tuple of (PetriNet, initial_marking, final_marking).
        
    Raises:
        ValueError: If noise_threshold != 0.0 or log is empty.
    """
    if noise_threshold != 0.0:
        raise ValueError(
            f"Strict Invariant Violation: noise_threshold must be strictly 0.0 to retain all "
            f"trace variants and prevent masking data-loss artifacts (received noise_threshold={noise_threshold})"
        )

    if df.empty:
        raise ValueError("Cannot discover Petri net from an empty event log.")

    net, initial_marking, final_marking = pm4py.discover_petri_net_inductive(
        df,
        noise_threshold=0.0,
    )
    return net, initial_marking, final_marking


def serialize_petri_net_to_dict(
    net: PetriNet,
    initial_marking: Marking,
    final_marking: Marking,
    service_name: str,
    case_count: int,
    event_count: int,
    variant_count: int,
) -> Dict[str, Any]:
    """Convert a pm4py Petri net and markings into a deterministic structured JSON dict.
    
    Conforms to the schema conventions of `interfaces/mined-nets.json`.
    """
    places = sorted(p.name for p in net.places)

    transitions = []
    for t in net.transitions:
        is_silent = t.label is None or t.label == ""
        transitions.append({
            "id": t.name,
            "label": t.label if not is_silent else None,
            "is_silent": is_silent,
        })
    # Deterministic sorting: visible before silent, then by label, then by id
    transitions.sort(key=lambda x: (x["is_silent"], x["label"] or "", x["id"]))

    arcs = sorted([arc.source.name, arc.target.name] for arc in net.arcs)

    # Initial marking place list
    im_places = sorted(p.name for p, count in initial_marking.items() for _ in range(count))
    # Final marking place list
    fm_places = sorted(p.name for p, count in final_marking.items() for _ in range(count))

    return {
        "service": service_name,
        "noise_threshold": 0.0,
        "variant_retention": "100%",
        "case_count": case_count,
        "event_count": event_count,
        "variant_count": variant_count,
        "places": places,
        "transitions": transitions,
        "arcs": arcs,
        "initial_marking": im_places,
        "final_marking": fm_places,
    }


def calculate_mining_summary(
    service_name: str,
    log_file: str,
    case_count: int,
    event_count: int,
    variant_count: int,
    net: PetriNet,
) -> Dict[str, Any]:
    """Compute summary statistics for a mined service Petri net."""
    silent_count = sum(1 for t in net.transitions if t.label is None or t.label == "")
    visible_count = len(net.transitions) - silent_count

    return {
        "service": service_name,
        "log_file": log_file,
        "case_count": case_count,
        "event_count": event_count,
        "variant_count": variant_count,
        "place_count": len(net.places),
        "visible_transition_count": visible_count,
        "silent_transition_count": silent_count,
        "arc_count": len(net.arcs),
        "noise_threshold": 0.0,
        "all_variants_retained": True,
    }


def export_pnml(
    net: PetriNet,
    initial_marking: Marking,
    final_marking: Marking,
    output_path: str,
) -> None:
    """Export Petri net to standard PNML format."""
    os.makedirs(os.path.dirname(os.path.abspath(output_path)), exist_ok=True)
    pm4py.write_pnml(net, initial_marking, final_marking, output_path)


def export_diagrams(
    net: PetriNet,
    initial_marking: Marking,
    final_marking: Marking,
    output_dir: str,
    service_name: str,
    export_dot: bool = True,
    export_svg: bool = True,
    export_png: bool = True,
) -> Dict[str, str]:
    """Render and export Petri net visualizations in DOT, SVG, and PNG formats."""
    os.makedirs(output_dir, exist_ok=True)
    results = {}

    from pm4py.visualization.petri_net import visualizer as pn_visualizer
    gviz = pn_visualizer.apply(net, initial_marking, final_marking)

    if export_dot:
        dot_path = os.path.join(output_dir, f"{service_name}.dot")
        with open(dot_path, "w", encoding="utf-8") as f:
            f.write(str(gviz))
        results["dot"] = dot_path

    if export_svg:
        svg_path = os.path.join(output_dir, f"{service_name}.svg")
        try:
            gviz.render(filename=service_name, directory=output_dir, format="svg", cleanup=True)
            results["svg"] = svg_path
        except Exception:
            pass

    if export_png:
        png_path = os.path.join(output_dir, f"{service_name}.png")
        try:
            gviz.render(filename=service_name, directory=output_dir, format="png", cleanup=True)
            results["png"] = png_path
        except Exception:
            pass

    return results


def process_service_log(
    csv_path: str,
    noise_threshold: float = 0.0,
    pnml_dir: Optional[str] = None,
    diagram_dir: Optional[str] = None,
) -> Tuple[Dict[str, Any], Dict[str, Any]]:
    """Process a single service event log, discover Petri net, and compute exports and metrics.
    
    Args:
        csv_path: Path to service CSV log.
        noise_threshold: Noise threshold (must be strictly 0.0).
        pnml_dir: Optional directory to export PNML file.
        diagram_dir: Optional directory to export diagrams.
        
    Returns:
        Tuple of (service_net_dict, service_summary_dict).
    """
    service_name = Path(csv_path).stem
    formatted_df = load_event_log(csv_path)
    case_count, event_count, variant_count = get_log_statistics(formatted_df)

    net, initial_marking, final_marking = discover_service_net(
        formatted_df,
        noise_threshold=noise_threshold,
    )

    net_dict = serialize_petri_net_to_dict(
        net=net,
        initial_marking=initial_marking,
        final_marking=final_marking,
        service_name=service_name,
        case_count=case_count,
        event_count=event_count,
        variant_count=variant_count,
    )

    summary_dict = calculate_mining_summary(
        service_name=service_name,
        log_file=csv_path,
        case_count=case_count,
        event_count=event_count,
        variant_count=variant_count,
        net=net,
    )

    tag = infer_artifact_tag(csv_path)
    suffix = f"_{tag}" if tag and tag not in service_name else ""

    if pnml_dir:
        pnml_path = os.path.join(pnml_dir, f"{service_name}{suffix}.pnml")
        export_pnml(net, initial_marking, final_marking, pnml_path)

    if diagram_dir:
        export_diagrams(net, initial_marking, final_marking, diagram_dir, f"{service_name}{suffix}")

    return net_dict, summary_dict


def process_all_logs(
    logs_dir: str,
    noise_threshold: float = 0.0,
    pnml_dir: Optional[str] = None,
    diagram_dir: Optional[str] = None,
) -> Tuple[Dict[str, Dict[str, Any]], Dict[str, Dict[str, Any]]]:
    """Process all CSV service event logs in a directory in deterministic alphabetical order.
    
    Args:
        logs_dir: Directory containing service CSV logs.
        noise_threshold: Noise threshold (must be strictly 0.0).
        pnml_dir: Optional directory for PNML exports.
        diagram_dir: Optional directory for diagram exports.
        
    Returns:
        Tuple of (all_mined_nets_dict, all_summaries_dict).
    """
    if not os.path.isdir(logs_dir):
        raise FileNotFoundError(f"Logs directory not found: {logs_dir}")

    csv_files = sorted(
        [
            os.path.join(logs_dir, f)
            for f in os.listdir(logs_dir)
            if f.endswith(".csv") and not f.startswith(".")
        ]
    )

    if not csv_files:
        raise ValueError(f"No CSV event logs found in directory: {logs_dir}")

    all_nets: Dict[str, Dict[str, Any]] = {}
    all_summaries: Dict[str, Dict[str, Any]] = {}

    for csv_path in csv_files:
        service_name = Path(csv_path).stem
        net_dict, summary_dict = process_service_log(
            csv_path=csv_path,
            noise_threshold=noise_threshold,
            pnml_dir=pnml_dir,
            diagram_dir=diagram_dir,
        )
        all_nets[service_name] = net_dict
        all_summaries[service_name] = summary_dict

    return all_nets, all_summaries


def build_parser() -> argparse.ArgumentParser:
    """Build the CLI argument parser for inductive miner discovery."""
    parser = argparse.ArgumentParser(
        description="Discover sound Generalized Workflow Petri nets from service event logs "
                    "using pm4py Inductive Miner with strict noise_threshold = 0.0 invariant."
    )
    group = parser.add_mutually_exclusive_group()
    group.add_argument(
        "--log",
        type=str,
        help="Path to a single service CSV event log (e.g. logs/compose-post-service.csv).",
    )
    group.add_argument(
        "--logs-dir",
        type=str,
        default="data/logs",
        help="Directory containing per-service CSV event logs (default: data/logs).",
    )
    parser.add_argument(
        "--output",
        type=str,
        default=None,
        help="Output JSON path for mined Petri net representations (default: interfaces/mined-nets.json or interfaces/mined/<category>/mined-nets_<tag>.json).",
    )
    parser.add_argument(
        "--summary-file",
        type=str,
        default=None,
        help="Output JSON path for discovery summary report (default: data/logs/mining.summary.json or <logs-dir>/mining_<tag>.summary.json).",
    )
    parser.add_argument(
        "--pnml-dir",
        type=str,
        default=None,
        help="Optional directory to export standard PNML models (e.g. interfaces/pnml).",
    )
    parser.add_argument(
        "--diagram-dir",
        type=str,
        default=None,
        help="Optional directory to export DOT/SVG/PNG Petri net visualizations.",
    )
    parser.add_argument(
        "--noise-threshold",
        type=float,
        default=0.0,
        help="Noise filtering threshold. Invariant enforcement: must be strictly 0.0.",
    )
    return parser


def main() -> int:
    """Main CLI execution routine."""
    parser = build_parser()
    args = parser.parse_args()

    # Enforce strict invariant early at CLI boundary
    if args.noise_threshold != 0.0:
        sys.stderr.write(
            f"Error: Strict Invariant Violation: noise_threshold must be strictly 0.0 to retain all "
            f"trace variants and prevent masking data-loss artifacts (received {args.noise_threshold}).\n"
        )
        return 1

    try:
        tag = infer_artifact_tag(args.log if args.log else args.logs_dir)

        output_path = args.output
        if output_path is None:
            if tag:
                if tag.startswith("mixed_"):
                    output_path = f"interfaces/mined/mixed/mined-nets_{tag}.json"
                elif tag.startswith("drift_"):
                    output_path = f"interfaces/mined/drift/mined-nets_{tag}.json"
                elif tag.startswith("partial_"):
                    output_path = f"interfaces/mined/partial/mined-nets_{tag}.json"
                else:
                    output_path = f"interfaces/mined/mined-nets_{tag}.json"
            else:
                output_path = "interfaces/mined-nets.json"

        summary_path = args.summary_file
        if summary_path is None:
            if tag:
                base_dir = os.path.dirname(args.log) if args.log else args.logs_dir
                summary_path = os.path.join(base_dir, f"mining_{tag}.summary.json")
            else:
                summary_path = "data/logs/mining.summary.json"

        if args.log:
            service_name = Path(args.log).stem
            net_dict, summary_dict = process_service_log(
                csv_path=args.log,
                noise_threshold=args.noise_threshold,
                pnml_dir=args.pnml_dir,
                diagram_dir=args.diagram_dir,
            )
            mined_nets = {service_name: net_dict}
            summaries = {service_name: summary_dict}
        else:
            mined_nets, summaries = process_all_logs(
                logs_dir=args.logs_dir,
                noise_threshold=args.noise_threshold,
                pnml_dir=args.pnml_dir,
                diagram_dir=args.diagram_dir,
            )

        if output_path:
            os.makedirs(os.path.dirname(os.path.abspath(output_path)), exist_ok=True)
            with open(output_path, "w", encoding="utf-8") as f:
                json.dump(mined_nets, f, indent=2)
            print(f"Mined Petri nets saved to: {output_path}")

        if summary_path:
            os.makedirs(os.path.dirname(os.path.abspath(summary_path)), exist_ok=True)
            with open(summary_path, "w", encoding="utf-8") as f:
                json.dump(summaries, f, indent=2)
            print(f"Discovery summary saved to: {summary_path}")

        print(f"Successfully processed {len(mined_nets)} service log(s) with noise_threshold=0.0 (100% variant retention).")
        return 0

    except Exception as exc:
        sys.stderr.write(f"Error during inductive process mining: {exc}\n")
        return 1


if __name__ == "__main__":
    sys.exit(main())
