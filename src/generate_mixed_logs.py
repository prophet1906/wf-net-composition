#!/usr/bin/env python3
"""
Deterministic Service Event Log Compound Label Drift & Truncation Loss Generator.

Composes telemetry label drift (Cause-3) and tail-truncation loss (Cause-2) in strict physical
causal sequence (Drift Mutation First -> Tail Truncation Second), guaranteeing orthogonal parameter
independence, strict source directory immutability, and unified multi-fault provenance metadata.

Reuses core mutation and truncation algorithms directly from:
  - src.generate_drift_logs (is_case_selected_for_drift, DEFAULT_DRIFT_RULES, PROOF_OF_CALL_TARGETS, validate_csv_header)
  - src.generate_partial_logs (truncate_event_rows)

Guarantees:
  - Strict read-only immutability of the source logs directory.
  - Causal execution pipeline: caller client span mutation across the full ground-truth case universe first,
    followed by deterministic tail-truncation of event rows second.
  - Standardized compound naming: logs_mixed_drift_<D>_partial_<L>/ and mixed_drift_<D>_partial_<L>.summary.json.
  - Pure Python standard library (zero external dependencies).
"""

import argparse
import csv
import json
import math
import os
import re
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple

# Add repository root to path for direct invocation
REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.generate_drift_logs import (
    DEFAULT_DRIFT_RULES,
    PROOF_OF_CALL_TARGETS,
    REQUIRED_CSV_COLUMNS,
    is_case_selected_for_drift,
    validate_csv_header,
)
from src.generate_partial_logs import truncate_event_rows


def _format_num_tag(val: float) -> str:
    """Format a float or int into a filesystem-safe number string with underscores for decimals."""
    if float(val).is_integer():
        return str(int(val))
    formatted = f"{val:.4f}".rstrip("0").rstrip(".")
    return formatted.replace(".", "_")


def format_mixed_tag(drift_percentage: float, loss_percentage: float) -> str:
    """Format drift and loss percentages into a clean compound mixed tag string.

    Examples:
        (10.0, 5.0)   -> "mixed_drift_10_partial_5"
        (0.0, 0.0)    -> "mixed_drift_0_partial_0"
        (2.5, 7.5)    -> "mixed_drift_2_5_partial_7_5"
        (12.25, 5.0)  -> "mixed_drift_12_25_partial_5"

    Args:
        drift_percentage: Percentage of trace cases to mutate.
        loss_percentage: Percentage of tail events to truncate.

    Returns:
        Formatted compound tag string.
    """
    d_tag = _format_num_tag(drift_percentage)
    l_tag = _format_num_tag(loss_percentage)
    return f"mixed_drift_{d_tag}_partial_{l_tag}"


def infer_mixed_tag(path_or_name: str) -> Optional[str]:
    """Extract a compound mixed tag from a directory path or string.

    Examples:
        "logs_mixed_drift_10_partial_5" -> "mixed_drift_10_partial_5"
        "path/to/logs_mixed_drift_2_5_partial_7_5/svc.csv" -> "mixed_drift_2_5_partial_7_5"

    Args:
        path_or_name: Directory path or filename string.

    Returns:
        Extracted tag string or None if not matched.
    """
    if not path_or_name:
        return None
    match = re.search(r"mixed_drift_\d+(?:_\d+)?_partial_\d+(?:_\d+)?", str(path_or_name))
    if match:
        return match.group(0)
    return None


def format_mixed_filename(base_name: str, tag: Optional[str] = None, extension: str = "") -> str:
    """Construct an artifact filename with an optional mixed tag infix.

    Args:
        base_name: Base name of the file (e.g. 'mining' or 'mixed').
        tag: Optional mixed tag (e.g. 'mixed_drift_10_partial_5').
        extension: File extension including dot (e.g. '.summary.json' or '.pnml').

    Returns:
        Formatted filename string.
    """
    if tag:
        if tag in base_name:
            return f"{base_name}{extension}"
        return f"{base_name}_{tag}{extension}"
    return f"{base_name}{extension}"


def process_service_mixed_log(
    csv_path: str,
    drift_percentage: float,
    loss_percentage: float,
    output_csv_path: str,
    drift_rules: Optional[Dict[str, str]] = None,
) -> Tuple[Dict[str, Any], Set[str], Set[str], Set[str]]:
    """Process a single service CSV log: apply caller drift mutation first, tail truncation second.

    Pipeline:
      1. Ingest original rows and validate CSV schema.
      2. Deterministically apply caller client span drift mutation across full case universe.
      3. Apply deterministic tail-truncation loss slicing to the resulting mutated rows.
      4. Write final retained rows to output destination.

    Args:
        csv_path: Path to the source service CSV file.
        drift_percentage: Percentage of trace cases to mutate (0.0 to 100.0).
        loss_percentage: Percentage of tail events to truncate (0.0 to 100.0).
        output_csv_path: Destination path for the transformed CSV file.
        drift_rules: Optional custom dictionary of canonical-to-drifted span mapping rules.

    Returns:
        Tuple of (service_metrics_dict, all_case_ids, mutated_case_ids, retained_case_ids).

    Raises:
        FileNotFoundError: If source CSV does not exist.
        ValueError: If CSV schema is invalid.
    """
    if not os.path.exists(csv_path):
        raise FileNotFoundError(f"Service log file not found: {csv_path}")

    rules = drift_rules if drift_rules is not None else DEFAULT_DRIFT_RULES

    with open(csv_path, "r", encoding="utf-8", newline="") as f:
        reader = csv.reader(f)
        try:
            header = next(reader)
        except StopIteration:
            header = REQUIRED_CSV_COLUMNS
            rows = []
        else:
            validate_csv_header(header, csv_path)
            rows = list(reader)

    dict_rows = [dict(zip(header, row)) for row in rows]
    total_original_events = len(dict_rows)

    all_case_ids: Set[str] = set()
    mutated_case_ids: Set[str] = set()
    applied_mutations: Dict[str, int] = {}
    mutated_events = 0

    # Step 1: Apply Drift Mutation First across full ground-truth case universe
    drifted_dict_rows: List[Dict[str, str]] = []
    for r in dict_rows:
        case_id = r.get("case_id", "")
        activity = r.get("activity", "")
        if case_id:
            all_case_ids.add(case_id)

        new_row = dict(r)
        if case_id and is_case_selected_for_drift(case_id, drift_percentage):
            if activity in rules:
                new_activity = rules[activity]
                new_row["activity"] = new_activity
                mutated_events += 1
                mutated_case_ids.add(case_id)
                mutation_key = f"{activity} -> {new_activity}"
                applied_mutations[mutation_key] = applied_mutations.get(mutation_key, 0) + 1

        drifted_dict_rows.append(new_row)

    # Step 2: Apply Tail Truncation Second to the drifted stream
    retained_dict_rows, orig_count, retained_count = truncate_event_rows(
        drifted_dict_rows, loss_percentage
    )

    retained_case_ids: Set[str] = {
        row["case_id"] for row in retained_dict_rows if "case_id" in row and row["case_id"]
    }
    dropped_events = total_original_events - retained_count

    # Write final output CSV
    os.makedirs(os.path.dirname(os.path.abspath(output_csv_path)), exist_ok=True)
    with open(output_csv_path, "w", encoding="utf-8", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(header)
        for r in retained_dict_rows:
            writer.writerow([r.get(col, "") for col in header])

    metrics: Dict[str, Any] = {
        "original_events": total_original_events,
        "total_events": total_original_events,
        "mutated_events": mutated_events,
        "retained_events": retained_count,
        "dropped_events": dropped_events,
        "total_cases": len(all_case_ids),
        "mutated_cases": len(mutated_case_ids),
        "retained_cases": len(retained_case_ids),
        "applied_mutations": applied_mutations,
    }

    return metrics, all_case_ids, mutated_case_ids, retained_case_ids


def generate_mixed_logs(
    logs_dir: str,
    drift_percentage: float,
    loss_percentage: float,
    output_dir: Optional[str] = None,
    drift_rules: Optional[Dict[str, str]] = None,
) -> Dict[str, Any]:
    """Generate compound drifted and tail-truncated service event logs for a (drift, loss) pair.

    Args:
        logs_dir: Source directory containing original service CSV logs.
        drift_percentage: Drift percentage in [0.0, 100.0].
        loss_percentage: Loss percentage in [0.0, 100.0].
        output_dir: Optional explicit output directory. Defaults to 'logs_mixed_drift_<D>_partial_<L>'.
        drift_rules: Optional custom span mutation mapping rules.

    Returns:
        Structured compound provenance summary dictionary.

    Raises:
        FileNotFoundError: If logs_dir does not exist.
        NotADirectoryError: If logs_dir is not a directory.
        ValueError: If parameters are out of bounds, output_dir equals logs_dir, or no CSVs found.
    """
    if not os.path.exists(logs_dir):
        raise FileNotFoundError(f"Source logs directory not found: {logs_dir}")
    if not os.path.isdir(logs_dir):
        raise NotADirectoryError(f"Source path is not a directory: {logs_dir}")

    drift_float = float(drift_percentage)
    if drift_float < 0.0 or drift_float > 100.0:
        raise ValueError(
            f"Invalid drift percentage: {drift_percentage}. Must be between 0.0 and 100.0 (inclusive)."
        )

    loss_float = float(loss_percentage)
    if loss_float < 0.0 or loss_float > 100.0:
        raise ValueError(
            f"Invalid loss percentage: {loss_percentage}. Must be between 0.0 and 100.0 (inclusive)."
        )

    tag = format_mixed_tag(drift_float, loss_float)

    if output_dir is None:
        abs_source = os.path.abspath(logs_dir)
        parent_dir = os.path.dirname(abs_source)
        source_name = os.path.basename(abs_source)
        if os.path.basename(parent_dir) == "data" and source_name == "logs":
            resolved_output_dir = os.path.join(parent_dir, "benchmarks", "mixed", f"{source_name}_{tag}")
        else:
            resolved_output_dir = os.path.join(parent_dir, f"{source_name}_{tag}")
    else:
        resolved_output_dir = os.path.abspath(output_dir)

    # Strict source directory immutability guard
    if os.path.abspath(logs_dir) == resolved_output_dir:
        raise ValueError(
            f"Source directory immutability violation: output directory '{resolved_output_dir}' "
            f"cannot be identical to source directory '{os.path.abspath(logs_dir)}'."
        )

    # Discover service CSV logs in deterministic order
    csv_files = sorted(
        [
            f
            for f in os.listdir(logs_dir)
            if f.endswith(".csv") and not f.startswith(".")
        ]
    )

    if not csv_files:
        raise ValueError(f"No CSV event logs found in directory: {logs_dir}")

    os.makedirs(resolved_output_dir, exist_ok=True)

    rules = drift_rules if drift_rules is not None else DEFAULT_DRIFT_RULES

    services_summary: Dict[str, Dict[str, Any]] = {}
    all_cases: Set[str] = set()
    all_mutated_cases: Set[str] = set()
    all_retained_cases: Set[str] = set()
    total_original_events = 0
    total_mutated_events = 0
    total_retained_events = 0
    total_dropped_events = 0

    for csv_file in csv_files:
        service_name = Path(csv_file).stem
        src_path = os.path.join(logs_dir, csv_file)
        dst_path = os.path.join(resolved_output_dir, csv_file)

        (
            service_metrics,
            service_all_cases,
            service_mutated_cases,
            service_retained_cases,
        ) = process_service_mixed_log(
            csv_path=src_path,
            drift_percentage=drift_float,
            loss_percentage=loss_float,
            output_csv_path=dst_path,
            drift_rules=rules,
        )

        services_summary[service_name] = service_metrics
        all_cases.update(service_all_cases)
        all_mutated_cases.update(service_mutated_cases)
        all_retained_cases.update(service_retained_cases)
        total_original_events += service_metrics["original_events"]
        total_mutated_events += service_metrics["mutated_events"]
        total_retained_events += service_metrics["retained_events"]
        total_dropped_events += service_metrics["dropped_events"]

    retained_ratio = (
        round(total_retained_events / total_original_events, 4)
        if total_original_events > 0
        else 1.0
    )

    summary: Dict[str, Any] = {
        "source_dir": logs_dir,
        "output_dir": resolved_output_dir,
        "drift_percentage": drift_float,
        "loss_percentage": loss_float,
        "selection_strategy": "sha256_modulo_10000",
        "total_original_events": total_original_events,
        "total_mutated_events": total_mutated_events,
        "total_retained_events": total_retained_events,
        "total_dropped_events": total_dropped_events,
        "retained_event_ratio": retained_ratio,
        "total_cases": len(all_cases),
        "total_mutated_cases": len(all_mutated_cases),
        "total_retained_cases": len(all_retained_cases),
        "drift_rules": rules,
        "proof_of_call_targets": PROOF_OF_CALL_TARGETS,
        "services": services_summary,
    }

    # Write summary JSON named mixed_drift_<D>_partial_<L>.summary.json
    summary_filename = f"{tag}.summary.json"
    summary_path = os.path.join(resolved_output_dir, summary_filename)
    with open(summary_path, "w", encoding="utf-8") as f:
        json.dump(summary, f, indent=2)

    return summary


def generate_mixed_logs_batch(
    logs_dir: str,
    drift_percentages: List[float],
    loss_percentages: List[float],
    output_dir: Optional[str] = None,
    drift_rules: Optional[Dict[str, str]] = None,
) -> Dict[Tuple[float, float], Dict[str, Any]]:
    """Execute 2D Cartesian grid batch generation across drift and loss parameter lists.

    Args:
        logs_dir: Source directory containing original service CSV logs.
        drift_percentages: List of drift percentages (e.g. [0.0, 5.0, 10.0]).
        loss_percentages: List of loss percentages (e.g. [0.0, 5.0, 10.0]).
        output_dir: Optional custom output directory (only allowed when generating a single pair).
        drift_rules: Optional custom span mutation mapping rules.

    Returns:
        Dictionary mapping (drift_pct, loss_pct) tuple to its corresponding summary dict.

    Raises:
        ValueError: If multiple parameter pairs are provided with a custom output_dir.
    """
    total_combinations = len(drift_percentages) * len(loss_percentages)
    if output_dir is not None and total_combinations > 1:
        raise ValueError(
            "Custom --output-dir can only be specified when generating logs for a single (drift, loss) pair."
        )

    results: Dict[Tuple[float, float], Dict[str, Any]] = {}
    for drift in drift_percentages:
        for loss in loss_percentages:
            summary = generate_mixed_logs(
                logs_dir=logs_dir,
                drift_percentage=drift,
                loss_percentage=loss,
                output_dir=output_dir,
                drift_rules=drift_rules,
            )
            results[(float(drift), float(loss))] = summary

    return results


def build_parser() -> argparse.ArgumentParser:
    """Build the CLI argument parser for compound mixed log generation."""
    parser = argparse.ArgumentParser(
        description="Generate deterministic compound telemetry label drift and tail-truncation "
                    "loss service event logs with strict immutability guarantees for source logs."
    )
    parser.add_argument(
        "--logs-dir",
        type=str,
        default="data/logs",
        help="Directory containing per-service CSV event logs (default: data/logs).",
    )
    parser.add_argument(
        "--drift",
        type=float,
        nargs="+",
        default=[5.0],
        help="One or more drift percentages to simulate (e.g. --drift 0 5 10 15 20). Default: 5.0.",
    )
    parser.add_argument(
        "--loss",
        type=float,
        nargs="+",
        default=[5.0],
        help="One or more loss percentages to simulate (e.g. --loss 0 5 10 15 20). Default: 5.0.",
    )
    parser.add_argument(
        "--output-dir",
        type=str,
        default=None,
        help="Explicit output directory path (valid only when specifying a single drift and single loss percentage).",
    )
    return parser


def main(argv: Optional[List[str]] = None) -> int:
    """Main CLI execution routine."""
    parser = build_parser()
    args = parser.parse_args(argv)

    try:
        results = generate_mixed_logs_batch(
            logs_dir=args.logs_dir,
            drift_percentages=args.drift,
            loss_percentages=args.loss,
            output_dir=args.output_dir,
        )

        for (drift, loss), summary in results.items():
            tag = format_mixed_tag(drift, loss)
            summary_file = f"{tag}.summary.json"
            print(
                f"Generated compound logs for drift={drift}%, loss={loss}% in '{summary['output_dir']}' "
                f"({summary['total_retained_events']}/{summary['total_original_events']} events retained, "
                f"{summary['total_mutated_events']} events mutated across "
                f"{summary['total_mutated_cases']}/{summary['total_cases']} cases, "
                f"summary saved to '{summary_file}')."
            )

        return 0

    except Exception as exc:
        sys.stderr.write(f"Error during compound log generation: {exc}\n")
        return 1


if __name__ == "__main__":
    sys.exit(main())
