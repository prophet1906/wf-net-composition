#!/usr/bin/env python3
"""
Deterministic Service Event Log Label Drift Generator & Invariant Verification.

Ingests service CSV event logs from an input directory, deterministically selects a configurable
percentage of trace cases using SHA-256 modulo hashing, applies canonical-to-drifted RPC span
mutation rules to caller client spans while strictly preserving callee server spans as immutable
physical proof, and exports the mutated logs into isolated destination directories (e.g. logs_drift_<percentage>).

Guarantees:
  - Strict read-only immutability of the source logs directory.
  - Deterministic trace selection via SHA-256 modulo: int(sha256(case_id)) % 10000 < round(D * 100).
  - Selective caller client span mutation with 100% callee server span proof preservation.
  - Strict mathematical invariants: row count preservation, timestamp invariance, case count preservation.
  - Explicit drift_<percentage> artifact and summary naming.
  - Pure Python standard library (zero external dependencies).
"""

import argparse
import csv
import hashlib
import json
import math
import os
import re
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple


REQUIRED_CSV_COLUMNS = ["case_id", "activity", "timestamp"]

DEFAULT_DRIFT_RULES: Dict[str, str] = {
    # compose-post-service RPC client dispatches
    "store_post_client": "store_post_client_v2",
    "compose_text_client": "compose_text_grpc_client",
    "compose_unique_id_client": "unique_id_rpc_client",
    "write_home_timeline_client": "post_home_timeline_client",
    "compose_media_client": "media_upload_dispatch_client",
    "write_user_timeline_client": "user_timeline_dispatch_client",
    "compose_creator_client": "user_creator_rpc_client",
    # text-service RPC client dispatches
    "compose_urls_client": "compose_urls_grpc_client",
    "compose_user_mentions_client": "user_mentions_rpc_client",
    # home-timeline-service RPC client dispatches
    "get_followers_client": "get_followers_rpc_client",
    # nginx-web-server RPC client dispatches
    "compose_post_client": "compose_post_dispatch_client",
    "read_home_timeline_client": "read_home_timeline_dispatch_client",
}

PROOF_OF_CALL_TARGETS: Dict[str, str] = {
    "store_post_client": "store_post_server",
    "compose_text_client": "compose_text_server",
    "compose_unique_id_client": "compose_unique_id_server",
    "write_home_timeline_client": "write_home_timeline_server",
    "compose_media_client": "compose_media_server",
    "write_user_timeline_client": "write_user_timeline_server",
    "compose_creator_client": "compose_creator_server",
    "compose_urls_client": "compose_urls_server",
    "compose_user_mentions_client": "compose_user_mentions_server",
    "get_followers_client": "get_followers_server",
    "compose_post_client": "compose_post_server",
    "read_home_timeline_client": "read_home_timeline_server",
}


def format_drift_tag(drift_percentage: float) -> str:
    """Format a drift percentage into a clean drift tag string.

    Examples:
        5.0   -> "drift_5"
        10.0  -> "drift_10"
        7.5   -> "drift_7_5"
        0.0   -> "drift_0"
        100.0 -> "drift_100"

    Args:
        drift_percentage: Percentage of trace cases to mutate.

    Returns:
        Formatted string tag e.g. 'drift_5'.
    """
    if float(drift_percentage).is_integer():
        return f"drift_{int(drift_percentage)}"
    # Replace decimal dot with underscore for valid filesystem naming
    formatted = f"{drift_percentage:.4f}".rstrip("0").rstrip(".")
    return f"drift_{formatted.replace('.', '_')}"


def infer_drift_tag(path_or_name: str) -> Optional[str]:
    """Extract a drift tag (e.g. 'drift_5', 'drift_10', 'drift_7_5') from a directory path or string.

    Args:
        path_or_name: Directory path or filename string.

    Returns:
        Extracted tag string (e.g. 'drift_5') or None if not found.
    """
    if not path_or_name:
        return None
    match = re.search(r"drift_\d+(?:_\d+)?", str(path_or_name))
    if match:
        return match.group(0)
    return None


def format_drift_filename(base_name: str, tag: Optional[str] = None, extension: str = "") -> str:
    """Construct an artifact filename with an optional drift tag infix.

    Args:
        base_name: Base name of the file (e.g. 'mining' or 'compose-post-service').
        tag: Optional drift tag (e.g. 'drift_5').
        extension: File extension including dot (e.g. '.summary.json' or '.pnml').

    Returns:
        Formatted filename string.
    """
    if tag:
        # Avoid double tagging if base_name already contains the tag
        if tag in base_name:
            return f"{base_name}{extension}"
        return f"{base_name}_{tag}{extension}"
    return f"{base_name}{extension}"


def is_case_selected_for_drift(case_id: str, drift_percentage: float) -> bool:
    """Determine deterministically whether a trace case is selected for drift mutation.

    Uses SHA-256 modulo hashing: int(sha256(case_id.encode('utf-8')).hexdigest(), 16) % 10000 < round(D * 100).

    Args:
        case_id: Unique trace identifier string.
        drift_percentage: Drift percentage in [0.0, 100.0].

    Returns:
        True if the case is selected for mutation, False otherwise.
    """
    drift_float = float(drift_percentage)
    if drift_float <= 0.0:
        return False
    if drift_float >= 100.0:
        return True

    threshold = round(drift_float * 100)
    digest = hashlib.sha256(str(case_id).encode("utf-8")).hexdigest()
    hash_val = int(digest, 16) % 10000
    return hash_val < threshold


def validate_csv_header(header: List[str], file_path: str) -> None:
    """Validate that the CSV header contains all required columns.

    Args:
        header: List of column names from CSV header row.
        file_path: Path to the CSV file for error reporting.

    Raises:
        ValueError: If any required column is missing.
    """
    header_set = set(header)
    missing = [col for col in REQUIRED_CSV_COLUMNS if col not in header_set]
    if missing:
        raise ValueError(
            f"Missing required columns in CSV log '{file_path}': {missing}. "
            f"Expected header to contain {REQUIRED_CSV_COLUMNS}."
        )


def process_service_drift_log(
    csv_path: str,
    drift_percentage: float,
    output_csv_path: str,
    drift_rules: Optional[Dict[str, str]] = None,
) -> Tuple[Dict[str, Any], Set[str], Set[str]]:
    """Process a single service CSV log, apply selective caller span drift, and write to destination.

    Args:
        csv_path: Path to the source service CSV file.
        drift_percentage: Percentage of trace cases to mutate.
        output_csv_path: Destination path for the drifted CSV file.
        drift_rules: Optional dictionary of canonical-to-drifted span mapping rules.

    Returns:
        Tuple of (service_metrics_dict, all_case_ids_set, mutated_case_ids_set).

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
            # File is completely empty (0 bytes) -> write header and return 0 counts
            header = REQUIRED_CSV_COLUMNS
            rows = []
        else:
            validate_csv_header(header, csv_path)
            rows = list(reader)

    dict_rows = [dict(zip(header, row)) for row in rows]
    total_events = len(dict_rows)

    all_case_ids: Set[str] = set()
    mutated_case_ids: Set[str] = set()
    applied_mutations: Dict[str, int] = {}
    mutated_events = 0

    mutated_dict_rows: List[Dict[str, str]] = []
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

        mutated_dict_rows.append(new_row)

    # Write mutated CSV to output destination preserving exact row count and schema
    os.makedirs(os.path.dirname(os.path.abspath(output_csv_path)), exist_ok=True)
    with open(output_csv_path, "w", encoding="utf-8", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(header)
        for r in mutated_dict_rows:
            writer.writerow([r.get(col, "") for col in header])

    metrics: Dict[str, Any] = {
        "total_events": total_events,
        "total_cases": len(all_case_ids),
        "mutated_cases": len(mutated_case_ids),
        "mutated_events": mutated_events,
        "retained_events": total_events,
        "dropped_events": 0,
        "applied_mutations": applied_mutations,
    }

    return metrics, all_case_ids, mutated_case_ids


def generate_drift_logs(
    logs_dir: str,
    drift_percentage: float,
    output_dir: Optional[str] = None,
    drift_rules: Optional[Dict[str, str]] = None,
) -> Dict[str, Any]:
    """Generate drifted service event logs for a single drift percentage.

    Args:
        logs_dir: Source directory containing original service CSV logs.
        drift_percentage: Drift percentage in [0.0, 100.0].
        output_dir: Optional explicit output directory. Defaults to 'logs_drift_<percentage>'.
        drift_rules: Optional custom span mutation mapping rules.

    Returns:
        Structured drift provenance summary dictionary.

    Raises:
        FileNotFoundError: If logs_dir does not exist.
        NotADirectoryError: If logs_dir is not a directory.
        ValueError: If drift_percentage is out of bounds, output_dir equals logs_dir, or no CSVs found.
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

    tag = format_drift_tag(drift_float)

    # Determine output directory
    if output_dir is None:
        abs_source = os.path.abspath(logs_dir)
        parent_dir = os.path.dirname(abs_source)
        source_name = os.path.basename(abs_source)
        if os.path.basename(parent_dir) == "data" and source_name == "logs":
            resolved_output_dir = os.path.join(parent_dir, "benchmarks", "drift", f"{source_name}_{tag}")
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
    total_original_events = 0
    total_mutated_events = 0

    for csv_file in csv_files:
        service_name = Path(csv_file).stem
        src_path = os.path.join(logs_dir, csv_file)
        dst_path = os.path.join(resolved_output_dir, csv_file)

        service_metrics, service_all_cases, service_mutated_cases = process_service_drift_log(
            csv_path=src_path,
            drift_percentage=drift_float,
            output_csv_path=dst_path,
            drift_rules=rules,
        )

        services_summary[service_name] = service_metrics
        all_cases.update(service_all_cases)
        all_mutated_cases.update(service_mutated_cases)
        total_original_events += service_metrics["total_events"]
        total_mutated_events += service_metrics["mutated_events"]

    summary: Dict[str, Any] = {
        "source_dir": logs_dir,
        "output_dir": resolved_output_dir,
        "drift_percentage": drift_float,
        "selection_strategy": "sha256_modulo_10000",
        "total_original_events": total_original_events,
        "total_mutated_events": total_mutated_events,
        "total_retained_events": total_original_events,
        "total_dropped_events": 0,
        "total_cases": len(all_cases),
        "total_mutated_cases": len(all_mutated_cases),
        "drift_rules": rules,
        "proof_of_call_targets": PROOF_OF_CALL_TARGETS,
        "services": services_summary,
    }

    # Write summary JSON with standardized drift tag naming
    summary_filename = f"drift_{tag}.summary.json"
    summary_path = os.path.join(resolved_output_dir, summary_filename)
    with open(summary_path, "w", encoding="utf-8") as f:
        json.dump(summary, f, indent=2)

    return summary


def generate_drift_logs_batch(
    logs_dir: str,
    drift_percentages: List[float],
    output_dir: Optional[str] = None,
    drift_rules: Optional[Dict[str, str]] = None,
) -> Dict[float, Dict[str, Any]]:
    """Execute batch drift log generation across multiple drift percentages.

    Args:
        logs_dir: Source directory containing original service CSV logs.
        drift_percentages: List of drift percentages (e.g. [5.0, 10.0, 20.0]).
        output_dir: Optional custom output directory (only allowed when len(drift_percentages) == 1).
        drift_rules: Optional custom span mutation mapping rules.

    Returns:
        Dictionary mapping each drift_percentage to its corresponding summary dict.

    Raises:
        ValueError: If multiple drift percentages are provided with a custom output_dir.
    """
    if output_dir is not None and len(drift_percentages) > 1:
        raise ValueError(
            "Custom --output-dir can only be specified when generating logs for a single drift percentage."
        )

    results: Dict[float, Dict[str, Any]] = {}
    for drift in drift_percentages:
        summary = generate_drift_logs(
            logs_dir=logs_dir,
            drift_percentage=drift,
            output_dir=output_dir,
            drift_rules=drift_rules,
        )
        results[float(drift)] = summary

    return results


def build_parser() -> argparse.ArgumentParser:
    """Build the CLI argument parser for label drift log generation."""
    parser = argparse.ArgumentParser(
        description="Generate deterministic telemetry label drift service event logs "
                    "with strict immutability guarantees for source logs."
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
        help="One or more drift percentages to simulate (e.g. --drift 5 or --drift 0 2.5 5 7.5 10 20). Default: 5.0.",
    )
    parser.add_argument(
        "--output-dir",
        type=str,
        default=None,
        help="Explicit output directory path (valid only when specifying a single drift percentage).",
    )
    return parser


def main(argv: Optional[List[str]] = None) -> int:
    """Main CLI execution routine."""
    parser = build_parser()
    args = parser.parse_args(argv)

    try:
        results = generate_drift_logs_batch(
            logs_dir=args.logs_dir,
            drift_percentages=args.drift,
            output_dir=args.output_dir,
        )

        for drift, summary in results.items():
            tag = format_drift_tag(drift)
            summary_file = f"drift_{tag}.summary.json"
            print(
                f"Generated drift logs for drift={drift}% in '{summary['output_dir']}' "
                f"({summary['total_mutated_events']} events mutated across "
                f"{summary['total_mutated_cases']}/{summary['total_cases']} cases, "
                f"summary saved to '{summary_file}')."
            )

        return 0

    except Exception as exc:
        sys.stderr.write(f"Error during drift log generation: {exc}\n")
        return 1


if __name__ == "__main__":
    sys.exit(main())
