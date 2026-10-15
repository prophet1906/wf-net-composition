#!/usr/bin/env python3
"""
Deterministic Service Event Log Partial Loss Generator & Invariant Verification.

Ingests service CSV event logs from an input directory, applies a deterministic tail-truncation
loss percentage (cutting events from the end of each log), and exports the truncated logs into
a distinct destination directory (defaulting to logs_partial_<percentage>).

Guarantees:
  - Strict read-only immutability of the source logs directory.
  - Deterministic row ordering and CSV header preservation.
  - Retention count K = floor(N * (1 - loss / 100)).
  - Explicit partial_<percentage> artifact and summary naming.
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


REQUIRED_CSV_COLUMNS = ["case_id", "activity", "timestamp"]


def format_loss_tag(loss_percentage: float) -> str:
    """Format a loss percentage into a clean partial tag string.
    
    Examples:
        5.0   -> "partial_5"
        10.0  -> "partial_10"
        7.5   -> "partial_7_5"
        0.0   -> "partial_0"
        100.0 -> "partial_100"
        
    Args:
        loss_percentage: Percentage of tail events to drop.
        
    Returns:
        Formatted string tag e.g. 'partial_5'.
    """
    if float(loss_percentage).is_integer():
        return f"partial_{int(loss_percentage)}"
    # Replace decimal dot with underscore for valid filesystem naming
    formatted = f"{loss_percentage:.4f}".rstrip("0").rstrip(".")
    return f"partial_{formatted.replace('.', '_')}"


def infer_partial_tag(path_or_name: str) -> Optional[str]:
    """Extract a partial tag (e.g. 'partial_5', 'partial_10', 'partial_7_5') from a directory path or string.
    
    Args:
        path_or_name: Directory path or filename string.
        
    Returns:
        Extracted tag string (e.g. 'partial_5') or None if not found.
    """
    if not path_or_name:
        return None
    match = re.search(r"partial_\d+(?:_\d+)?", str(path_or_name))
    if match:
        return match.group(0)
    return None


def format_partial_filename(base_name: str, tag: Optional[str] = None, extension: str = "") -> str:
    """Construct an artifact filename with an optional partial tag infix.
    
    Args:
        base_name: Base name of the file (e.g. 'mining' or 'compose-post-service').
        tag: Optional partial tag (e.g. 'partial_5').
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


def truncate_event_rows(
    rows: List[Dict[str, str]],
    loss_percentage: float,
) -> Tuple[List[Dict[str, str]], int, int]:
    """Apply deterministic tail-truncation to a list of event rows.
    
    Calculates K = floor(N * (1 - loss / 100)) and retains rows[:K].
    
    Args:
        rows: List of CSV row dictionaries.
        loss_percentage: Loss percentage in [0.0, 100.0].
        
    Returns:
        Tuple of (retained_rows, original_count, retained_count).
    """
    n = len(rows)
    if n == 0:
        return [], 0, 0
    
    if loss_percentage <= 0.0:
        k = n
    elif loss_percentage >= 100.0:
        k = 0
    else:
        k = math.floor(n * (1.0 - (loss_percentage / 100.0)))
    
    k = max(0, min(k, n))
    retained_rows = rows[:k]
    return retained_rows, n, k


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


def process_service_log(
    csv_path: str,
    loss_percentage: float,
    output_csv_path: str,
) -> Tuple[Dict[str, Any], Set[str]]:
    """Process a single service CSV log, perform tail truncation, and write to destination.
    
    Args:
        csv_path: Path to the source service CSV file.
        loss_percentage: Percentage of tail events to truncate.
        output_csv_path: Destination path for the truncated CSV file.
        
    Returns:
        Tuple of (service_metrics_dict, retained_case_ids_set).
        
    Raises:
        FileNotFoundError: If source CSV does not exist.
        ValueError: If CSV schema is invalid.
    """
    if not os.path.exists(csv_path):
        raise FileNotFoundError(f"Service log file not found: {csv_path}")

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

    # Map rows to dicts for column-based processing
    dict_rows = [dict(zip(header, row)) for row in rows]
    retained_dict_rows, original_events, retained_events = truncate_event_rows(
        dict_rows, loss_percentage
    )

    retained_cases = {
        row["case_id"] for row in retained_dict_rows if "case_id" in row and row["case_id"]
    }
    dropped_events = original_events - retained_events

    # Write truncated CSV to output destination
    os.makedirs(os.path.dirname(os.path.abspath(output_csv_path)), exist_ok=True)
    with open(output_csv_path, "w", encoding="utf-8", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(header)
        for r in retained_dict_rows:
            writer.writerow([r.get(col, "") for col in header])

    metrics = {
        "original_events": original_events,
        "retained_events": retained_events,
        "dropped_events": dropped_events,
        "retained_cases": len(retained_cases),
    }

    return metrics, retained_cases


def generate_partial_logs(
    logs_dir: str,
    loss_percentage: float,
    output_dir: Optional[str] = None,
) -> Dict[str, Any]:
    """Generate truncated partial service event logs for a single loss percentage.
    
    Args:
        logs_dir: Source directory containing original service CSV logs.
        loss_percentage: Loss percentage in [0.0, 100.0].
        output_dir: Optional explicit output directory. Defaults to 'logs_partial_<percentage>'.
        
    Returns:
        Structured loss summary dictionary.
        
    Raises:
        FileNotFoundError: If logs_dir does not exist.
        NotADirectoryError: If logs_dir is not a directory.
        ValueError: If loss_percentage is out of bounds, output_dir equals logs_dir, or no CSVs found.
    """
    if not os.path.exists(logs_dir):
        raise FileNotFoundError(f"Source logs directory not found: {logs_dir}")
    if not os.path.isdir(logs_dir):
        raise NotADirectoryError(f"Source path is not a directory: {logs_dir}")

    loss_float = float(loss_percentage)
    if loss_float < 0.0 or loss_float > 100.0:
        raise ValueError(
            f"Invalid loss percentage: {loss_percentage}. Must be between 0.0 and 100.0 (inclusive)."
        )

    tag = format_loss_tag(loss_float)

    # Determine output directory
    if output_dir is None:
        abs_source = os.path.abspath(logs_dir)
        parent_dir = os.path.dirname(abs_source)
        source_name = os.path.basename(abs_source)
        if os.path.basename(parent_dir) == "data" and source_name == "logs":
            resolved_output_dir = os.path.join(parent_dir, "benchmarks", "partial", f"{source_name}_{tag}")
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

    services_summary: Dict[str, Dict[str, Any]] = {}
    all_retained_cases: Set[str] = set()
    total_original_events = 0
    total_retained_events = 0
    total_dropped_events = 0

    for csv_file in csv_files:
        service_name = Path(csv_file).stem
        src_path = os.path.join(logs_dir, csv_file)
        dst_path = os.path.join(resolved_output_dir, csv_file)

        service_metrics, service_cases = process_service_log(
            csv_path=src_path,
            loss_percentage=loss_float,
            output_csv_path=dst_path,
        )

        services_summary[service_name] = service_metrics
        all_retained_cases.update(service_cases)
        total_original_events += service_metrics["original_events"]
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
        "loss_percentage": loss_float,
        "total_original_events": total_original_events,
        "total_retained_events": total_retained_events,
        "total_dropped_events": total_dropped_events,
        "retained_event_ratio": retained_ratio,
        "total_retained_cases": len(all_retained_cases),
        "services": services_summary,
    }

    # Write summary JSON with explicit partial tag naming
    summary_filename = f"loss_{tag}.summary.json"
    summary_path = os.path.join(resolved_output_dir, summary_filename)
    with open(summary_path, "w", encoding="utf-8") as f:
        json.dump(summary, f, indent=2)

    return summary


def generate_partial_logs_batch(
    logs_dir: str,
    loss_percentages: List[float],
    output_dir: Optional[str] = None,
) -> Dict[float, Dict[str, Any]]:
    """Execute batch partial log generation across multiple loss percentages.
    
    Args:
        logs_dir: Source directory containing original service CSV logs.
        loss_percentages: List of loss percentages (e.g. [5.0, 10.0, 20.0]).
        output_dir: Optional custom output directory (only allowed when len(loss_percentages) == 1).
        
    Returns:
        Dictionary mapping each loss_percentage to its corresponding summary dict.
        
    Raises:
        ValueError: If multiple loss percentages are provided with a custom output_dir.
    """
    if output_dir is not None and len(loss_percentages) > 1:
        raise ValueError(
            "Custom --output-dir can only be specified when generating logs for a single loss percentage."
        )

    results: Dict[float, Dict[str, Any]] = {}
    for loss in loss_percentages:
        summary = generate_partial_logs(
            logs_dir=logs_dir,
            loss_percentage=loss,
            output_dir=output_dir,
        )
        results[float(loss)] = summary

    return results


def build_parser() -> argparse.ArgumentParser:
    """Build the CLI argument parser for partial log generation."""
    parser = argparse.ArgumentParser(
        description="Generate deterministic tail-truncated partial service event logs "
                    "with strict immutability guarantees for source logs."
    )
    parser.add_argument(
        "--logs-dir",
        type=str,
        default="data/logs",
        help="Directory containing per-service CSV event logs (default: data/logs).",
    )
    parser.add_argument(
        "--loss",
        type=float,
        nargs="+",
        default=[5.0],
        help="One or more loss percentages to simulate (e.g. --loss 5 or --loss 5 10 20). Default: 5.0.",
    )
    parser.add_argument(
        "--output-dir",
        type=str,
        default=None,
        help="Explicit output directory path (valid only when specifying a single loss percentage).",
    )
    return parser


def main(argv: Optional[List[str]] = None) -> int:
    """Main CLI execution routine."""
    parser = build_parser()
    args = parser.parse_args(argv)

    try:
        results = generate_partial_logs_batch(
            logs_dir=args.logs_dir,
            loss_percentages=args.loss,
            output_dir=args.output_dir,
        )

        for loss, summary in results.items():
            tag = format_loss_tag(loss)
            summary_file = f"loss_{tag}.summary.json"
            print(
                f"Generated partial logs for loss={loss}% in '{summary['output_dir']}' "
                f"({summary['total_retained_events']}/{summary['total_original_events']} events retained, "
                f"summary saved to '{summary_file}')."
            )

        return 0

    except Exception as exc:
        sys.stderr.write(f"Error during partial log generation: {exc}\n")
        return 1


if __name__ == "__main__":
    sys.exit(main())
