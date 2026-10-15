#!/usr/bin/env python3
"""
Deterministic Jaeger Trace Deduplication and Service Event Log Projection.

Ingests multi-flow Jaeger trace JSON exports, enforces global traceID deduplication,
projects spans into per-service event logs (data/logs/<service>.csv) sorted deterministically
by (case_id, timestamp, activity), and calculates process mining projection summaries
(data/logs/projection.summary.json).
"""

import argparse
import collections
import csv
import json
import os
import sys
from typing import Any, Dict, List, Optional, Set, Tuple


def extract_events_from_trace(trace: Dict[str, Any]) -> Dict[str, List[Dict[str, Any]]]:
    """Extract span events grouped by serviceName from a validated trace."""
    trace_id = trace["traceID"]
    processes = trace.get("processes", {})
    spans = trace.get("spans", [])

    service_events: Dict[str, List[Dict[str, Any]]] = collections.defaultdict(list)

    for span in spans:
        process_id = span.get("processID")
        service_name = None

        if process_id and process_id in processes:
            proc = processes[process_id]
            if isinstance(proc, dict):
                service_name = proc.get("serviceName")

        if not service_name and "process" in span and isinstance(span["process"], dict):
            service_name = span["process"].get("serviceName")

        if not service_name:
            continue

        operation_name = span.get("operationName", "")
        start_time = int(span.get("startTime", 0))

        service_events[service_name].append({
            "case_id": trace_id,
            "activity": operation_name,
            "timestamp": start_time,
        })

    return service_events


def load_and_deduplicate_traces(traces_dir: str) -> Tuple[List[Dict[str, Any]], Dict[str, Any]]:
    """Load trace JSON files in deterministic order and deduplicate globally by traceID.
    
    Returns (deduplicated_traces, loading_stats).
    """
    if not os.path.exists(traces_dir):
        raise FileNotFoundError(f"Traces directory not found: {traces_dir}")

    # Discover and sort trace files deterministically
    trace_files: List[str] = []
    for fname in sorted(os.listdir(traces_dir)):
        if fname.endswith(".traces.json") or (fname.endswith(".json") and not fname.endswith(".summary.json")):
            trace_files.append(os.path.join(traces_dir, fname))

    seen_trace_ids: Set[str] = set()
    deduped_traces: List[Dict[str, Any]] = []
    total_raw_traces = 0
    duplicate_count = 0

    for filepath in trace_files:
        with open(filepath, "r", encoding="utf-8") as f:
            payload = json.load(f)

        if isinstance(payload, dict) and "data" in payload:
            file_traces = payload["data"]
        elif isinstance(payload, list):
            file_traces = payload
        else:
            continue

        for trace in file_traces:
            if not isinstance(trace, dict) or "traceID" not in trace:
                continue
            total_raw_traces += 1
            trace_id = trace["traceID"]
            if trace_id in seen_trace_ids:
                duplicate_count += 1
                continue
            seen_trace_ids.add(trace_id)
            deduped_traces.append(trace)

    stats = {
        "files_loaded": len(trace_files),
        "total_raw_traces": total_raw_traces,
        "unique_traces": len(deduped_traces),
        "duplicates_skipped": duplicate_count,
    }
    return deduped_traces, stats


def calculate_projection_metrics(service_events: Dict[str, List[Dict[str, Any]]]) -> Dict[str, Any]:
    """Calculate aggregate process mining projection metrics for all services."""
    summary: Dict[str, Any] = {}

    for service in sorted(service_events.keys()):
        events = service_events[service]
        total_events = len(events)

        # Group activities by case_id preserving deterministic order
        case_activities: Dict[str, List[str]] = collections.defaultdict(list)
        activities_set: Set[str] = set()

        for event in events:
            case_activities[event["case_id"]].append(event["activity"])
            activities_set.add(event["activity"])

        total_cases = len(case_activities)
        distinct_activities = len(activities_set)
        sorted_activities = sorted(activities_set)

        # Variant calculation
        variant_counter: collections.Counter = collections.Counter()
        for _, act_list in case_activities.items():
            variant_counter[tuple(act_list)] += 1

        distinct_variants = len(variant_counter)

        # Sort variants by frequency descending, then sequence ascending
        sorted_variant_tuples = sorted(
            variant_counter.items(),
            key=lambda item: (-item[1], item[0])
        )

        top_variants = []
        for seq_tuple, count in sorted_variant_tuples[:5]:
            top_variants.append({
                "count": count,
                "len": len(seq_tuple),
                "seq": list(seq_tuple),
            })

        summary[service] = {
            "cases": total_cases,
            "events": total_events,
            "distinct_activities": distinct_activities,
            "activities": sorted_activities,
            "distinct_variants": distinct_variants,
            "top_variants": top_variants,
        }

    return summary


def write_service_csvs(service_events: Dict[str, List[Dict[str, Any]]], output_dir: str) -> None:
    """Write per-service CSV logs sorted by (case_id, timestamp, activity)."""
    os.makedirs(output_dir, exist_ok=True)

    for service in sorted(service_events.keys()):
        events = service_events[service]
        # Deterministic sorting
        events.sort(key=lambda e: (e["case_id"], e["timestamp"], e["activity"]))

        csv_path = os.path.join(output_dir, f"{service}.csv")
        with open(csv_path, "w", newline="", encoding="utf-8") as f:
            writer = csv.writer(f)
            writer.writerow(["case_id", "activity", "timestamp"])
            for event in events:
                writer.writerow([event["case_id"], event["activity"], event["timestamp"]])


def project_traces(
    traces_dir: str = "data/traces",
    output_dir: str = "data/logs",
    summary_file: Optional[str] = None
) -> Dict[str, Any]:
    """Project deduplicated trace spans into per-service CSVs and compute summary."""
    deduped_traces, _ = load_and_deduplicate_traces(traces_dir)

    all_service_events: Dict[str, List[Dict[str, Any]]] = collections.defaultdict(list)
    for trace in deduped_traces:
        extracted = extract_events_from_trace(trace)
        for service, events in extracted.items():
            all_service_events[service].extend(events)

    # Sort events deterministically for each service
    for service, events in all_service_events.items():
        events.sort(key=lambda e: (e["case_id"], e["timestamp"], e["activity"]))

    # Write CSV files
    write_service_csvs(all_service_events, output_dir)

    # Calculate summary metrics
    summary = calculate_projection_metrics(all_service_events)

    if summary_file is None:
        summary_file = os.path.join(output_dir, "projection.summary.json")

    summary_dir = os.path.dirname(summary_file)
    if summary_dir:
        os.makedirs(summary_dir, exist_ok=True)

    with open(summary_file, "w", encoding="utf-8") as f:
        json.dump(summary, f, indent=2)
        f.write("\n")

    return summary


def parse_args(argv: Optional[List[str]] = None) -> argparse.Namespace:
    """Parse CLI arguments for trace projection."""
    parser = argparse.ArgumentParser(
        description="Deduplicate Jaeger traces and project into per-service CSV event logs."
    )
    parser.add_argument(
        "--traces-dir",
        default="data/traces",
        help="Directory containing input .traces.json files (default: data/traces)"
    )
    parser.add_argument(
        "--output-dir",
        default="data/logs",
        help="Directory to write per-service CSV logs and summary (default: data/logs)"
    )
    parser.add_argument(
        "--summary-file",
        default=None,
        help="Output summary JSON file path (default: <output-dir>/projection.summary.json)"
    )
    return parser.parse_args(argv)


def main() -> None:
    """CLI entrypoint for trace projection."""
    args = parse_args()
    summary = project_traces(
        traces_dir=args.traces_dir,
        output_dir=args.output_dir,
        summary_file=args.summary_file
    )

    print(f"Projected event logs for {len(summary)} service(s) to '{args.output_dir}':")
    for service, data in summary.items():
        print(f"  - {service}: {data['cases']} cases, {data['events']} events, {data['distinct_variants']} variants")


if __name__ == "__main__":
    main()
