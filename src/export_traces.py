#!/usr/bin/env python3
"""
Jaeger Trace Collector, Normalizer, and Exporter.

Ingests Jaeger/OTLP microservice distributed trace spans from live telemetry endpoints
or local JSON trace export files (data/traces/<flow>.traces.json), validates trace and span
schemas, and emits workflow-level trace summaries (data/traces/export.summary.json).
"""

import argparse
import json
import os
import sys
import urllib.request
from typing import Any, Dict, List, Optional, Set


class TraceValidationError(Exception):
    """Raised when a trace or span fails schema validation."""
    pass


def validate_span_schema(span: Dict[str, Any], trace_id: str, processes: Dict[str, Any]) -> None:
    """Validate schema for an individual Jaeger span."""
    if not isinstance(span, dict):
        raise TraceValidationError(f"Trace {trace_id}: Span must be a JSON object, got {type(span).__name__}")

    for required_field in ("spanID", "operationName", "startTime", "processID"):
        if required_field not in span:
            raise TraceValidationError(
                f"Trace {trace_id}: Span {span.get('spanID', 'unknown')} missing required field '{required_field}'"
            )

    process_id = span["processID"]
    if process_id not in processes:
        raise TraceValidationError(
            f"Trace {trace_id}: Span {span['spanID']} references unknown processID '{process_id}'"
        )

    proc = processes[process_id]
    if not isinstance(proc, dict) or "serviceName" not in proc:
        raise TraceValidationError(
            f"Trace {trace_id}: Process '{process_id}' missing required 'serviceName' attribute"
        )


def validate_trace_schema(trace: Dict[str, Any]) -> None:
    """Validate schema for a complete Jaeger trace object."""
    if not isinstance(trace, dict):
        raise TraceValidationError(f"Trace must be a JSON object, got {type(trace).__name__}")

    for required_field in ("traceID", "spans", "processes"):
        if required_field not in trace:
            raise TraceValidationError(f"Trace missing required field '{required_field}'")

    trace_id = trace["traceID"]
    if not isinstance(trace_id, str) or not trace_id:
        raise TraceValidationError(f"Invalid or empty traceID: {trace_id!r}")

    spans = trace["spans"]
    if not isinstance(spans, list):
        raise TraceValidationError(f"Trace {trace_id}: 'spans' must be a list, got {type(spans).__name__}")

    processes = trace["processes"]
    if not isinstance(processes, dict):
        raise TraceValidationError(f"Trace {trace_id}: 'processes' must be a dict, got {type(processes).__name__}")

    for span in spans:
        validate_span_schema(span, trace_id, processes)


def load_trace_file(filepath: str) -> List[Dict[str, Any]]:
    """Load and validate trace records from a JSON file.
    
    Supports both raw trace arrays `[...]` and Jaeger HTTP API envelope format `{"data": [...]}`.
    """
    if not os.path.exists(filepath):
        raise FileNotFoundError(f"Trace file not found: {filepath}")

    with open(filepath, "r", encoding="utf-8") as f:
        payload = json.load(f)

    if isinstance(payload, dict) and "data" in payload:
        traces = payload["data"]
    elif isinstance(payload, list):
        traces = payload
    else:
        raise TraceValidationError(f"Trace file {filepath} must contain a JSON array or envelope with 'data' array")

    if not isinstance(traces, list):
        raise TraceValidationError(f"Trace payload in {filepath} must be a list of traces")

    for trace in traces:
        validate_trace_schema(trace)

    return traces


def fetch_traces_from_jaeger(jaeger_url: str, service_or_op: str, limit: int = 1000) -> List[Dict[str, Any]]:
    """Fetch trace data from a live Jaeger HTTP Query API endpoint."""
    url = f"{jaeger_url.rstrip('/')}/api/traces?service={service_or_op}&limit={limit}"
    req = urllib.request.Request(
        url,
        headers={"User-Agent": "gwf-net-composition-trace-exporter/1.0", "Accept": "application/json"}
    )
    with urllib.request.urlopen(req) as resp:
        if resp.status != 200:
            raise RuntimeError(f"Jaeger query to {url} returned HTTP status {resp.status}")
        raw_data = resp.read().decode("utf-8")

    payload = json.loads(raw_data)
    traces = payload.get("data", [])
    if not isinstance(traces, list):
        raise TraceValidationError(f"Unexpected Jaeger response payload from {url}")

    for trace in traces:
        validate_trace_schema(trace)

    return traces


def summarize_traces(traces: List[Dict[str, Any]]) -> Dict[str, Any]:
    """Generate flow-level summary dictionary from a collection of traces."""
    total_traces = len(traces)
    total_spans = sum(len(t.get("spans", [])) for t in traces)
    services_set: Set[str] = set()

    for trace in traces:
        processes = trace.get("processes", {})
        for proc in processes.values():
            if isinstance(proc, dict) and "serviceName" in proc:
                services_set.add(proc["serviceName"])

    return {
        "traces": total_traces,
        "total_spans": total_spans,
        "services_touched": sorted(services_set),
    }


def export_traces(
    flows: Optional[List[str]] = None,
    traces_dir: str = "data/traces",
    jaeger_url: Optional[str] = None,
    summary_file: Optional[str] = None
) -> Dict[str, Any]:
    """Export and summarize traces across one or more flows."""
    if flows is None or len(flows) == 0:
        # Default known flows or discover existing .traces.json in directory
        default_flows = ["compose-post", "read-home-timeline", "read-user-timeline"]
        if os.path.exists(traces_dir) and not jaeger_url:
            discovered = []
            for fname in sorted(os.listdir(traces_dir)):
                if fname.endswith(".traces.json"):
                    flow_name = fname[:-12]
                    discovered.append(flow_name)
            flows = discovered if discovered else default_flows
        else:
            flows = default_flows

    if summary_file is None:
        summary_file = os.path.join(traces_dir, "export.summary.json")

    os.makedirs(traces_dir, exist_ok=True)
    combined_summary: Dict[str, Any] = {}

    for flow in flows:
        trace_file = os.path.join(traces_dir, f"{flow}.traces.json")
        if jaeger_url:
            traces = fetch_traces_from_jaeger(jaeger_url, flow)
            with open(trace_file, "w", encoding="utf-8") as f:
                json.dump(traces, f, indent=1)
        else:
            traces = load_trace_file(trace_file)

        combined_summary[flow] = summarize_traces(traces)

    summary_dir = os.path.dirname(summary_file)
    if summary_dir:
        os.makedirs(summary_dir, exist_ok=True)

    with open(summary_file, "w", encoding="utf-8") as f:
        json.dump(combined_summary, f, indent=2)
        f.write("\n")

    return combined_summary


def parse_args(argv: Optional[List[str]] = None) -> argparse.Namespace:
    """Parse CLI arguments for trace export."""
    parser = argparse.ArgumentParser(
        description="Ingest, validate, and summarize Jaeger distributed traces."
    )
    parser.add_argument(
        "--traces-dir",
        default="data/traces",
        help="Directory containing or storing .traces.json files (default: data/traces)"
    )
    parser.add_argument(
        "--flows",
        nargs="*",
        default=None,
        help="Flow names to export/summarize (e.g. compose-post read-home-timeline read-user-timeline)"
    )
    parser.add_argument(
        "--jaeger-url",
        default=None,
        help="Optional Jaeger Query HTTP base URL (e.g. http://localhost:16686)"
    )
    parser.add_argument(
        "--summary-file",
        default=None,
        help="Output summary JSON file path (default: <traces-dir>/export.summary.json)"
    )
    return parser.parse_args(argv)


def main() -> None:
    """CLI entrypoint for trace export and summarization."""
    args = parse_args()
    flows = args.flows
    if flows and len(flows) == 1 and "," in flows[0]:
        flows = [f.strip() for f in flows[0].split(",") if f.strip()]

    summary = export_traces(
        flows=flows,
        traces_dir=args.traces_dir,
        jaeger_url=args.jaeger_url,
        summary_file=args.summary_file
    )

    print(f"Exported trace summaries for {len(summary)} flow(s):")
    for flow, data in summary.items():
        print(f"  - {flow}: {data['traces']} traces, {data['total_spans']} spans, {len(data['services_touched'])} services")


if __name__ == "__main__":
    main()
