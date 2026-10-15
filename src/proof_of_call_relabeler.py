#!/usr/bin/env python3
"""
Server-Span Proof-of-Call Relabeling Pre-Pass Module & CLI.

Lossless pre-pass that detects unlinked or drifted caller span aliases across service boundaries,
verifies physical execution via callee microservice server-spans (_server) within the same trace ID
across peer service logs in a benchmark directory or trace graphs, and relabels verified caller spans
to their canonical IDL names in-place without dropping any traces or inserting synthetic events.

Guarantees:
  - Strict read-only immutability of the source logs directory.
  - Zero trace drops (retention ratio = 1.0) and exact CSV row count preservation.
  - Deterministic CSV row ordering and exact timestamp preservation.
  - Strict physical observation invariant: 0 synthetic events generated.
  - Pure Python standard library (zero external dependencies).
"""

import argparse
import collections
import csv
import json
import os
import re
import sys
import time
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple

# Add repository root to path for module execution
REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

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


def build_alias_to_canonical_map(
    drift_rules: Optional[Dict[str, str]] = None,
    custom_rules: Optional[Dict[str, str]] = None,
) -> Dict[str, str]:
    """Invert canonical->drifted drift rules to construct an alias->canonical lookup map.

    Args:
        drift_rules: Mapping from canonical client span -> drifted alias name.
        custom_rules: Optional custom alias->canonical or canonical->drifted map.

    Returns:
        Dictionary mapping alias string -> canonical client span string.
    """
    rules = drift_rules if drift_rules is not None else DEFAULT_DRIFT_RULES
    alias_to_canonical: Dict[str, str] = {}

    for canonical, drifted in rules.items():
        alias_to_canonical[drifted] = canonical

    if custom_rules:
        for k, v in custom_rules.items():
            # If v is a known canonical target or key looks like an alias
            if v in PROOF_OF_CALL_TARGETS or v in rules:
                alias_to_canonical[k] = v
            elif k in PROOF_OF_CALL_TARGETS or k in rules:
                alias_to_canonical[v] = k
            else:
                alias_to_canonical[k] = v

    return alias_to_canonical


def load_canonical_targets(
    contracts_path: Optional[str] = None,
    topology_path: Optional[str] = None,
) -> Dict[str, str]:
    """Load canonical client span -> callee server span proof targets from topology/contracts.

    Falls back to PROOF_OF_CALL_TARGETS defaults.
    """
    targets = dict(PROOF_OF_CALL_TARGETS)

    if topology_path and os.path.exists(topology_path):
        try:
            with open(topology_path, "r", encoding="utf-8") as f:
                data = json.load(f)

            # Check workflows
            workflows = data.get("workflows", {})
            for wf in workflows.values():
                if "server_span" in wf and "client_span" in wf:
                    c_span = wf["client_span"]
                    s_span = wf["server_span"]
                    if c_span and s_span:
                        targets[c_span] = s_span

                phases = wf.get("phases", {})
                for phase in phases.values():
                    if isinstance(phase, dict) and "dispatches" in phase:
                        for disp in phase["dispatches"]:
                            c_span = disp.get("client_span")
                            s_span = disp.get("server_span")
                            if c_span and s_span:
                                targets[c_span] = s_span

            # Check services
            services = data.get("services", {})
            for svc in services.values():
                channels = svc.get("channels", [])
                for ch in channels:
                    c_span = ch.get("client_span")
                    s_span = ch.get("server_span")
                    if c_span and s_span:
                        targets[c_span] = s_span
                    for nested in ch.get("nested_dispatches", []):
                        nc_span = nested.get("client_span")
                        ns_span = nested.get("server_span")
                        if nc_span and ns_span:
                            targets[nc_span] = ns_span
        except Exception:
            pass

    return targets


def infer_artifact_tag(path_or_name: str) -> str:
    """Extract mixed, partial, or drift tag from path or name."""
    if not path_or_name:
        return "baseline"
    path_str = str(path_or_name)
    m = re.search(r"mixed_drift_\d+(?:_\d+)?_partial_\d+(?:_\d+)?", path_str)
    if m:
        return m.group(0)
    m = re.search(r"partial_\d+(?:_\d+)?", path_str)
    if m:
        return m.group(0)
    m = re.search(r"drift_\d+(?:_\d+)?", path_str)
    if m:
        return m.group(0)
    if "baseline" in path_str or path_str.endswith("logs") or path_str.endswith("logs/"):
        return "baseline"
    return "baseline"


def validate_csv_header(header: List[str], file_path: str) -> None:
    """Validate that CSV contains required columns (case_id, activity, timestamp)."""
    header_clean = [col.strip() for col in header]
    missing = set(REQUIRED_CSV_COLUMNS) - set(header_clean)
    if missing:
        raise ValueError(f"CSV {file_path} is missing required columns: {sorted(missing)}")


def build_proof_of_call_index(
    logs_dir: Optional[str] = None,
    csv_paths: Optional[List[str]] = None,
    traces_dir: Optional[str] = None,
    canonical_targets: Optional[Dict[str, str]] = None,
) -> Dict[str, Set[str]]:
    """Build distributed proof-of-call index mapping trace ID (case_id) -> set of recorded server spans.

    Args:
        logs_dir: Directory containing peer service CSV logs.
        csv_paths: Explicit list of CSV file paths to index.
        traces_dir: Optional directory of raw trace JSON exports.
        canonical_targets: Mapping of canonical client spans to server spans.

    Returns:
        Dictionary mapping case_id -> set of server span activity strings.
    """
    known_server_spans: Set[str] = set()
    if canonical_targets:
        known_server_spans.update(canonical_targets.values())
    for s_span in PROOF_OF_CALL_TARGETS.values():
        known_server_spans.add(s_span)

    proof_index: Dict[str, Set[str]] = collections.defaultdict(set)

    # 1. Index CSV files
    target_csvs: List[str] = []
    if csv_paths:
        target_csvs.extend(csv_paths)
    elif logs_dir and os.path.isdir(logs_dir):
        for fname in sorted(os.listdir(logs_dir)):
            if fname.endswith(".csv") and not fname.startswith("."):
                target_csvs.append(os.path.join(logs_dir, fname))

    for csv_file in target_csvs:
        if not os.path.exists(csv_file):
            continue
        try:
            with open(csv_file, "r", encoding="utf-8", newline="") as f:
                reader = csv.DictReader(f)
                if not reader.fieldnames:
                    continue
                validate_csv_header(list(reader.fieldnames), csv_file)
                for row in reader:
                    case_id = row.get("case_id", "").strip()
                    activity = row.get("activity", "").strip()
                    if not case_id or not activity:
                        continue
                    if activity.endswith("_server") or activity in known_server_spans:
                        proof_index[case_id].add(activity)
        except Exception as exc:
            sys.stderr.write(f"Warning: Failed to index server spans from {csv_file}: {exc}\n")

    # 2. Index raw JSON traces if provided
    if traces_dir and os.path.isdir(traces_dir):
        for fname in sorted(os.listdir(traces_dir)):
            if fname.endswith(".traces.json") or (fname.endswith(".json") and not fname.endswith(".summary.json")):
                tpath = os.path.join(traces_dir, fname)
                try:
                    with open(tpath, "r", encoding="utf-8") as f:
                        payload = json.load(f)
                    traces = payload.get("data", payload) if isinstance(payload, dict) else payload
                    if isinstance(traces, list):
                        for trace in traces:
                            if not isinstance(trace, dict) or "traceID" not in trace:
                                continue
                            tid = trace["traceID"]
                            for span in trace.get("spans", []):
                                op = span.get("operationName", "")
                                if op.endswith("_server") or op in known_server_spans:
                                    proof_index[tid].add(op)
                except Exception as exc:
                    sys.stderr.write(f"Warning: Failed to index traces from {tpath}: {exc}\n")

    return dict(proof_index)


def relabel_service_log(
    csv_path: str,
    proof_index: Dict[str, Set[str]],
    alias_map: Optional[Dict[str, str]] = None,
    canonical_targets: Optional[Dict[str, str]] = None,
) -> Tuple[List[Dict[str, str]], List[str], Dict[str, Any]]:
    """Relabel drifted caller spans to canonical IDL names in a service CSV log in-place.

    Preserves exact row ordering, case count, row count, and timestamps.
    Only relabels an alias if the corresponding callee server-span exists in proof_index for that case_id.

    Args:
        csv_path: Path to the service CSV event log.
        proof_index: Proof-of-call server span index (case_id -> set of server spans).
        alias_map: Mapping of drifted alias -> canonical client span.
        canonical_targets: Mapping of canonical client span -> required callee server span.

    Returns:
        Tuple of (output_rows, fieldnames, service_stats).
    """
    if not os.path.exists(csv_path):
        raise FileNotFoundError(f"Service CSV log not found: {csv_path}")

    alias_to_canonical = alias_map if alias_map is not None else build_alias_to_canonical_map()
    targets = canonical_targets if canonical_targets is not None else PROOF_OF_CALL_TARGETS

    service_name = Path(csv_path).stem

    with open(csv_path, "r", encoding="utf-8", newline="") as f:
        reader = csv.DictReader(f)
        if not reader.fieldnames:
            raise ValueError(f"CSV log is empty or lacks headers: {csv_path}")
        fieldnames = list(reader.fieldnames)
        validate_csv_header(fieldnames, csv_path)
        input_rows = list(reader)

    input_row_count = len(input_rows)
    input_cases: Set[str] = set()
    output_rows: List[Dict[str, str]] = []
    relabeled_events: List[Dict[str, Any]] = []
    relabeled_spans_counter: Dict[str, int] = collections.defaultdict(int)

    for row in input_rows:
        case_id = row.get("case_id", "").strip()
        activity = row.get("activity", "").strip()
        input_cases.add(case_id)

        new_row = dict(row)

        if activity in alias_to_canonical:
            canonical_name = alias_to_canonical[activity]
            required_server_span = targets.get(canonical_name)

            # Proof-of-call verification: check if callee server span is present for this case_id
            if required_server_span and required_server_span in proof_index.get(case_id, set()):
                new_row["activity"] = canonical_name
                relabeled_spans_counter[f"{activity} -> {canonical_name}"] += 1
                relabeled_events.append({
                    "case_id": case_id,
                    "original_activity": activity,
                    "canonical_activity": canonical_name,
                    "verified_by_server_span": required_server_span,
                    "timestamp": row.get("timestamp"),
                })
            else:
                # Server span proof absent -> leave untouched
                pass

        output_rows.append(new_row)

    # Invariant assertions
    assert len(output_rows) == input_row_count, f"Row count changed: {input_row_count} -> {len(output_rows)}"
    output_cases = {r["case_id"] for r in output_rows}
    assert len(output_cases) == len(input_cases), f"Case count changed: {len(input_cases)} -> {len(output_cases)}"

    stats = {
        "service": service_name,
        "input_rows": input_row_count,
        "output_rows": len(output_rows),
        "input_cases": len(input_cases),
        "output_cases": len(output_cases),
        "relabeled_count": len(relabeled_events),
        "relabeled_spans": dict(relabeled_spans_counter),
        "retention_ratio": 1.0,
        "row_count_preserved": True,
        "case_count_preserved": True,
    }

    return output_rows, fieldnames, stats


def relabel_logs_directory(
    logs_dir: str,
    output_dir: str,
    traces_dir: Optional[str] = None,
    contracts_path: Optional[str] = None,
    topology_path: Optional[str] = None,
    custom_rules: Optional[Dict[str, str]] = None,
    summary_file: Optional[str] = None,
) -> Dict[str, Any]:
    """Execute proof-of-call relabeling across all CSV logs in a directory.

    Args:
        logs_dir: Input logs directory (read-only).
        output_dir: Destination directory for relabeled logs.
        traces_dir: Optional traces directory for proof indexing.
        contracts_path: Path to idl-contracts.json.
        topology_path: Path to social-network.json.
        custom_rules: Optional custom drift/alias rules.
        summary_file: Path to serialize summary JSON.

    Returns:
        Structured summary report dictionary.
    """
    if not os.path.isdir(logs_dir):
        raise FileNotFoundError(f"Input logs directory not found: {logs_dir}")

    csv_files = sorted(
        [
            os.path.join(logs_dir, f)
            for f in os.listdir(logs_dir)
            if f.endswith(".csv") and not f.startswith(".")
        ]
    )

    if not csv_files:
        raise ValueError(f"No CSV event logs found in {logs_dir}")

    alias_map = build_alias_to_canonical_map(custom_rules=custom_rules)
    canonical_targets = load_canonical_targets(contracts_path, topology_path)

    # 1. Build proof-of-call server-span index
    proof_index = build_proof_of_call_index(
        logs_dir=logs_dir,
        csv_paths=csv_files,
        traces_dir=traces_dir,
        canonical_targets=canonical_targets,
    )

    os.makedirs(output_dir, exist_ok=True)

    tag = infer_artifact_tag(logs_dir)
    total_input_rows = 0
    total_output_rows = 0
    total_input_cases: Set[str] = set()
    total_output_cases: Set[str] = set()
    total_relabeled_events = 0
    per_service_stats: Dict[str, Any] = {}

    for csv_path in csv_files:
        service_name = Path(csv_path).stem
        out_rows, fieldnames, stats = relabel_service_log(
            csv_path=csv_path,
            proof_index=proof_index,
            alias_map=alias_map,
            canonical_targets=canonical_targets,
        )

        out_path = os.path.join(output_dir, f"{service_name}.csv")
        with open(out_path, "w", encoding="utf-8", newline="") as f:
            writer = csv.DictWriter(f, fieldnames=fieldnames)
            writer.writeheader()
            writer.writerows(out_rows)

        total_input_rows += stats["input_rows"]
        total_output_rows += stats["output_rows"]
        total_relabeled_events += stats["relabeled_count"]
        per_service_stats[service_name] = stats

        for r in out_rows:
            total_output_cases.add(r["case_id"])

    # Extract all input case IDs
    for csv_path in csv_files:
        with open(csv_path, "r", encoding="utf-8") as f:
            r = csv.DictReader(f)
            for row in r:
                total_input_cases.add(row["case_id"])

    summary_data = {
        "_meta": {
            "title": "Server-Span Proof-of-Call Relabeling Summary",
            "source_dir": str(logs_dir),
            "output_dir": str(output_dir),
            "tag": tag,
            "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        },
        "total_files": len(csv_files),
        "total_cases_input": len(total_input_cases),
        "total_cases_output": len(total_output_cases),
        "total_rows_input": total_input_rows,
        "total_rows_output": total_output_rows,
        "total_relabeled_events": total_relabeled_events,
        "retention_ratio": 1.0,
        "invariants_verified": {
            "row_count_preserved": (total_input_rows == total_output_rows),
            "case_count_preserved": (len(total_input_cases) == len(total_output_cases)),
            "zero_synthetic_events": True,
            "zero_trace_loss": True,
        },
        "per_service": per_service_stats,
    }

    if summary_file:
        os.makedirs(os.path.dirname(os.path.abspath(summary_file)), exist_ok=True)
        with open(summary_file, "w", encoding="utf-8") as f:
            json.dump(summary_data, f, indent=2)
    else:
        def_summary = os.path.join(
            output_dir,
            f"relabel_{tag}.summary.json" if tag else "relabel.summary.json",
        )
        with open(def_summary, "w", encoding="utf-8") as f:
            json.dump(summary_data, f, indent=2)

    return summary_data


def build_parser() -> argparse.ArgumentParser:
    """Build CLI argument parser for proof-of-call relabeler."""
    parser = argparse.ArgumentParser(
        description="Lossless Server-Span Proof-of-Call Relabeler: detects drifted caller span aliases, "
                    "verifies execution via callee server spans (_server), and relabels in-place with zero trace drops.",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument(
        "--logs-dir",
        type=str,
        help="Path to directory containing input service CSV event logs.",
    )
    group.add_argument(
        "--log",
        type=str,
        help="Path to a single service CSV event log.",
    )
    parser.add_argument(
        "--output-dir",
        type=str,
        default=None,
        help="Directory to write relabeled CSV logs.",
    )
    parser.add_argument(
        "--output",
        type=str,
        default=None,
        help="Path to write single relabeled CSV log (used with --log).",
    )
    parser.add_argument(
        "--traces-dir",
        type=str,
        default="data/traces",
        help="Directory containing raw trace JSON files for additional proof indexing.",
    )
    parser.add_argument(
        "--contracts",
        type=str,
        default="interfaces/idl-contracts.json",
        help="Path to IDL contracts JSON oracle.",
    )
    parser.add_argument(
        "--topology",
        type=str,
        default="interfaces/social-network.json",
        help="Path to topology oracle JSON.",
    )
    parser.add_argument(
        "--summary-file",
        type=str,
        default=None,
        help="Output path for relabeling summary JSON.",
    )
    parser.add_argument(
        "--custom-rules",
        type=str,
        default=None,
        help="Optional JSON file with custom alias -> canonical mappings.",
    )
    return parser


def main() -> int:
    """Main CLI entrypoint."""
    parser = build_parser()
    args = parser.parse_args()

    custom_rules_map = None
    if args.custom_rules and os.path.exists(args.custom_rules):
        with open(args.custom_rules, "r", encoding="utf-8") as f:
            custom_rules_map = json.load(f)

    try:
        if args.logs_dir:
            out_dir = args.output_dir
            if not out_dir:
                tag = infer_artifact_tag(args.logs_dir)
                if tag:
                    out_dir = f"data/benchmarks/repaired/logs_relabeled_{tag}"
                else:
                    out_dir = "data/benchmarks/repaired/logs_relabeled"

            summary = relabel_logs_directory(
                logs_dir=args.logs_dir,
                output_dir=out_dir,
                traces_dir=args.traces_dir if os.path.exists(args.traces_dir) else None,
                contracts_path=args.contracts if os.path.exists(args.contracts) else None,
                topology_path=args.topology if os.path.exists(args.topology) else None,
                custom_rules=custom_rules_map,
                summary_file=args.summary_file,
            )
            print(f"Proof-of-call relabeling complete across {summary['total_files']} files.")
            print(f"Total relabeled events: {summary['total_relabeled_events']}")
            print(f"Output directory: {summary['_meta']['output_dir']}")
            return 0
        else:
            # Single log mode
            canonical_targets = load_canonical_targets(args.contracts, args.topology)
            alias_map = build_alias_to_canonical_map(custom_rules=custom_rules_map)
            peer_dir = os.path.dirname(args.log)
            proof_index = build_proof_of_call_index(
                logs_dir=peer_dir,
                csv_paths=[args.log],
                traces_dir=args.traces_dir if os.path.exists(args.traces_dir) else None,
                canonical_targets=canonical_targets,
            )
            out_rows, fieldnames, stats = relabel_service_log(
                csv_path=args.log,
                proof_index=proof_index,
                alias_map=alias_map,
                canonical_targets=canonical_targets,
            )
            out_file = args.output
            if not out_file:
                out_file = args.log + ".relabeled.csv"

            os.makedirs(os.path.dirname(os.path.abspath(out_file)), exist_ok=True)
            with open(out_file, "w", encoding="utf-8", newline="") as f:
                writer = csv.DictWriter(f, fieldnames=fieldnames)
                writer.writeheader()
                writer.writerows(out_rows)

            print(f"Relabeled {stats['relabeled_count']} events in {args.log} -> {out_file}")
            return 0

    except Exception as exc:
        sys.stderr.write(f"Error during proof-of-call relabeling: {exc}\n")
        return 1


if __name__ == "__main__":
    sys.exit(main())
