#!/usr/bin/env python3
"""
Unit and invariant tests for Jaeger Trace Ingestion, Deduplication, and Service Projection.
"""

import csv
import json
import os
import shutil
import tempfile
import unittest
from unittest.mock import MagicMock, patch
import sys

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from src.export_traces import (
    TraceValidationError,
    export_traces,
    fetch_traces_from_jaeger,
    load_trace_file,
    summarize_traces,
    validate_span_schema,
    validate_trace_schema,
)
from src.project_service_traces import (
    calculate_projection_metrics,
    extract_events_from_trace,
    load_and_deduplicate_traces,
    project_traces,
    write_service_csvs,
)


class TestTraceExport(unittest.TestCase):
    """Unit tests for trace schema validation, ingestion, and flow export summarization."""

    def setUp(self):
        self.temp_dir = tempfile.mkdtemp()
        self.sample_valid_trace = {
            "traceID": "t1001",
            "spans": [
                {
                    "traceID": "t1001",
                    "spanID": "s1",
                    "operationName": "compose_post_server",
                    "startTime": 1700000000000000,
                    "duration": 5000,
                    "processID": "p1"
                },
                {
                    "traceID": "t1001",
                    "spanID": "s2",
                    "operationName": "compose_text_client",
                    "startTime": 1700000000000100,
                    "duration": 2000,
                    "processID": "p1"
                }
            ],
            "processes": {
                "p1": {
                    "serviceName": "compose-post-service",
                    "tags": []
                }
            }
        }

    def tearDown(self):
        shutil.rmtree(self.temp_dir, ignore_errors=True)

    def test_validate_trace_schema_valid(self):
        # Should not raise exception
        validate_trace_schema(self.sample_valid_trace)

    def test_validate_trace_schema_missing_fields(self):
        with self.assertRaises(TraceValidationError):
            validate_trace_schema({"spans": [], "processes": {}})

        with self.assertRaises(TraceValidationError):
            validate_trace_schema({"traceID": "t1", "processes": {}})

        with self.assertRaises(TraceValidationError):
            validate_trace_schema({"traceID": "t1", "spans": []})

    def test_validate_span_schema_invalid_process(self):
        invalid_span_trace = {
            "traceID": "t1002",
            "spans": [
                {
                    "spanID": "s1",
                    "operationName": "op1",
                    "startTime": 1000,
                    "processID": "unknown_proc"
                }
            ],
            "processes": {
                "p1": {"serviceName": "svc1"}
            }
        }
        with self.assertRaises(TraceValidationError):
            validate_trace_schema(invalid_span_trace)

    def test_load_trace_file_formats(self):
        # Test array format
        arr_path = os.path.join(self.temp_dir, "arr.json")
        with open(arr_path, "w", encoding="utf-8") as f:
            json.dump([self.sample_valid_trace], f)
        loaded = load_trace_file(arr_path)
        self.assertEqual(len(loaded), 1)
        self.assertEqual(loaded[0]["traceID"], "t1001")

        # Test Jaeger envelope format {"data": [...]}
        env_path = os.path.join(self.temp_dir, "env.json")
        with open(env_path, "w", encoding="utf-8") as f:
            json.dump({"data": [self.sample_valid_trace]}, f)
        loaded_env = load_trace_file(env_path)
        self.assertEqual(len(loaded_env), 1)
        self.assertEqual(loaded_env[0]["traceID"], "t1001")

    def test_summarize_traces(self):
        trace2 = {
            "traceID": "t1002",
            "spans": [
                {
                    "spanID": "s3",
                    "operationName": "read_user_server",
                    "startTime": 1700000000001000,
                    "processID": "p2"
                }
            ],
            "processes": {
                "p2": {"serviceName": "user-service"}
            }
        }
        summary = summarize_traces([self.sample_valid_trace, trace2])
        self.assertEqual(summary["traces"], 2)
        self.assertEqual(summary["total_spans"], 3)
        self.assertEqual(summary["services_touched"], ["compose-post-service", "user-service"])

    def test_export_traces_pipeline(self):
        flow_file = os.path.join(self.temp_dir, "sample-flow.traces.json")
        with open(flow_file, "w", encoding="utf-8") as f:
            json.dump([self.sample_valid_trace], f)

        summary_file = os.path.join(self.temp_dir, "export.summary.json")
        res = export_traces(
            flows=["sample-flow"],
            traces_dir=self.temp_dir,
            summary_file=summary_file
        )
        self.assertIn("sample-flow", res)
        self.assertEqual(res["sample-flow"]["traces"], 1)
        self.assertEqual(res["sample-flow"]["total_spans"], 2)
        self.assertTrue(os.path.exists(summary_file))

    @patch("urllib.request.urlopen")
    def test_fetch_traces_from_jaeger_mocked(self, mock_urlopen):
        mock_response = MagicMock()
        mock_response.status = 200
        mock_response.read.return_value = json.dumps({"data": [self.sample_valid_trace]}).encode("utf-8")
        mock_urlopen.return_value.__enter__.return_value = mock_response

        traces = fetch_traces_from_jaeger("http://localhost:16686", "compose-post", limit=50)
        self.assertEqual(len(traces), 1)
        self.assertEqual(traces[0]["traceID"], "t1001")

    @patch("urllib.request.urlopen")
    def test_export_traces_pipeline_with_jaeger_url(self, mock_urlopen):
        mock_response = MagicMock()
        mock_response.status = 200
        mock_response.read.return_value = json.dumps({"data": [self.sample_valid_trace]}).encode("utf-8")
        mock_urlopen.return_value.__enter__.return_value = mock_response

        summary_file = os.path.join(self.temp_dir, "live_export.summary.json")
        res = export_traces(
            flows=["live-flow"],
            traces_dir=self.temp_dir,
            jaeger_url="http://localhost:16686",
            summary_file=summary_file
        )
        self.assertIn("live-flow", res)
        self.assertEqual(res["live-flow"]["traces"], 1)
        saved_file = os.path.join(self.temp_dir, "live-flow.traces.json")
        self.assertTrue(os.path.exists(saved_file))


class TestTraceDeduplication(unittest.TestCase):
    """Invariant tests for global trace deduplication across multi-file exports."""

    def setUp(self):
        self.temp_dir = tempfile.mkdtemp()

    def tearDown(self):
        shutil.rmtree(self.temp_dir, ignore_errors=True)

    def _create_trace(self, trace_id: str, service: str, op: str, start_time: int) -> dict:
        return {
            "traceID": trace_id,
            "spans": [
                {
                    "spanID": f"span_{trace_id}",
                    "operationName": op,
                    "startTime": start_time,
                    "processID": "p1"
                }
            ],
            "processes": {
                "p1": {"serviceName": service}
            }
        }

    def test_global_trace_deduplication_invariant(self):
        # File 1: traces T1, T2
        t1 = self._create_trace("T1", "service-a", "opA", 1000)
        t2_v1 = self._create_trace("T2", "service-a", "opA_orig", 2000)

        file1 = os.path.join(self.temp_dir, "1_flow1.traces.json")
        with open(file1, "w", encoding="utf-8") as f:
            json.dump([t1, t2_v1], f)

        # File 2: traces T2 (overlapping duplicate), T3
        t2_v2 = self._create_trace("T2", "service-a", "opA_dup", 2000)
        t3 = self._create_trace("T3", "service-b", "opB", 3000)

        file2 = os.path.join(self.temp_dir, "2_flow2.traces.json")
        with open(file2, "w", encoding="utf-8") as f:
            json.dump([t2_v2, t3], f)

        deduped, stats = load_and_deduplicate_traces(self.temp_dir)
        self.assertEqual(stats["total_raw_traces"], 4)
        self.assertEqual(stats["unique_traces"], 3)
        self.assertEqual(stats["duplicates_skipped"], 1)

        loaded_ids = [t["traceID"] for t in deduped]
        self.assertEqual(loaded_ids, ["T1", "T2", "T3"])
        # Invariant: first encounter (from file 1) is preserved
        t2_loaded = [t for t in deduped if t["traceID"] == "T2"][0]
        self.assertEqual(t2_loaded["spans"][0]["operationName"], "opA_orig")


class TestCaseProjectionAndSorting(unittest.TestCase):
    """Unit tests for deterministic per-service case projection, event sorting, and CSV writing."""

    def setUp(self):
        self.temp_dir = tempfile.mkdtemp()

    def tearDown(self):
        shutil.rmtree(self.temp_dir, ignore_errors=True)

    def test_extract_events_fidelity(self):
        trace = {
            "traceID": "trace_xyz_123",
            "spans": [
                {
                    "spanID": "s1",
                    "operationName": "op_alpha",
                    "startTime": 1786190660000000,
                    "processID": "p1"
                },
                {
                    "spanID": "s2",
                    "operationName": "op_beta",
                    "startTime": 1786190660000500,
                    "processID": "p2"
                }
            ],
            "processes": {
                "p1": {"serviceName": "service-alpha"},
                "p2": {"serviceName": "service-beta"}
            }
        }
        events = extract_events_from_trace(trace)
        self.assertIn("service-alpha", events)
        self.assertIn("service-beta", events)

        # Invariant: exact zero synthetic modifications
        ev_alpha = events["service-alpha"][0]
        self.assertEqual(ev_alpha["case_id"], "trace_xyz_123")
        self.assertEqual(ev_alpha["activity"], "op_alpha")
        self.assertEqual(ev_alpha["timestamp"], 1786190660000000)

    def test_deterministic_sorting_and_csv_generation(self):
        # Multiple events with scrambled order and tie timestamps
        service_events = {
            "test-service": [
                {"case_id": "case_b", "activity": "act_2", "timestamp": 200},
                {"case_id": "case_a", "activity": "act_z", "timestamp": 100},
                {"case_id": "case_a", "activity": "act_a", "timestamp": 100}, # Same timestamp tie break by activity
                {"case_id": "case_b", "activity": "act_1", "timestamp": 150},
            ]
        }
        logs_dir = os.path.join(self.temp_dir, "logs")
        write_service_csvs(service_events, logs_dir)

        csv_file = os.path.join(logs_dir, "test-service.csv")
        self.assertTrue(os.path.exists(csv_file))

        with open(csv_file, "r", encoding="utf-8") as f:
            reader = list(csv.reader(f))

        # Check header
        self.assertEqual(reader[0], ["case_id", "activity", "timestamp"])

        # Check deterministic row ordering: (case_id, timestamp, activity)
        # Expected:
        # 1. case_a, act_a, 100
        # 2. case_a, act_z, 100
        # 3. case_b, act_1, 150
        # 4. case_b, act_2, 200
        self.assertEqual(reader[1], ["case_a", "act_a", "100"])
        self.assertEqual(reader[2], ["case_a", "act_z", "100"])
        self.assertEqual(reader[3], ["case_b", "act_1", "150"])
        self.assertEqual(reader[4], ["case_b", "act_2", "200"])


class TestProjectionSummaryMetrics(unittest.TestCase):
    """Unit tests for process mining summary metrics and variant calculations."""

    def test_variant_calculation(self):
        service_events = {
            "order-service": [
                # Case 1: create -> validate -> pay
                {"case_id": "c1", "activity": "create", "timestamp": 10},
                {"case_id": "c1", "activity": "validate", "timestamp": 20},
                {"case_id": "c1", "activity": "pay", "timestamp": 30},
                # Case 2: create -> validate -> pay (same variant)
                {"case_id": "c2", "activity": "create", "timestamp": 15},
                {"case_id": "c2", "activity": "validate", "timestamp": 25},
                {"case_id": "c2", "activity": "pay", "timestamp": 35},
                # Case 3: create -> cancel (different variant)
                {"case_id": "c3", "activity": "create", "timestamp": 5},
                {"case_id": "c3", "activity": "cancel", "timestamp": 12},
            ]
        }
        summary = calculate_projection_metrics(service_events)
        self.assertIn("order-service", summary)
        svc_metrics = summary["order-service"]

        self.assertEqual(svc_metrics["cases"], 3)
        self.assertEqual(svc_metrics["events"], 8)
        self.assertEqual(svc_metrics["distinct_activities"], 4)
        self.assertEqual(svc_metrics["activities"], ["cancel", "create", "pay", "validate"])
        self.assertEqual(svc_metrics["distinct_variants"], 2)

        top_variants = svc_metrics["top_variants"]
        self.assertEqual(len(top_variants), 2)
        # Most frequent variant: create -> validate -> pay (count 2)
        self.assertEqual(top_variants[0]["count"], 2)
        self.assertEqual(top_variants[0]["len"], 3)
        self.assertEqual(top_variants[0]["seq"], ["create", "validate", "pay"])

        # Second variant: create -> cancel (count 1)
        self.assertEqual(top_variants[1]["count"], 1)
        self.assertEqual(top_variants[1]["len"], 2)
        self.assertEqual(top_variants[1]["seq"], ["create", "cancel"])


class TestEndToEndRepoProjection(unittest.TestCase):
    """End-to-end integration test against actual repo trace exports."""

    def test_repo_traces_projection(self):
        repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
        traces_dir = os.path.join(repo_root, "data", "traces")

        with tempfile.TemporaryDirectory() as temp_output:
            summary = project_traces(traces_dir=traces_dir, output_dir=temp_output)

            # Check 12 services projected
            self.assertEqual(len(summary), 12)
            self.assertIn("compose-post-service", summary)
            self.assertIn("nginx-web-server", summary)

            # Check deduplication cardinality on nginx-web-server (1081 cases across all 3 flows)
            self.assertEqual(summary["nginx-web-server"]["cases"], 1081)
            self.assertEqual(summary["compose-post-service"]["cases"], 119)
            self.assertEqual(summary["compose-post-service"]["events"], 952)

            # Check CSV files exist
            for service in summary.keys():
                csv_path = os.path.join(temp_output, f"{service}.csv")
                self.assertTrue(os.path.exists(csv_path))


if __name__ == "__main__":
    unittest.main()
