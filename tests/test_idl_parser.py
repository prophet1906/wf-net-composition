#!/usr/bin/env python3
"""
Unit and integration tests for Thrift IDL parser and Zero-Optional Contractual Oracle.
"""

import json
import os
import tempfile
import unittest

import sys
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from src.idl_parser import (
    InvariantViolationError,
    ThriftParser,
    parse_thrift_file,
    pascal_or_camel_to_kebab,
    strip_comments,
)


class TestThriftParser(unittest.TestCase):

    def setUp(self):
        self.idl_path = os.path.join(
            os.path.dirname(__file__), "..", "IDL", "social_network.thrift"
        )

    def test_kebab_case_conversion(self):
        self.assertEqual(pascal_or_camel_to_kebab("ComposePostService"), "compose-post-service")
        self.assertEqual(pascal_or_camel_to_kebab("UniqueIdService"), "unique-id-service")
        self.assertEqual(pascal_or_camel_to_kebab("UserService"), "user-service")
        self.assertEqual(pascal_or_camel_to_kebab("SocialGraphService"), "social-graph-service")

    def test_strip_comments(self):
        text = """
        // Single line comment
        # Another single line comment
        /* Multi-line
           comment block */
        struct Sample {
            1: i64 id; // inline comment
        }
        """
        cleaned = strip_comments(text)
        self.assertNotIn("Single line comment", cleaned)
        self.assertNotIn("Another single line comment", cleaned)
        self.assertNotIn("comment block", cleaned)
        self.assertIn("struct Sample", cleaned)
        self.assertIn("1: i64 id", cleaned)

    def test_parse_social_network_thrift(self):
        contracts = parse_thrift_file(self.idl_path)

        # Invariant and metadata check
        self.assertTrue(contracts["_meta"]["zero_optional_verified"])
        self.assertEqual(contracts["_meta"]["idl_file"], "social_network.thrift")

        # Check all 11 services are present
        expected_services = [
            "unique-id-service",
            "text-service",
            "user-service",
            "compose-post-service",
            "post-storage-service",
            "home-timeline-service",
            "user-timeline-service",
            "social-graph-service",
            "user-mention-service",
            "url-shorten-service",
            "media-service",
        ]
        services = contracts["services"]
        for expected in expected_services:
            self.assertIn(expected, services, f"Missing service {expected}")

        # Test IP-1 classification on void return methods
        compose_post_channels = services["compose-post-service"]["channels"]
        self.assertEqual(len(compose_post_channels), 1)
        self.assertEqual(compose_post_channels[0]["name"], "ComposePost")
        self.assertEqual(compose_post_channels[0]["pattern"], "IP-1")
        self.assertEqual(compose_post_channels[0]["return_type"], "void")

        store_post_channel = next(
            c for c in services["post-storage-service"]["channels"] if c["name"] == "StorePost"
        )
        self.assertEqual(store_post_channel["pattern"], "IP-1")
        self.assertEqual(store_post_channel["return_type"], "void")

        # Test IP-4 classification on non-void return methods
        compose_uid = next(
            c for c in services["unique-id-service"]["channels"] if c["name"] == "ComposeUniqueId"
        )
        self.assertEqual(compose_uid["pattern"], "IP-4")
        self.assertEqual(compose_uid["return_type"], "i64")

        read_posts = next(
            c for c in services["post-storage-service"]["channels"] if c["name"] == "ReadPosts"
        )
        self.assertEqual(read_posts["pattern"], "IP-4")
        self.assertEqual(read_posts["return_type"], "list<Post>")

    def test_zero_optional_invariant_violation_in_struct(self):
        bad_thrift = """
        struct BadUser {
            1: i64 id;
            2: optional string bio;
        }
        service BadService {
            void DoSomething(1: i64 req_id)
        }
        """
        parser = ThriftParser(bad_thrift, "bad.thrift")
        with self.assertRaises(InvariantViolationError) as ctx:
            parser.parse()
        self.assertIn("is marked optional", str(ctx.exception))

    def test_zero_optional_invariant_violation_in_exception(self):
        bad_thrift = """
        exception BadException {
            1: i32 code;
            2: optional string detail;
        }
        service BadService {
            void DoSomething(1: i64 req_id) throws (1: BadException be)
        }
        """
        parser = ThriftParser(bad_thrift, "bad.thrift")
        with self.assertRaises(InvariantViolationError) as ctx:
            parser.parse()
        self.assertIn("is marked optional", str(ctx.exception))

    def test_zero_optional_invariant_violation_in_method_arg(self):
        bad_thrift = """
        service BadService {
            void DoSomething(1: i64 req_id, 2: optional string filter)
        }
        """
        parser = ThriftParser(bad_thrift, "bad.thrift")
        with self.assertRaises(InvariantViolationError) as ctx:
            parser.parse()
        self.assertIn("is marked optional", str(ctx.exception))

    def test_file_output_generation(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            out_file = os.path.join(tmpdir, "interfaces", "idl-contracts.json")
            parse_thrift_file(self.idl_path, output_path=out_file)

            self.assertTrue(os.path.exists(out_file))
            with open(out_file, "r", encoding="utf-8") as f:
                data = json.load(f)
            self.assertTrue(data["_meta"]["zero_optional_verified"])
            self.assertIn("services", data)
            self.assertGreaterEqual(len(data["services"]), 11)


if __name__ == "__main__":
    unittest.main()
