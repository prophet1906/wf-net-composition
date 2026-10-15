#!/usr/bin/env python3
"""
Unit and Regression Tests for Topology Enricher.

Validates:
1. DeathStarBench source root resolution via argument, environment variable, and search paths.
2. Nginx Lua ingress endpoint extraction and HTTP route mapping.
3. C++ handler concurrency phase disambiguation (P1 vs P2).
4. Synchronization join barrier injection (post_assemble_barrier).
5. Nested parallel dispatch extraction (TextHandler fan-out).
6. Jaeger client/server trace span grounding.
7. End-to-end social-network.json topology oracle generation with --dsb-root argument.
"""

import json
import os
import shutil
import tempfile
import unittest
from pathlib import Path

from src.topology_enricher import (
    CppHandlerGrepExtractor,
    DSBRootResolver,
    IDLContractIngester,
    LuaIngressGrepExtractor,
    TopologyEnricher,
    pascal_to_kebab,
)


def create_mock_dsb_tree(root_dir: Path) -> None:
    """Create a minimal synthetic DeathStarBench file tree for standalone test execution."""
    # 1. Nginx Lua script
    lua_dir = root_dir / "nginx-web-server" / "lua-scripts" / "wrk2-api" / "post"
    lua_dir.mkdir(parents=True, exist_ok=True)
    compose_lua = lua_dir / "compose.lua"
    with open(compose_lua, "w", encoding="utf-8") as f:
        f.write('''
local _M = {}
function _M.ComposePost()
  local GenericObjectPool = require "GenericObjectPool"
  local social_network_ComposePostService = require "social_network_ComposePostService"
  local ComposePostServiceClient = social_network_ComposePostService.ComposePostServiceClient
  local client = GenericObjectPool:connection(ComposePostServiceClient, "compose-post-service", 9090)
  local span = tracer:start_span("compose_post_client", {})
  local post = ngx.req.get_post_args()
  status, ret = pcall(client.ComposePost, client, req_id, post.username, tonumber(post.user_id), post.text)
  span:finish()
end
return _M
''')

    # Nginx config
    conf_dir = root_dir / "nginx-web-server" / "conf"
    conf_dir.mkdir(parents=True, exist_ok=True)
    with open(conf_dir / "nginx.conf", "w", encoding="utf-8") as f:
        f.write('''
http {
  server {
    location /wrk2-api/post/compose {
      content_by_lua '
          local client = require "wrk2-api/post/compose"
          client.ComposePost();
      ';
    }
  }
}
''')

    # 2. ComposePostHandler.h
    cpp_dir = root_dir / "src" / "ComposePostService"
    cpp_dir.mkdir(parents=True, exist_ok=True)
    with open(cpp_dir / "ComposePostHandler.h", "w", encoding="utf-8") as f:
        f.write('''
#ifndef SOCIAL_NETWORK_COMPOSEPOSTHANDLER_H
#define SOCIAL_NETWORK_COMPOSEPOSTHANDLER_H

namespace social_network {

class ComposePostHandler {
  Creator _ComposeCreaterHelper(int64_t req_id, int64_t user_id, const std::string &username) {
    auto span = opentracing::Tracer::Global()->StartSpan("compose_creator_client");
    auto user_client = _user_service_client_pool->Pop()->GetClient();
    Creator _return_creator;
    user_client->ComposeCreatorWithUserId(_return_creator, req_id, user_id, username);
    span->Finish();
    return _return_creator;
  }

  TextServiceReturn _ComposeTextHelper(int64_t req_id, const std::string &text) {
    auto span = opentracing::Tracer::Global()->StartSpan("compose_text_client");
    auto text_client = _text_service_client_pool->Pop()->GetClient();
    TextServiceReturn _return_text;
    text_client->ComposeText(_return_text, req_id, text);
    span->Finish();
    return _return_text;
  }

  void _UploadPostHelper(int64_t req_id, const Post &post) {
    auto span = opentracing::Tracer::Global()->StartSpan("store_post_client");
    auto post_client = _post_storage_client_pool->Pop()->GetClient();
    post_client->StorePost(req_id, post);
    span->Finish();
  }

  void _UploadUserTimelineHelper(int64_t req_id, int64_t post_id) {
    auto span = opentracing::Tracer::Global()->StartSpan("write_user_timeline_client");
    auto user_timeline_client = _user_timeline_client_pool->Pop()->GetClient();
    user_timeline_client->WriteUserTimeline(req_id, post_id);
    span->Finish();
  }

  void ComposePost(const int64_t req_id, const std::string &username, int64_t user_id) {
    auto span = opentracing::Tracer::Global()->StartSpan("compose_post_server");

    auto text_future = std::async(std::launch::async, &ComposePostHandler::_ComposeTextHelper, this, req_id, text);
    auto creator_future = std::async(std::launch::async, &ComposePostHandler::_ComposeCreaterHelper, this, req_id, user_id, username);

    auto creator = creator_future.get();
    auto text = text_future.get();

    auto post_future = std::async(std::launch::async, &ComposePostHandler::_UploadPostHelper, this, req_id, post);
    auto user_timeline_future = std::async(std::launch::deferred, &ComposePostHandler::_UploadUserTimelineHelper, this, req_id, post.post_id);

    post_future.get();
    user_timeline_future.get();
    span->Finish();
  }
};

}
#endif
''')

    # 3. TextHandler.h with nested parallel calls
    text_dir = root_dir / "src" / "TextService"
    text_dir.mkdir(parents=True, exist_ok=True)
    with open(text_dir / "TextHandler.h", "w", encoding="utf-8") as f:
        f.write('''
#ifndef SOCIAL_NETWORK_TEXTHANDLER_H
#define SOCIAL_NETWORK_TEXTHANDLER_H

namespace social_network {

class TextHandler {
  void ComposeText(TextServiceReturn &_return, int64_t req_id, const std::string &text) {
    auto span = opentracing::Tracer::Global()->StartSpan("compose_text_server");

    auto shortened_urls_future = std::async(std::launch::async, [&]() {
      auto url_span = opentracing::Tracer::Global()->StartSpan("compose_urls_client");
      auto url_client = _url_client_pool->Pop()->GetClient();
      std::vector<Url> _return_urls;
      url_client->ComposeUrls(_return_urls, req_id, urls);
      url_span->Finish();
      return _return_urls;
    });

    auto user_mention_future = std::async(std::launch::async, [&]() {
      auto user_mention_span = opentracing::Tracer::Global()->StartSpan("compose_user_mentions_client");
      auto user_mention_client = _user_mention_client_pool->Pop()->GetClient();
      std::vector<UserMention> _return_user_mentions;
      user_mention_client->ComposeUserMentions(_return_user_mentions, req_id, mention_usernames);
      user_mention_span->Finish();
      return _return_user_mentions;
    });

    auto urls = shortened_urls_future.get();
    auto mentions = user_mention_future.get();
    span->Finish();
  }
};

}
#endif
''')


class TestDSBResolversAndIngester(unittest.TestCase):
    """Test path resolution and baseline IDL contract loading."""

    def test_idl_contract_ingestion_valid(self):
        contracts = IDLContractIngester.load("interfaces/idl-contracts.json")
        self.assertIn("services", contracts)
        self.assertIn("compose-post-service", contracts["services"])
        self.assertIn("text-service", contracts["services"])
        self.assertTrue(contracts.get("_meta", {}).get("zero_optional_verified", False))

    def test_idl_contract_ingestion_missing(self):
        with self.assertRaises(FileNotFoundError):
            IDLContractIngester.load("non_existent_file.json")

    def test_dsb_root_resolution_with_explicit_arg(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            tmp_path = Path(tmpdir).resolve()
            (tmp_path / "src").mkdir()
            resolved = DSBRootResolver.resolve(str(tmp_path))
            self.assertEqual(resolved, tmp_path)

    def test_dsb_root_resolution_invalid_arg(self):
        with self.assertRaises(FileNotFoundError):
            DSBRootResolver.resolve("/invalid/non_existent_directory_12345")


class TestGrepExtractionWithMock(unittest.TestCase):
    """Test Lua and C++ extraction using an isolated mock source tree."""

    @classmethod
    def setUpClass(cls):
        cls.temp_dir = tempfile.mkdtemp()
        cls.mock_root = Path(cls.temp_dir).resolve()
        create_mock_dsb_tree(cls.mock_root)

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.temp_dir, ignore_errors=True)

    def test_extract_ingress_endpoints(self):
        extractor = LuaIngressGrepExtractor(self.mock_root)
        endpoints = extractor.extract_ingress()
        self.assertGreaterEqual(len(endpoints), 1)

        ep = endpoints[0]
        self.assertEqual(ep.endpoint, "/wrk2-api/post/compose")
        self.assertEqual(ep.entry_service, "compose-post-service")
        self.assertEqual(ep.entry_channel, "ComposePost")
        self.assertEqual(ep.span_client, "compose_post_client")
        self.assertEqual(ep.method, "POST")
        self.assertIn("username", ep.payload_fields)
        self.assertIn("user_id", ep.payload_fields)

    def test_compose_post_handler_concurrency_and_phases(self):
        extractor = CppHandlerGrepExtractor(self.mock_root)
        handlers_meta = extractor.extract_handler_metadata()
        self.assertIn("compose-post-service", handlers_meta)

        cp_meta = handlers_meta["compose-post-service"]
        self.assertIn("ComposePost", cp_meta["methods"])
        method_data = cp_meta["methods"]["ComposePost"]

        self.assertEqual(method_data["server_span"], "compose_post_server")
        phases = method_data["phases"]
        self.assertIn("P1", phases)
        self.assertIn("barrier", phases)
        self.assertIn("P2", phases)

        # Verify P1 concurrent dispatches
        p1 = phases["P1"]
        self.assertEqual(p1["type"], "concurrent")
        p1_services = {d["service"] for d in p1["dispatches"]}
        self.assertIn("text-service", p1_services)
        self.assertIn("user-service", p1_services)

        # Verify join barrier
        barrier = phases["barrier"]
        self.assertEqual(barrier["name"], "compose_post_barrier")
        self.assertEqual(barrier["type"], "join_barrier")
        self.assertIn("creator_future", barrier["waits_on"])
        self.assertIn("text_future", barrier["waits_on"])

        # Verify P2 sequential/deferred dispatches
        p2 = phases["P2"]
        self.assertEqual(p2["type"], "sequential")
        p2_services = {d["service"] for d in p2["dispatches"]}
        self.assertIn("post-storage-service", p2_services)
        self.assertIn("user-timeline-service", p2_services)

    def test_text_handler_nested_parallel_dispatches(self):
        extractor = CppHandlerGrepExtractor(self.mock_root)
        nested = extractor.extract_nested_dispatches("text-service", "ComposeText")
        self.assertEqual(len(nested), 2)
        nested_services = {d["service"] for d in nested}
        self.assertIn("url-shorten-service", nested_services)
        self.assertIn("user-mention-service", nested_services)

        nested_map = {d["service"]: d for d in nested}
        self.assertEqual(nested_map["url-shorten-service"]["channel"], "ComposeUrls")
        self.assertEqual(nested_map["url-shorten-service"]["client_span"], "compose_urls_client")
        self.assertEqual(nested_map["user-mention-service"]["channel"], "ComposeUserMentions")
        self.assertEqual(nested_map["user-mention-service"]["client_span"], "compose_user_mentions_client")

    def test_end_to_end_enrichment(self):
        enricher = TopologyEnricher(
            idl_path="interfaces/idl-contracts.json",
            dsb_root=str(self.mock_root)
        )
        oracle = enricher.enrich()

        self.assertEqual(oracle["_meta"]["name"], "Social Network Topology Oracle")
        self.assertEqual(oracle["_meta"]["version"], "1.0.0")
        self.assertTrue(oracle["_meta"]["zero_optional_verified"])
        self.assertEqual(oracle["_meta"]["dsb_source"], str(self.mock_root))

        self.assertIn("compose_post_workflow", oracle["workflows"])
        cp_wf = oracle["workflows"]["compose_post_workflow"]
        self.assertEqual(cp_wf["entry_service"], "compose-post-service")
        self.assertEqual(cp_wf["entry_channel"], "ComposePost")

        text_dispatch = [
            d for d in cp_wf["phases"]["P1"]["dispatches"]
            if d["service"] == "text-service"
        ][0]
        self.assertIn("nested_dispatches", text_dispatch)
        self.assertEqual(len(text_dispatch["nested_dispatches"]), 2)


class TestGenericServiceInference(unittest.TestCase):
    """Test generic service inference and dynamic C++ type extraction without hardcoded maps."""

    def test_infer_from_idl_method_mapping(self):
        idl_mock = {
            "services": {
                "custom-order-service": {
                    "channels": [
                        {"name": "CreateOrder", "pattern": "IP-4", "return_type": "string"},
                        {"name": "CancelOrder", "pattern": "IP-1", "return_type": "void"}
                    ]
                },
                "payment-gateway-service": {
                    "channels": [
                        {"name": "ProcessPayment", "pattern": "IP-4", "return_type": "bool"}
                    ]
                }
            }
        }
        with tempfile.TemporaryDirectory() as tmpdir:
            tmp_root = Path(tmpdir).resolve()
            (tmp_root / "src").mkdir()
            extractor = CppHandlerGrepExtractor(tmp_root, idl_data=idl_mock)
            
            # Primary lookup: IDL method mapping resolves without needing known variable names
            self.assertEqual(extractor._infer_service_from_client_var("random_client_var", "CreateOrder"), "custom-order-service")
            self.assertEqual(extractor._infer_service_from_client_var("p_client", "ProcessPayment"), "payment-gateway-service")

    def test_extract_type_mappings_from_cpp(self):
        cpp_snippet = '''
        ClientPool<ThriftClient<InventoryServiceClient>> *_inventory_client_pool;
        ClientPool<social_network::ThriftClient<ShippingServiceClient>> *_shipping_pool;
        ClientPool<ThriftClient<NotificationService>> *_notify_client_pool;
        '''
        with tempfile.TemporaryDirectory() as tmpdir:
            tmp_root = Path(tmpdir).resolve()
            (tmp_root / "src").mkdir()
            extractor = CppHandlerGrepExtractor(tmp_root, idl_data={})
            type_map = extractor._extract_type_mappings(cpp_snippet)
            
            self.assertEqual(type_map.get("inventory"), "inventory-service")
            self.assertEqual(type_map.get("shipping"), "shipping-service")
            self.assertEqual(type_map.get("notify"), "notification-service")

    def test_variable_normalization_and_fallback(self):
        idl_mock = {
            "services": {
                "account-management-service": {"channels": []},
                "audit-log-service": {"channels": []}
            }
        }
        with tempfile.TemporaryDirectory() as tmpdir:
            tmp_root = Path(tmpdir).resolve()
            (tmp_root / "src").mkdir()
            extractor = CppHandlerGrepExtractor(tmp_root, idl_data=idl_mock)
            
            # 1. Exact match with -service
            self.assertEqual(extractor._infer_service_from_client_var("account_management_client", ""), "account-management-service")
            # 2. Token prefix match
            self.assertEqual(extractor._infer_service_from_client_var("audit_client", ""), "audit-log-service")
            # 3. Generic fallback
            self.assertEqual(extractor._infer_service_from_client_var("unregistered_component_client", ""), "unregistered-component-service")


if __name__ == "__main__":
    unittest.main()
