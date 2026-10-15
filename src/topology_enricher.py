#!/usr/bin/env python3
"""
Topology Enricher for Microservice Composition.

Ingests baseline IDL contracts (interfaces/idl-contracts.json) and statically greps
DeathStarBench C++ service handlers and Nginx/wrk2 Lua scripts to extract:
  1. Front-Door HTTP REST Ingress endpoints and parameter bindings.
  2. Concurrency Phase Disambiguation (P1 concurrent vs P2 deferred/sequential).
  3. Synchronization join barriers (e.g., post_assemble_barrier).
  4. Nested multi-tier parallel execution graphs (e.g., TextService fan-out).
  5. Jaeger/OpenTracing client and server span label grounding.

Outputs the complete topology oracle to interfaces/social-network.json.
"""

import argparse
import json
import os
import re
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple


# ============================================================================
# Domain Data Structures
# ============================================================================

@dataclass
class IngressEndpoint:
    """Represents an external front-door HTTP REST ingress route."""
    endpoint: str
    method: str
    entry_service: str
    entry_channel: str
    span_client: str
    workflow: str
    payload_fields: List[str] = field(default_factory=list)


@dataclass
class DispatchCall:
    """Represents a downstream microservice RPC dispatch within a workflow."""
    service: str
    channel: str
    client_span: str
    launch_type: str = "direct"  # "async", "deferred", "direct"
    server_span: Optional[str] = None
    nested_dispatches: List[Dict[str, Any]] = field(default_factory=list)


@dataclass
class JoinBarrier:
    """Represents a synchronization barrier waiting on outstanding async futures."""
    name: str
    type: str = "join_barrier"
    waits_on: List[str] = field(default_factory=list)


@dataclass
class ConcurrencyPhase:
    """Represents an execution concurrency phase (P1 or P2)."""
    phase_id: str
    type: str  # "concurrent" or "sequential"
    dispatches: List[DispatchCall] = field(default_factory=list)


@dataclass
class WorkflowDefinition:
    """Represents a composite multi-phase microservice execution workflow."""
    name: str
    entry_service: str
    entry_channel: str
    server_span: str
    client_span: str
    phases: Dict[str, Any] = field(default_factory=dict)


# ============================================================================
# Helpers & String Utilities
# ============================================================================

def pascal_to_kebab(name: str) -> str:
    """Convert PascalCase or camelCase to kebab-case (e.g. ComposePostService -> compose-post-service)."""
    s1 = re.sub(r'(.)([A-Z][a-z]+)', r'\1-\2', name)
    s2 = re.sub(r'([a-z0-9])([A-Z])', r'\1-\2', s1)
    return s2.lower().strip('-')


def strip_cpp_comments(content: str) -> str:
    """Strip C/C++ style comments from source code."""
    no_multiline = re.sub(r'/\*.*?\*/', '', content, flags=re.DOTALL)
    no_singleline = re.sub(r'//.*$', '', no_multiline, flags=re.MULTILINE)
    return no_singleline


def strip_lua_comments(content: str) -> str:
    """Strip Lua style comments from source code."""
    no_multiline = re.sub(r'--\[\[.*?\]\]', '', content, flags=re.DOTALL)
    no_singleline = re.sub(r'--.*$', '', no_multiline, flags=re.MULTILINE)
    return no_singleline


# ============================================================================
# IDL Contract Ingestion
# ============================================================================

class IDLContractIngester:
    """Loads and validates baseline idl-contracts.json."""

    @staticmethod
    def load(idl_path: str) -> Dict[str, Any]:
        path = Path(idl_path)
        if not path.exists():
            raise FileNotFoundError(f"IDL contract file not found at: {idl_path}")
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
        if "services" not in data:
            raise ValueError(f"Invalid IDL contract JSON: missing 'services' key in {idl_path}")
        return data


# ============================================================================
# DeathStarBench Path Resolver
# ============================================================================

class DSBRootResolver:
    """Resolves and validates target microservice source root directory."""

    SEARCH_PATHS = [
        "../DeathStarBench/socialNetwork",
        "../../DeathStarBench/socialNetwork",
        "../socialNetwork",
        "../app",
        "../service",
        "../microservices",
    ]

    @classmethod
    def resolve(cls, specified_path: Optional[str] = None) -> Path:
        if specified_path:
            p = Path(specified_path).resolve()
            if p.exists() and (p / "src").exists():
                return p
            raise FileNotFoundError(f"Specified microservice root is invalid or missing src/ folder: {specified_path}")

        # Check environment variables
        env_path = (
            os.environ.get("BENCHMARK_ROOT")
            or os.environ.get("APP_ROOT")
            or os.environ.get("DSB_ROOT")
            or os.environ.get("DEATHSTARBENCH_ROOT")
        )
        if env_path:
            p = Path(env_path).resolve()
            if p.exists() and (p / "src").exists():
                return p

        # Check relative search paths
        for candidate in cls.SEARCH_PATHS:
            p = Path(candidate).resolve()
            if p.exists() and (p / "src").exists():
                return p

        raise FileNotFoundError(
            "Could not locate microservice root directory. Please provide --dsb-root/--app-root <path> or set $APP_ROOT / $DSB_ROOT."
        )


# ============================================================================
# Lua & Nginx Ingress Grep Extractor
# ============================================================================

class LuaIngressGrepExtractor:
    """Grep scanner for Nginx configuration and Lua API endpoints."""

    def __init__(self, dsb_root: Path):
        self.dsb_root = dsb_root
        self.nginx_conf_path = dsb_root / "nginx-web-server" / "conf" / "nginx.conf"
        self.lua_dir = dsb_root / "nginx-web-server" / "lua-scripts"
        
        # Dynamically locate wrk2 scripts directory if present
        wrk2_base = dsb_root / "wrk2" / "scripts"
        self.wrk2_dir = wrk2_base
        if wrk2_base.exists():
            for sub in wrk2_base.iterdir():
                if sub.is_dir() and not sub.name.startswith("."):
                    self.wrk2_dir = sub
                    break

    def extract_ingress(self) -> List[IngressEndpoint]:
        endpoints: List[IngressEndpoint] = []
        
        # 1. Parse nginx.conf location directives and require targets
        nginx_routes: Dict[str, Dict[str, Any]] = {}
        if self.nginx_conf_path.exists():
            with open(self.nginx_conf_path, "r", encoding="utf-8") as f:
                conf_text = f.read()
            
            # Match location /wrk2-api/... or /api/... blocks
            loc_matches = re.finditer(
                r'location\s+([/\w\-]+)\s*\{([^}]+content_by_lua[^{]*[\'"{]([^\'"\}]+)[\'"}][^}]*)\}',
                conf_text,
                re.DOTALL
            )
            for m in loc_matches:
                loc_path = m.group(1).strip()
                block_content = m.group(2)
                lua_content = m.group(3)
                
                methods = ["POST", "GET"]
                method_match = re.findall(r'\$request_method\s*=\s*[\'"](POST|GET)[\'"]', block_content)
                if method_match:
                    methods = list(set(method_match))
                
                req_match = re.search(r'require\s+[\'"]([^\'"]+)[\'"]', lua_content)
                call_match = re.search(r'client\.([A-Za-z0-9_]+)\(', lua_content)
                
                if req_match:
                    req_target = req_match.group(1)
                    nginx_routes[loc_path] = {
                        "script": req_target,
                        "method_call": call_match.group(1) if call_match else None,
                        "methods": methods
                    }

        # 2. Grep wrk2-api Lua scripts
        lua_files = list(self.lua_dir.glob("wrk2-api/**/*.lua"))
        if not lua_files:
            lua_files = list(self.lua_dir.glob("**/*.lua"))

        for lua_file in sorted(lua_files):
            rel_path = lua_file.relative_to(self.lua_dir)
            rel_str = str(rel_path).replace("\\", "/").replace(".lua", "")
            
            with open(lua_file, "r", encoding="utf-8") as f:
                content = strip_lua_comments(f.read())
            
            # Grep connection service target
            conn_match = re.search(r'connection\s*\(\s*([A-Za-z0-9_]+),\s*["\']([A-Za-z0-9_\-]+)["\']', content)
            service_name = conn_match.group(2) if conn_match else None
            
            # If not found directly, infer from required Thrift module (e.g. social_network_UserService or UserService)
            if not service_name:
                mod_match = re.search(r'require\s+["\'](?:[A-Za-z0-9_]+_)?([A-Za-z0-9_]+Service)["\']', content)
                if mod_match:
                    service_name = pascal_to_kebab(mod_match.group(1))
            
            # Grep start_span
            span_match = re.search(r'start_span\s*\(\s*["\']([A-Za-z0-9_\-]+)["\']', content)
            span_client = span_match.group(1) if span_match else ""
            
            # Grep client RPC calls (ignore .iprot and standard methods)
            raw_rpc_calls = re.findall(r'client\.([A-Z][A-Za-z0-9_]+)', content)
            rpc_matches = [c for c in raw_rpc_calls if c not in ("GetClient", "iprot")]
            rpc_channel = rpc_matches[0] if rpc_matches else ""
            
            # If still not found, check pcall(client.Method, ...)
            if not rpc_channel:
                pcall_match = re.search(r'pcall\s*\(\s*client\.([A-Za-z0-9_]+)', content)
                if pcall_match and pcall_match.group(1) != "iprot":
                    rpc_channel = pcall_match.group(1)

            http_method = "POST"
            if "get_post_args" in content or "read_body" in content:
                http_method = "POST"
            elif "get_uri_args" in content:
                http_method = "GET"
            
            payload_fields = re.findall(r'(?:post|uri_args)\.([a-zA-Z0-9_]+)', content)
            payload_fields = sorted(list(set(payload_fields)))
            
            endpoint_path = f"/{rel_str}"
            if not endpoint_path.startswith("/wrk2-api") and not endpoint_path.startswith("/api"):
                endpoint_path = f"/wrk2-api/{rel_str}"
            
            for loc, info in nginx_routes.items():
                if info["script"] == rel_str:
                    endpoint_path = loc
                    if info.get("methods"):
                        http_method = info["methods"][0]
                    break
            
            if service_name and rpc_channel:
                workflow_name = f"{pascal_to_kebab(rpc_channel).replace('-', '_')}_workflow"
                endpoints.append(IngressEndpoint(
                    endpoint=endpoint_path,
                    method=http_method,
                    entry_service=service_name,
                    entry_channel=rpc_channel,
                    span_client=span_client,
                    workflow=workflow_name,
                    payload_fields=payload_fields
                ))

        self._enrich_payloads_from_wrk2(endpoints)
        return endpoints

    def _enrich_payloads_from_wrk2(self, endpoints: List[IngressEndpoint]) -> None:
        if not self.wrk2_dir.exists():
            return
        for ep in endpoints:
            wrk_script = self.wrk2_dir / f"{ep.entry_service.replace('-service', '')}.lua"
            if not wrk_script.exists():
                wrk_script = self.wrk2_dir / f"{pascal_to_kebab(ep.entry_channel)}.lua"
            if wrk_script.exists():
                with open(wrk_script, "r", encoding="utf-8") as f:
                    txt = f.read()
                fields = re.findall(r'([a-zA-Z0-9_]+)=["\']?\s*\.\.', txt)
                if fields:
                    combined = set(ep.payload_fields) | set(fields)
                    ep.payload_fields = sorted(list(combined))


# ============================================================================
# C++ Handler Grep Extractor
# ============================================================================

class CppHandlerGrepExtractor:
    """Grep scanner for DeathStarBench C++ service handlers."""

    def __init__(self, dsb_root: Path, idl_data: Optional[Dict[str, Any]] = None):
        self.dsb_root = dsb_root
        self.src_dir = dsb_root / "src"
        if idl_data is None:
            default_idl = Path("interfaces/idl-contracts.json")
            if default_idl.exists():
                try:
                    self.idl_data = IDLContractIngester.load(str(default_idl))
                except Exception:
                    self.idl_data = {}
            else:
                self.idl_data = {}
        else:
            self.idl_data = idl_data

        self.idl_method_to_service: Dict[str, str] = {}
        self.known_services: Set[str] = set()
        self.var_to_service: Dict[str, str] = {}
        self._init_idl_mappings()
        self._discover_services_and_types()

    def _init_idl_mappings(self) -> None:
        """Derive method-to-service mapping and known canonical service names from IDL contracts."""
        services = self.idl_data.get("services", {})
        for s_name, s_data in services.items():
            self.known_services.add(s_name)
            for ch in s_data.get("channels", []):
                ch_name = ch.get("name")
                if ch_name:
                    self.idl_method_to_service[ch_name] = s_name

    def _discover_services_and_types(self) -> None:
        """Discover service directories and scan C++ headers for ThriftClient types."""
        if not self.src_dir.exists():
            return
        for p in self.src_dir.iterdir():
            if p.is_dir() and not p.name.startswith("."):
                self.known_services.add(pascal_to_kebab(p.name))

        for hf in self.src_dir.glob("*/*Handler.h"):
            try:
                with open(hf, "r", encoding="utf-8") as f:
                    content = strip_cpp_comments(f.read())
                type_map = self._extract_type_mappings(content)
                self.var_to_service.update(type_map)
            except Exception:
                continue

    def _extract_type_mappings(self, content: str) -> Dict[str, str]:
        """Extract member variable type definitions from C++ handler to dynamically map variable names to services."""
        var_map: Dict[str, str] = {}
        
        # 1. Match ClientPool<ThriftClient<FooServiceClient>> *_foo_client_pool or ClientPool<social_network::ThriftClient<FooServiceClient>>
        client_pool_pattern = re.compile(
            r'ClientPool\s*<\s*(?:[A-Za-z0-9_]+::)?ThriftClient\s*<\s*([A-Za-z0-9_]+)\s*>\s*>\s*\*?\s*([A-Za-z0-9_]+)',
            re.DOTALL
        )
        for m in client_pool_pattern.finditer(content):
            raw_type, var_name = m.groups()
            clean_type = re.sub(r'(?:Service)?Client$', 'Service', raw_type)
            if not clean_type.endswith("Service"):
                clean_type = f"{clean_type}Service"
            service_id = pascal_to_kebab(clean_type)
            clean = var_name.replace("_client_wrapper", "").replace("_client", "").replace("_pool", "").strip("_")
            var_map[clean] = service_id
            var_map[var_name] = service_id
            var_map[var_name.lstrip("_")] = service_id

        # 2. Match direct client declarations: FooServiceClient *_foo_client; or std::shared_ptr<FooServiceClient> _foo_client;
        direct_client_pattern = re.compile(
            r'(?:std::shared_ptr<\s*)?([A-Za-z0-9_]+(?:Service|ServiceClient))\s*>?\s*\*?\s*([A-Za-z0-9_]+_client(?:_wrapper)?)',
            re.DOTALL
        )
        for m in direct_client_pattern.finditer(content):
            raw_type, var_name = m.groups()
            clean_type = re.sub(r'(?:Service)?Client$', 'Service', raw_type)
            if not clean_type.endswith("Service"):
                clean_type = f"{clean_type}Service"
            service_id = pascal_to_kebab(clean_type)
            clean = var_name.replace("_client_wrapper", "").replace("_client", "").replace("_pool", "").strip("_")
            var_map[clean] = service_id
            var_map[var_name] = service_id
            var_map[var_name.lstrip("_")] = service_id

        return var_map

    def extract_handler_metadata(self) -> Dict[str, Dict[str, Any]]:
        """Grep all service handlers (*Handler.h) and return structured metadata."""
        handlers_meta: Dict[str, Dict[str, Any]] = {}
        handler_files = list(self.src_dir.glob("*/*Handler.h"))

        for hf in sorted(handler_files):
            service_folder = hf.parent.name
            service_id = pascal_to_kebab(service_folder)
            
            with open(hf, "r", encoding="utf-8") as f:
                content = strip_cpp_comments(f.read())
            
            local_type_map = self._extract_type_mappings(content)
            span_matches = re.findall(r'StartSpan\(\s*["\']([A-Za-z0-9_\-]+)["\']', content)
            helpers = self._grep_helper_methods(content, local_type_map)
            methods = self._grep_methods(content, service_id, helpers, local_type_map)
            
            handlers_meta[service_id] = {
                "file": str(hf.relative_to(self.dsb_root)),
                "spans": span_matches,
                "helpers": helpers,
                "methods": methods
            }

        return handlers_meta

    def _grep_helper_methods(self, content: str, local_type_map: Optional[Dict[str, str]] = None) -> Dict[str, Dict[str, Any]]:
        """Extract helper methods (e.g. _ComposeCreaterHelper) with their target RPC and client span."""
        helpers: Dict[str, Dict[str, Any]] = {}
        
        helper_defs = re.finditer(
            r'(?:void|[A-Za-z0-9_<>:]+)\s+(?:[A-Za-z0-9_]+Handler::)?(_?[A-Za-z0-9_]+Helper)\s*\(([^)]*)\)\s*\{',
            content
        )
        
        for m in helper_defs:
            helper_name = m.group(1)
            start_pos = m.end()
            body = self._extract_block(content, start_pos)
            
            # Grep client span inside helper
            span_match = re.search(r'StartSpan\(\s*["\']([A-Za-z0-9_\-]+)["\']', body)
            client_span = span_match.group(1) if span_match else ""
            
            # Grep target RPC calls (filtering out GetClient)
            raw_rpc_matches = re.findall(r'([A-Za-z0-9_]+_client(?:_wrapper)?(?:->GetClient\(\))?)->([A-Z][A-Za-z0-9_]+)\(', body)
            rpc_matches = [(v, c) for v, c in raw_rpc_matches if c != "GetClient"]
            
            target_service = ""
            target_channel = ""
            if rpc_matches:
                client_var, target_channel = rpc_matches[0]
                target_service = self._infer_service_from_client_var(client_var, target_channel, local_type_map)
            
            helpers[helper_name] = {
                "client_span": client_span,
                "target_service": target_service,
                "target_channel": target_channel,
                "body": body
            }

        return helpers

    def _grep_methods(
        self,
        content: str,
        service_id: str,
        helpers: Dict[str, Dict[str, Any]],
        local_type_map: Optional[Dict[str, str]] = None
    ) -> Dict[str, Dict[str, Any]]:
        """Extract main interface methods (e.g. ComposePost) and classify concurrency phases."""
        methods: Dict[str, Dict[str, Any]] = {}
        
        method_defs = re.finditer(
            r'\n\s*(?:void|[A-Za-z0-9_<>:]+)\s+(?:[A-Za-z0-9_]+Handler::)?([A-Z][A-Za-z0-9_]+)\s*\(([^)]*)\)\s*\{',
            content
        )
        
        for m in method_defs:
            method_name = m.group(1)
            if method_name in ("GetClient", "StartSpan"):
                continue
            start_pos = m.end()
            body = self._extract_block(content, start_pos)
            
            server_span_match = re.search(r'StartSpan\(\s*["\']([A-Za-z0-9_\-]+server)["\']', body)
            if not server_span_match:
                server_span_match = re.search(r'StartSpan\(\s*["\']([A-Za-z0-9_\-]+)["\']', body)
            server_span = server_span_match.group(1) if server_span_match else f"{pascal_to_kebab(method_name).replace('-', '_')}_server"
            
            phases = self._disambiguate_concurrency(body, helpers, service_id, method_name, local_type_map)
            
            methods[method_name] = {
                "server_span": server_span,
                "phases": phases,
                "body": body
            }

        return methods

    def _disambiguate_concurrency(
        self,
        body: str,
        helpers: Dict[str, Dict[str, Any]],
        service_id: str,
        method_name: str,
        local_type_map: Optional[Dict[str, str]] = None
    ) -> Dict[str, Any]:
        """Disambiguate P1 concurrent vs P2 sequential/deferred phases and barriers."""
        async_pattern = re.compile(
            r'(?:auto\s+)?([A-Za-z0-9_]+)\s*=\s*std::async\(\s*std::launch::([a-z]+)\s*,\s*(?:&[A-Za-z0-9_]+Handler::)?([A-Za-z0-9_]+|\(\)\s*\{|\[&\]\s*\(?\)?\s*\{)',
            re.DOTALL
        )
        
        get_pattern = re.compile(r'([A-Za-z0-9_]+)\.get\(\)')
        
        async_matches = list(async_pattern.finditer(body))
        get_matches = list(get_pattern.finditer(body))
        
        if not async_matches and not get_matches:
            direct_calls = self._extract_direct_calls(body, local_type_map)
            if direct_calls:
                return {
                    "P1": {
                        "type": "sequential",
                        "dispatches": [asdict(d) for d in direct_calls]
                    }
                }
            return {}

        p1_dispatches: List[DispatchCall] = []
        p2_dispatches: List[DispatchCall] = []
        barrier_joins: List[str] = []
        
        first_get_pos = get_matches[0].start() if get_matches else len(body)
        
        for am in async_matches:
            var_name = am.group(1)
            launch_type = am.group(2)  # "async" or "deferred"
            target_ref = am.group(3).strip()
            call_pos = am.start()
            
            dispatch = self._resolve_dispatch(target_ref, helpers, body, call_pos, launch_type, local_type_map)
            if not dispatch:
                continue

            if launch_type == "async" and call_pos < first_get_pos:
                p1_dispatches.append(dispatch)
            elif launch_type == "deferred" or call_pos > first_get_pos:
                p2_dispatches.append(dispatch)
            else:
                p1_dispatches.append(dispatch)

        for gm in get_matches:
            fut_name = gm.group(1)
            if fut_name in [am.group(1) for am in async_matches if am.group(2) == "async" and am.start() < first_get_pos]:
                barrier_joins.append(fut_name)

        phases_dict: Dict[str, Any] = {}
        if p1_dispatches:
            phases_dict["P1"] = {
                "type": "concurrent",
                "dispatches": [asdict(d) for d in p1_dispatches]
            }
        
        barrier_name = f"{pascal_to_kebab(method_name).replace('-', '_')}_barrier"
        if barrier_joins:
            phases_dict["barrier"] = asdict(JoinBarrier(
                name=barrier_name,
                type="join_barrier",
                waits_on=barrier_joins
            ))
            
        if p2_dispatches:
            phases_dict["P2"] = {
                "type": "sequential",
                "dispatches": [asdict(d) for d in p2_dispatches]
            }

        return phases_dict

    def _resolve_dispatch(
        self,
        target_ref: str,
        helpers: Dict[str, Dict[str, Any]],
        body: str,
        call_pos: int,
        launch_type: str,
        local_type_map: Optional[Dict[str, str]] = None
    ) -> Optional[DispatchCall]:
        """Resolve target service, channel, span, and nested calls from async target."""
        for helper_name, h_info in helpers.items():
            if helper_name in target_ref or target_ref.endswith(helper_name):
                return DispatchCall(
                    service=h_info["target_service"],
                    channel=h_info["target_channel"],
                    client_span=h_info["client_span"],
                    launch_type=launch_type,
                    server_span=f"{pascal_to_kebab(h_info['target_channel']).replace('-', '_')}_server"
                )

        brace_idx = body.find('{', call_pos)
        if brace_idx != -1:
            lambda_body = self._extract_block(body, brace_idx + 1)
            span_match = re.search(r'StartSpan\(\s*["\']([A-Za-z0-9_\-]+)["\']', lambda_body)
            
            raw_rpc_matches = re.findall(r'([A-Za-z0-9_]+_client(?:_wrapper)?(?:->GetClient\(\))?)->([A-Z][A-Za-z0-9_]+)\(', lambda_body)
            rpc_matches = [(v, c) for v, c in raw_rpc_matches if c != "GetClient"]
            if rpc_matches:
                client_var, target_channel = rpc_matches[0]
                target_service = self._infer_service_from_client_var(client_var, target_channel, local_type_map)
                client_span = span_match.group(1) if span_match else f"{pascal_to_kebab(target_channel).replace('-', '_')}_client"
                return DispatchCall(
                    service=target_service,
                    channel=target_channel,
                    client_span=client_span,
                    launch_type=launch_type,
                    server_span=f"{pascal_to_kebab(target_channel).replace('-', '_')}_server"
                )

        return None

    def _extract_direct_calls(self, body: str, local_type_map: Optional[Dict[str, str]] = None) -> List[DispatchCall]:
        """Extract synchronous direct client RPC calls from method body."""
        calls: List[DispatchCall] = []
        raw_rpc_matches = re.findall(r'([A-Za-z0-9_]+_client(?:_wrapper)?(?:->GetClient\(\))?)->([A-Z][A-Za-z0-9_]+)\(', body)
        rpc_matches = [(v, c) for v, c in raw_rpc_matches if c != "GetClient"]
        for client_var, channel in rpc_matches:
            service = self._infer_service_from_client_var(client_var, channel, local_type_map)
            calls.append(DispatchCall(
                service=service,
                channel=channel,
                client_span=f"{pascal_to_kebab(channel).replace('-', '_')}_client",
                launch_type="direct",
                server_span=f"{pascal_to_kebab(channel).replace('-', '_')}_server"
            ))
        return calls

    def extract_nested_dispatches(self, service_id: str, channel_name: str) -> List[Dict[str, Any]]:
        """Inspect service handlers (e.g. TextHandler::ComposeText) for nested parallel dispatches scoped to channel."""
        handler_file = self.src_dir / pascal_to_camel_dir(service_id) / f"{camel_case(service_id)}Handler.h"
        if not handler_file.exists():
            for h in self.src_dir.glob(f"*/*Handler.h"):
                if service_id.replace("-", "").lower() in h.name.lower():
                    handler_file = h
                    break
        
        if not handler_file.exists():
            return []

        with open(handler_file, "r", encoding="utf-8") as f:
            content = strip_cpp_comments(f.read())

        local_type_map = self._extract_type_mappings(content)

        # Find the specific method definition
        method_pattern = re.compile(
            r'\n\s*(?:void|[A-Za-z0-9_<>:]+)\s+(?:[A-Za-z0-9_]+Handler::)?' + re.escape(channel_name) + r'\s*\([^)]*\)\s*\{'
        )
        method_match = method_pattern.search(content)
        if not method_match:
            return []

        start_pos = method_match.end()
        method_body = self._extract_block(content, start_pos)

        nested: List[Dict[str, Any]] = []
        # Find all std::async calls inside this specific method body
        async_matches = re.finditer(
            r'std::async\(\s*std::launch::([a-z]+)\s*,\s*\[&\]\s*\(?\)?\s*\{',
            method_body
        )
        for m in async_matches:
            launch_type = m.group(1)
            start_block = m.end()
            block = self._extract_block(method_body, start_block)
            
            span_match = re.search(r'StartSpan\(\s*["\']([A-Za-z0-9_\-]+)["\']', block)
            
            raw_rpc_matches = re.findall(r'([A-Za-z0-9_]+_client(?:_wrapper)?(?:->GetClient\(\))?)->([A-Z][A-Za-z0-9_]+)\(', block)
            rpc_matches = [(v, c) for v, c in raw_rpc_matches if c != "GetClient"]
            if rpc_matches:
                client_var, target_channel = rpc_matches[0]
                target_service = self._infer_service_from_client_var(client_var, target_channel, local_type_map)
                client_span = span_match.group(1) if span_match else f"{pascal_to_kebab(target_channel).replace('-', '_')}_client"
                nested.append({
                    "service": target_service,
                    "channel": target_channel,
                    "client_span": client_span,
                    "launch_type": launch_type,
                    "server_span": f"{pascal_to_kebab(target_channel).replace('-', '_')}_server"
                })

        return nested

    @staticmethod
    def _extract_block(text: str, start_index: int) -> str:
        """Extract balanced curly braces block starting from start_index."""
        depth = 1
        pos = start_index
        while pos < len(text) and depth > 0:
            ch = text[pos]
            if ch == '{':
                depth += 1
            elif ch == '}':
                depth -= 1
            pos += 1
        return text[start_index:pos - 1]

    def _infer_service_from_client_var(
        self,
        client_var: str,
        method_name: str,
        local_var_map: Optional[Dict[str, str]] = None
    ) -> str:
        """Infer canonical microservice kebab-case ID dynamically from IDL, C++ types, or variable conventions."""
        # 1. Primary: IDL contract method-to-service lookup
        if method_name and method_name in self.idl_method_to_service:
            return self.idl_method_to_service[method_name]

        clean_var = client_var.replace("_client_wrapper", "").replace("_client", "").replace("_pool", "").strip("_")

        # 2. Secondary: Per-file local or global C++ type-extracted variable map
        if local_var_map and clean_var in local_var_map:
            return local_var_map[clean_var]
        if clean_var in self.var_to_service:
            return self.var_to_service[clean_var]

        # 3. Tertiary: Exact or prefix/token match against known services (from IDL or directory scan)
        candidate = clean_var.replace("_", "-")
        candidate_srv = candidate if candidate.endswith("-service") else f"{candidate}-service"
        if candidate_srv in self.known_services:
            return candidate_srv

        for srv in sorted(self.known_services):
            if srv.startswith(candidate) or candidate in srv:
                return srv

        # 4. Fallback: Generic kebab-case transformation
        return candidate_srv


def pascal_to_camel_dir(service_id: str) -> str:
    """Convert service id kebab-case to folder name (e.g. text-service -> TextService)."""
    parts = service_id.split("-")
    return "".join(p.capitalize() for p in parts)


def camel_case(service_id: str) -> str:
    parts = service_id.replace("-service", "").split("-")
    return "".join(p.capitalize() for p in parts)


# ============================================================================
# Topology Oracle Enrichment Engine
# ============================================================================

class TopologyEnricher:
    """Enrichment engine coordinating IDL contracts, Ingress routes, and C++ workflows."""

    def __init__(self, idl_path: str, dsb_root: Optional[str] = None):
        self.idl_path = idl_path
        self.dsb_root = DSBRootResolver.resolve(dsb_root)
        self.idl_data = IDLContractIngester.load(idl_path)
        self.ingress_extractor = LuaIngressGrepExtractor(self.dsb_root)
        self.cpp_extractor = CppHandlerGrepExtractor(self.dsb_root, idl_data=self.idl_data)

    def enrich(self) -> Dict[str, Any]:
        """Perform static grep enrichment and construct unified topology oracle."""
        # 1. Extract Ingress Endpoints
        ingress_endpoints = self.ingress_extractor.extract_ingress()
        
        # 2. Extract C++ Handlers Metadata
        handlers_meta = self.cpp_extractor.extract_handler_metadata()
        
        # 3. Enrich Baseline Services and Channels with Spans & Nested Dispatches
        services = self.idl_data.get("services", {})
        enriched_services: Dict[str, Any] = {}
        
        for service_name, s_data in services.items():
            channels = s_data.get("channels", [])
            enriched_channels = []
            h_info = handlers_meta.get(service_name, {})
            
            for ch in channels:
                ch_name = ch.get("name")
                pattern = ch.get("pattern")
                return_type = ch.get("return_type")
                
                # Ground Spans
                server_span = f"{pascal_to_kebab(ch_name).replace('-', '_')}_server"
                client_span = f"{pascal_to_kebab(ch_name).replace('-', '_')}_client"
                
                # Check discovered spans in handler
                if h_info and "spans" in h_info:
                    for sp in h_info["spans"]:
                        if sp.endswith("_server") and (pascal_to_kebab(ch_name).replace("-", "_") in sp or ch_name.lower() in sp.lower()):
                            server_span = sp
                        elif sp.endswith("_client") and (pascal_to_kebab(ch_name).replace("-", "_") in sp or ch_name.lower() in sp.lower()):
                            client_span = sp
                
                # Check for nested dispatches (e.g. TextService::ComposeText)
                nested = self.cpp_extractor.extract_nested_dispatches(service_name, ch_name)
                
                channel_obj: Dict[str, Any] = {
                    "name": ch_name,
                    "pattern": pattern,
                    "return_type": return_type,
                    "server_span": server_span,
                    "client_span": client_span
                }
                if nested:
                    channel_obj["nested_dispatches"] = nested
                
                enriched_channels.append(channel_obj)
            
            enriched_services[service_name] = {
                "channels": enriched_channels
            }

        # 4. Construct Workflows (Multi-phase runtime execution chains)
        workflows = self._build_workflows(ingress_endpoints, handlers_meta)

        # 5. Build Unified Topology Oracle Output
        idl_file_name = self.idl_data.get("_meta", {}).get("idl_file", "contract.thrift")
        app_title = Path(idl_file_name).stem.replace('_', ' ').replace('-', ' ').title()

        oracle: Dict[str, Any] = {
            "_meta": {
                "name": f"{app_title} Topology Oracle",
                "version": "1.0.0",
                "idl_file": idl_file_name,
                "zero_optional_verified": self.idl_data.get("_meta", {}).get("zero_optional_verified", True),
                "dsb_source": str(self.dsb_root)
            },
            "ingress": [asdict(ep) for ep in ingress_endpoints],
            "workflows": workflows,
            "services": enriched_services
        }

        return oracle

    def _build_workflows(
        self,
        ingress_endpoints: List[IngressEndpoint],
        handlers_meta: Dict[str, Dict[str, Any]]
    ) -> Dict[str, Any]:
        """Construct multi-phase workflow definitions for composite entry routes."""
        workflows: Dict[str, Any] = {}
        
        for ep in ingress_endpoints:
            wf_name = ep.workflow
            srv_meta = handlers_meta.get(ep.entry_service, {})
            method_info = srv_meta.get("methods", {}).get(ep.entry_channel, {})
            
            phases = method_info.get("phases", {})
            server_span = method_info.get("server_span", f"{pascal_to_kebab(ep.entry_channel).replace('-', '_')}_server")
            
            # Enrich nested calls in Phase 1 if present
            if "P1" in phases and "dispatches" in phases["P1"]:
                for d in phases["P1"]["dispatches"]:
                    nested = self.cpp_extractor.extract_nested_dispatches(d["service"], d["channel"])
                    if nested:
                        d["nested_dispatches"] = nested

            workflows[wf_name] = {
                "entry_service": ep.entry_service,
                "entry_channel": ep.entry_channel,
                "endpoint": ep.endpoint,
                "method": ep.method,
                "server_span": server_span,
                "client_span": ep.span_client,
                "phases": phases
            }

        return workflows


# ============================================================================
# CLI & Execution
# ============================================================================

def main() -> None:
    parser = argparse.ArgumentParser(
        description="Enrich IDL contracts with target microservice static grep analysis to generate topology oracle."
    )
    parser.add_argument(
        "--idl",
        type=str,
        default="interfaces/idl-contracts.json",
        help="Path to input IDL contracts JSON (default: interfaces/idl-contracts.json)"
    )
    parser.add_argument(
        "--app-root", "--dsb-root",
        dest="dsb_root",
        type=str,
        default=None,
        help="Path to target microservices/DeathStarBench root directory (or set $APP_ROOT / $DSB_ROOT)"
    )
    parser.add_argument(
        "--output",
        type=str,
        default="interfaces/social-network.json",
        help="Path to output topology oracle JSON (default: interfaces/social-network.json)"
    )

    args = parser.parse_args()

    enricher = TopologyEnricher(idl_path=args.idl, dsb_root=args.dsb_root)
    oracle_data = enricher.enrich()

    output_path = Path(args.output)
    output_path.parent.mkdir(parents=True, exist_ok=True)

    with open(output_path, "w", encoding="utf-8") as f:
        json.dump(oracle_data, f, indent=2)

    print(f"✓ Successfully generated topology oracle at: {output_path}")
    print(f"  Ingress endpoints: {len(oracle_data.get('ingress', []))}")
    print(f"  Workflows: {len(oracle_data.get('workflows', {}))}")
    print(f"  Enriched services: {len(oracle_data.get('services', {}))}")


if __name__ == "__main__":
    main()
