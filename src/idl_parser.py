#!/usr/bin/env python3
"""
Thrift IDL Parser and Contract Oracle Generator.

Extracts service declarations, RPC methods, and interaction channels from Thrift IDL.
Classifies exchange patterns (IP-1 for void, IP-4 for non-void).
Enforces the Zero Optional Fields Invariant (ZOF = 0).
Outputs canonical contract oracle JSON.
"""

import argparse
import json
import os
import re
from typing import Any, Dict, List, Optional, Tuple


class InvariantViolationError(Exception):
    """Raised when an IDL invariant (such as Zero Optional Fields) is violated."""
    pass


def strip_comments(thrift_text: str) -> str:
    """Strip single-line and multi-line comments from Thrift IDL."""
    # Strip multi-line comments /* ... */
    no_multiline = re.sub(r'/\*.*?\*/', '', thrift_text, flags=re.DOTALL)
    # Strip single-line comments // ... and # ...
    no_singleline = re.sub(r'(//|#).*$', '', no_multiline, flags=re.MULTILINE)
    return no_singleline


def pascal_or_camel_to_kebab(name: str) -> str:
    """Convert PascalCase or camelCase string to kebab-case."""
    # Insert hyphen before capital letters following lowercase letters/digits
    s1 = re.sub(r'(.)([A-Z][a-z]+)', r'\1-\2', name)
    # Insert hyphen before capital letters preceded by lowercase
    s2 = re.sub(r'([a-z0-9])([A-Z])', r'\1-\2', s1)
    return s2.lower().strip('-')


class ThriftParser:
    """Parser for Thrift IDL focusing on structs, exceptions, services, and invariant checks."""

    def __init__(self, thrift_content: str, idl_filename: str = "contract.thrift"):
        self.raw_content = thrift_content
        self.idl_filename = idl_filename
        self.cleaned_content = strip_comments(thrift_content)
        self.structs: Dict[str, List[Dict[str, Any]]] = {}
        self.exceptions: Dict[str, List[Dict[str, Any]]] = {}
        self.services: Dict[str, List[Dict[str, Any]]] = {}
        self.zero_optional_verified = False

    def parse(self) -> Dict[str, Any]:
        """Parse IDL content, enforce invariants, and generate the contract dictionary."""
        self._parse_structs_and_exceptions()
        self._parse_services()
        self._enforce_zero_optional_invariant()
        return self._build_contract_dict()

    def _parse_structs_and_exceptions(self) -> None:
        """Extract struct and exception definitions and their field declarations."""
        # Regex for struct and exception blocks:
        # struct/exception <Name> { <fields> }
        pattern = re.compile(r'\b(struct|exception)\s+([A-Za-z0-9_]+)\s*\{([^}]*)\}', re.DOTALL)
        for match in pattern.finditer(self.cleaned_content):
            kind, name, body = match.groups()
            fields = self._parse_fields(body.strip(), container_name=f"{kind} {name}")
            if kind == "struct":
                self.structs[name] = fields
            else:
                self.exceptions[name] = fields

    def _parse_fields(self, body: str, container_name: str) -> List[Dict[str, Any]]:
        """Parse individual field lines inside a struct, exception, or parameter list."""
        fields = []
        if not body.strip():
            return fields

        # Individual field statements separated by semicolons, commas, or newlines
        raw_fields = [f.strip() for f in re.split(r'[;\n]+', body) if f.strip()]
        for raw in raw_fields:
            # Field format: <id>: [required|optional] <type> <name> [= <default>]
            field_match = re.match(
                r'^(\d+)\s*:\s*(?:(required|optional)\s+)?([\w<>,\s]+?)\s+([A-Za-z0-9_]+)(?:\s*=.*)?$',
                raw
            )
            if field_match:
                f_id, modifier, f_type, f_name = field_match.groups()
                # Check for explicit 'optional' keyword in raw line as safety
                is_optional = (modifier == "optional") or bool(re.search(r'\boptional\b', raw))
                fields.append({
                    "id": int(f_id),
                    "name": f_name,
                    "type": re.sub(r'\s+', ' ', f_type.strip()),
                    "optional": is_optional,
                    "raw": raw,
                    "container": container_name
                })
            else:
                # Catch fields that might use optional without field id or alternative formatting
                if re.search(r'\boptional\b', raw):
                    fields.append({
                        "id": None,
                        "name": raw,
                        "type": "unknown",
                        "optional": True,
                        "raw": raw,
                        "container": container_name
                    })
        return fields

    def _parse_services(self) -> None:
        """Extract service definitions and their RPC method signatures."""
        service_pattern = re.compile(
            r'\bservice\s+([A-Za-z0-9_]+)(?:\s+extends\s+[A-Za-z0-9_]+)?\s*\{([^}]*)\}',
            re.DOTALL
        )

        for match in service_pattern.finditer(self.cleaned_content):
            service_name, body = match.groups()
            methods = self._parse_service_methods(body.strip(), service_name)
            self.services[service_name] = methods

    def _parse_service_methods(self, body: str, service_name: str) -> List[Dict[str, Any]]:
        """Parse method declarations within a service block."""
        methods = []
        if not body.strip():
            return methods

        # Regex for method:
        # <return_type> <method_name> ( <args> ) [throws ( <exceptions> )]
        method_pattern = re.compile(
            r'([\w<>,\s]+?)\s+([A-Za-z0-9_]+)\s*\(([^)]*)\)(?:\s*throws\s*\(([^)]*)\))?',
            re.DOTALL
        )

        for m in method_pattern.finditer(body):
            ret_type_raw, method_name, args_raw, throws_raw = m.groups()
            ret_type = re.sub(r'\s+', ' ', ret_type_raw.strip())
            
            # Clean and normalize return type
            # Void vs non-void pattern
            pattern = "IP-1" if ret_type == "void" else "IP-4"

            # Parse arguments to verify zero-optional invariant on arguments
            arg_fields = self._parse_fields(
                args_raw.strip(),
                container_name=f"service {service_name} method {method_name} args"
            )

            # Parse throws clause if present
            throws_fields = []
            if throws_raw:
                throws_fields = self._parse_fields(
                    throws_raw.strip(),
                    container_name=f"service {service_name} method {method_name} throws"
                )

            methods.append({
                "name": method_name,
                "return_type": ret_type,
                "pattern": pattern,
                "arguments": arg_fields,
                "throws": throws_fields
            })

        return methods

    def _enforce_zero_optional_invariant(self) -> None:
        """
        Enforce Zero Optional Fields Invariant ($ZOF = 0$).
        Asserts that 0 fields in structs, exceptions, or method signatures are marked 'optional'.
        """
        violations = []

        # Check structs
        for s_name, fields in self.structs.items():
            for f in fields:
                if f.get("optional"):
                    violations.append(f"Struct '{s_name}' field '{f['name']}' is marked optional.")

        # Check exceptions
        for e_name, fields in self.exceptions.items():
            for f in fields:
                if f.get("optional"):
                    violations.append(f"Exception '{e_name}' field '{f['name']}' is marked optional.")

        # Check service method args and throws
        for s_name, methods in self.services.items():
            for m in methods:
                for arg in m["arguments"]:
                    if arg.get("optional"):
                        violations.append(
                            f"Service '{s_name}' method '{m['name']}' argument '{arg['name']}' is marked optional."
                        )
                for throw_f in m["throws"]:
                    if throw_f.get("optional"):
                        violations.append(
                            f"Service '{s_name}' method '{m['name']}' throws field '{throw_f['name']}' is marked optional."
                        )

        # Fallback check across entire raw content for any unparsed 'optional' keyword
        optional_matches = re.findall(r'\boptional\b', self.cleaned_content)
        if optional_matches and not violations:
            violations.append(f"Found {len(optional_matches)} occurrences of 'optional' keyword in IDL.")

        if violations:
            error_msg = (
                f"Zero Optional Fields Invariant violated in {self.idl_filename}!\n"
                + "\n".join(f" - {v}" for v in violations)
            )
            raise InvariantViolationError(error_msg)

        self.zero_optional_verified = True

    def _build_contract_dict(self) -> Dict[str, Any]:
        """Construct canonical contract oracle dictionary matching the intermediate schema."""
        services_dict: Dict[str, Dict[str, Any]] = {}

        for s_name, methods in self.services.items():
            kebab_service_name = pascal_or_camel_to_kebab(s_name)
            channels = [
                {
                    "name": m["name"],
                    "pattern": m["pattern"],
                    "return_type": m["return_type"]
                }
                for m in methods
            ]
            services_dict[kebab_service_name] = {
                "channels": channels
            }

        return {
            "_meta": {
                "idl_file": os.path.basename(self.idl_filename),
                "zero_optional_verified": self.zero_optional_verified
            },
            "services": services_dict
        }


def parse_thrift_file(idl_path: str, output_path: Optional[str] = None) -> Dict[str, Any]:
    """Parse Thrift IDL file, assert invariants, and optionally save JSON output."""
    if not os.path.exists(idl_path):
        raise FileNotFoundError(f"IDL file not found: {idl_path}")

    with open(idl_path, "r", encoding="utf-8") as f:
        content = f.read()

    parser = ThriftParser(content, idl_filename=idl_path)
    contracts = parser.parse()

    if output_path:
        out_dir = os.path.dirname(output_path)
        if out_dir:
            os.makedirs(out_dir, exist_ok=True)
        with open(output_path, "w", encoding="utf-8") as f:
            json.dump(contracts, f, indent=2)
            f.write("\n")

    return contracts


def main():
    parser = argparse.ArgumentParser(
        description="Parse Thrift IDL to establish baseline cross-service API contracts and oracle."
    )
    parser.add_argument(
        "--idl",
        default="IDL/social_network.thrift",
        help="Path to input Thrift IDL file (default: IDL/social_network.thrift)"
    )
    parser.add_argument(
        "--output",
        default="interfaces/idl-contracts.json",
        help="Path to output contracts JSON (default: interfaces/idl-contracts.json)"
    )

    args = parser.parse_args()

    try:
        contracts = parse_thrift_file(args.idl, args.output)
        print(f"Successfully parsed {args.idl}")
        print(f"Verified Zero Optional Fields Invariant: {contracts['_meta']['zero_optional_verified']}")
        print(f"Extracted {len(contracts['services'])} services to {args.output}")
    except InvariantViolationError as e:
        print(f"ERROR: {e}")
        exit(1)
    except Exception as e:
        print(f"ERROR: Failed to process IDL: {e}")
        exit(1)


if __name__ == "__main__":
    main()
