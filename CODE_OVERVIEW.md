# Artifact Code & File Structure Overview

This document provides a comprehensive, file-by-file description of every component included in the `wf-net-composition` artifact package accompanying the paper:
**"Interface-Guided Discovery, Repair, and Verification of Microservice Workflow Nets"**  
*Shubham and Meenakshi D'Souza (International Institute of Information Technology, Bangalore)*

---

## 1. Top-Level Files

| File | Type | Description |
| :--- | :--- | :--- |
| [`README.md`](README.md) | Markdown Document | Complete Artifact Evaluation and Reproducibility Guide containing setup instructions, pre-flight checks, 60-second demo execution, Rocq proof compilation & verification steps, full benchmark reproduction commands, LoLA model checking examples, and paper claim validation tables. |
| [`CODE_OVERVIEW.md`](CODE_OVERVIEW.md) | Markdown Document | This document: detailed architectural overview and component descriptions for all code, proofs, IDL contracts, interface specifications, tests, and telemetry data assets. |
| [`pipeline.py`](pipeline.py) | Python Script | Top-level CLI entry point for the artifact evaluation toolchain. Delegates directly to `src.pipeline.main()` for environment checks, demo sweeps, parametric benchmark generation, single-directory runs, and batch evaluations. |
| [`Makefile`](Makefile) | GNU Makefile | Top-level build and test automation interface supporting targets: `proofs`, `check`, `rebuild`, `check-env`, `demo`, `test`, `benchmark-drift`, `benchmark-partial`, and `clean`. |
| [`requirements.txt`](requirements.txt) | Dependency Spec | Python package requirements (`pm4py>=2.7.0`, `pandas>=1.3.0`, `graphviz>=0.20`). |
| [`.gitignore`](.gitignore) | Git Configuration | Excludes compiled Python bytecode (`__pycache__`), Rocq compiled objects (`*.vo`, `*.glob`, `*.aux`), OS metadata (`.DS_Store`), and transient repair run caches. |

---

## 2. Formal Rocq Proofs (`proofs/`)

Machine-checked formalization in the Rocq Prover (v9.2+) certifying all theoretical theorems, composition sound preservation, and negative control deadlocks:

| File | Format | Description |
| :--- | :--- | :--- |
| [`proofs/_CoqProject`](proofs/_CoqProject) | Configuration | Project mapping binding `-Q . MicroserviceComposition` and listing active source files. |
| [`proofs/composition.v`](proofs/composition.v) | Rocq Source (1,270 lines) | Complete formalization: Workflow Net soundness definitions, Interface Patterns IP-1 & IP-4, Theorem 1 (Repair Monotonicity & Soundness Restoration), Theorem 2 (Phased Composition Soundness Preservation: option to complete, proper completion, clean drainage, 1-boundedness, barrier liveness, dead-transition freedom), negative control silent $\tau$-skip deadlock, and DeathStarBench structural instantiation. |
| [`proofs/Makefile`](proofs/Makefile) | Generated Makefile | Build system for compiling `composition.v` into binary bytecode (`composition.vo`, `composition.glob`). |
| [`proofs/Makefile.local`](proofs/Makefile.local) | Makefile Extension | Hooks adding `make check` (invokes `rocq check` kernel verifier) and `make rebuild`. |
| [`proofs/Makefile.conf`](proofs/Makefile.conf) | Configuration | Rocq environment flags and build variables. |
| [`proofs/README.md`](proofs/README.md) | Markdown Guide | Documentation mapping paper theorems (Theorem 1, Theorem 2, Negative Control, Invariants) directly to Rocq lemmas and definitions. |

---

## 3. Core Python Discovery, Repair & Verification Modules (`src/`)

All discovery, repair, composition, and model checking algorithms are implemented under `src/`:

| Module | Primary Role & Description | Key Functions & Classes |
| :--- | :--- | :--- |
| `src/__init__.py` | Package Initializer | Marks `src` as a standard Python module namespace. |
| [`src/pipeline.py`](src/pipeline.py) | Unified Orchestrator | Orchestrates the 4-phase verification lifecycle: Pre-Flight Diagnostics, Phase 1 (Pre-Repair Mining & Failure Demo), Phase 2 (Distributed Proof-of-Call Relabeling & DROP-Repair), Phase 3 (Post-Repair Re-Mining & Re-Verification), Phase 4 (Transition Certificates & Cataloging), Batch Benchmark Harness, and Fast Demo Mode (<60s). | `main()`, `run_single_pipeline()`, `run_batch_pipeline()`, `run_demo_pipeline()`, `check_environment()`, `generate_parametric_benchmarks()` |
| [`src/miner.py`](src/miner.py) | Noise-Unfiltered Discovery | Discovers sound Generalized Workflow (GWF) Petri nets from normalized service event logs using Inductive Miner under a strict zero-noise threshold (`noise_threshold = 0.0`) to guarantee 100% variant retention. | `discover_service_net()`, `process_all_logs()`, `load_event_log()`, `infer_artifact_tag()` |
| [`src/detector.py`](src/detector.py) | Deductive Model Checking | Instruments candidate mandatory client send transitions with dynamic unconsumed observer places ($obs$) and evaluates unskippability via CTL reachability queries ($\mathbf{EF}(\text{sink} > 0 \land obs = 0)$) in LoLA and native pure-Python BFS state-space solver. | `instrument_observer_place()`, `run_batch_detection()`, `serialize_to_lola()`, `formulate_ctl_reachability_formula()`, `Verdict`, `AlphaMorphismStatus` |
| [`src/proof_of_call_relabeler.py`](src/proof_of_call_relabeler.py) | Proof-of-Call Relabeling | Detects drifted caller client span aliases and validates physical execution by cross-correlating with immutable callee server spans (`_server`) under the same distributed `case_id`, relabeling aliases in-place with 100% trace retention ($\rho_{\text{ret}} = 1.0$) and 0 synthetic events ($\Delta_{\text{synth}} = 0$). | `relabel_logs_directory()`, `relabel_service_file()`, `build_alias_to_canonical_map()`, `PROOF_OF_CALL_TARGETS` |
| [`src/contract_drop_repair.py`](src/contract_drop_repair.py) | Contract DROP-Repair | Cross-references service event logs against mandatory client sends ($A_i$) defined by IDL contracts and purges non-conformant gap traces with zero synthetic data fabrication ($\Delta_{\text{synth}} = 0$) to restore per-service $\alpha$-morphism refinement ($R_i^* \rightarrow_\alpha A_i$). | `drop_repair_logs_directory()`, `drop_repair_service_log()`, `DEFAULT_MANDATORY_CONTRACTS` |
| [`src/workflow_net_composer.py`](src/workflow_net_composer.py) | Phased Composition Engine | Fuses per-service GWF-nets across asynchronous interface channels ($P_{\text{chan}}$) using explicit join synchronization barriers ($t_{\mathcal{B}}$) to enforce phased execution ($P_1 \prec t_{\mathcal{B}} \prec P_2$), and model-checks 4 composition properties (deadlock freedom, orphaned message freedom, 1-boundedness, response-liveness). | `compose_workflow_nets()`, `verify_composition()`, `serialize_composed_to_lola()`, `serialize_composed_to_json()`, `serialize_composed_to_pnml()`, `render_composed_diagrams()` |
| [`src/verify_properties.py`](src/verify_properties.py) | Temporal Property Checker | Verifies 8 domain-specific temporal CTL properties on composed nets using LoLA and native BFS state-space exploration with counterexample firing sequence witness generation. | `verify_all_properties()`, `load_property_specs()`, `FormulaAST`, `StateSpaceExplorer`, `export_verification_report()` |
| [`src/generate_drift_logs.py`](src/generate_drift_logs.py) | Drift Benchmark Generator | Generates parametric label drift benchmark suites ($0.0\%$ to $20.0\%$ in $2.5\%$ steps) from baseline telemetry by hashing trace case IDs to inject operation aliases while preserving downstream server spans. | `generate_drift_logs()`, `apply_drift_to_row()`, `format_drift_tag()`, `infer_drift_tag()` |
| [`src/generate_partial_logs.py`](src/generate_partial_logs.py) | Truncation Benchmark Generator | Generates parametric truncation loss benchmark suites ($0.0\%$ to $20.0\%$ in $2.5\%$ steps) from baseline telemetry by simulating tail-loss event omissions. | `generate_partial_logs()`, `apply_partial_loss_to_case()`, `format_loss_tag()`, `infer_partial_tag()` |
| [`src/generate_mixed_logs.py`](src/generate_mixed_logs.py) | Multi-Fault Matrix Generator | Synthesizes compound defect interactions across the defect grid ($D \times L \in [0.0\%, 20.0\%]^2$) by chaining drift injection followed by truncation loss. | `generate_mixed_logs()`, `format_mixed_tag()`, `infer_mixed_tag()` |
| [`src/idl_parser.py`](src/idl_parser.py) | IDL Contract Oracle | Parses Apache Thrift IDL specifications, enforces the Zero Optional Fields ($\text{ZOF} = 0$) invariant, and generates machine-readable contract oracles (`interfaces/idl-contracts.json`). | `ThriftParser`, `InvariantViolationError`, `pascal_or_camel_to_kebab()` |
| [`src/topology_enricher.py`](src/topology_enricher.py) | Topology & Phase Extractor | Extracts service bindings, front-door REST HTTP ingress endpoints, concurrency phase partitions ($P_1$ vs. $P_2$), and join synchronization barriers to construct `interfaces/social-network.json`. | `enrich_topology()`, `IngressEndpoint`, `DispatchCall`, `JoinBarrier` |
| [`src/build_reference_net.py`](src/build_reference_net.py) | Reference Net Synthesizer | Programmatically builds canonical reference Petri nets from topology specifications and renders DOT, SVG, and PNG visual diagrams. | `build_reference_net()`, `validate_wf_net_invariants()`, `render_diagram()` |
| [`src/project_service_traces.py`](src/project_service_traces.py) | Trace Ingestion & Projection | Ingests multi-flow Jaeger trace JSON exports, enforces global `traceID` deduplication, and projects spans into per-service CSV logs sorted deterministically by `(case_id, timestamp, activity)`. | `load_and_deduplicate_traces()`, `extract_events_from_trace()`, `write_service_csvs()` |
| [`src/export_traces.py`](src/export_traces.py) | Raw Trace Exporter | Utility for extracting and summarizing raw Jaeger distributed traces for benchmark processing. | `export_traces()`, `format_trace_json()` |
| [`src/repair_pipeline.py`](src/repair_pipeline.py) | Standalone Repair CLI | Standalone command-line interface for running the 4-stage repair workflow (Relabel -> Drop -> Re-Mine -> Re-Verify) directly on target log directories. | `run_repair_pipeline()`, `main()` |

---

## 4. Ground Truth IDL Specifications (`IDL/`)

| File | Format | Description |
| :--- | :--- | :--- |
| [`IDL/social_network.thrift`](IDL/social_network.thrift) | Apache Thrift IDL | Machine-readable interface specification for the 12 microservices comprising DeathStarBench `socialNetwork`. Enforces the **Zero Optional Fields ($\text{ZOF}=0$)** invariant: all RPC methods and fields are declared mandatory, serving as the non-heuristic formal ground truth oracle for interaction alphabets. |

---

## 5. Machine-Readable Interface Specifications (`interfaces/`)

| File / Directory | Format | Description |
| :--- | :--- | :--- |
| `interfaces/idl-contracts.json` | JSON Spec | Contract oracle extracted from `social_network.thrift` specifying per-service mandatory client/server RPC pairs and interaction patterns (IP-1 for void send, IP-4 for request-response pair). |
| `interfaces/social-network.json` | JSON Spec | Complete microservice topology oracle specifying service definitions, REST ingress routes, caller-callee bindings, and phased execution graphs ($P_1$ concurrent fan-out, $t_{\mathcal{B}}$ join barrier, $P_2$ sequential dispatches). |
| `interfaces/control-flow-properties.json` | JSON Catalog | Specification catalog defining 8 temporal control-flow properties, target CTL reachability queries, and pass/fail formal invariants. |
| `interfaces/mined-nets.json` | JSON Petri Nets | Serialized Generalized Workflow nets discovered from baseline telemetry under $\text{noise\_threshold} = 0.0$. |
| `interfaces/reference-nets.json` | JSON Petri Nets | Programmatic reference nets for validation. |
| `interfaces/composed-net.json` | JSON Petri Nets | Serialized composed Generalized Workflow net. |
| `interfaces/detection-reports.json` | JSON Report | Observer reachability verification reports. |
| `interfaces/composition-verification-report.json` | JSON Report | Four composition properties verification report. |
| `interfaces/property-verification-report.json` | JSON Report | Eight temporal control-flow properties verification report. |
| `interfaces/lola/` | LoLA Nets (.lola) | 13 canonical LoLA net specifications (12 per-service nets + 1 composed net). |
| `interfaces/diagrams/` | DOT / SVG / PNG | Graphical Petri net diagrams for individual workflows and composed architecture. |

---

## 6. Formal LoLA Model Specifications (`specs/`)

| File | Format | Description |
| :--- | :--- | :--- |
| `specs/lola/social_network_properties.lola` | LoLA CTL Spec | Standalone Computation Tree Logic (CTL) reachability formulas for verifying cross-service coordination invariants directly in external LoLA model checker CLI. |

---

## 7. Baseline Telemetry & Benchmark Datasets (`data/`)

| Path | Format | Description |
| :--- | :--- | :--- |
| `data/logs/` | CSV Event Logs | Clean baseline execution logs for all 12 microservices (1,081 trace cases, 119 `compose-post` transactions, 3,646 spans) collected from DeathStarBench `socialNetwork` via Jaeger distributed tracing. |
| `data/traces/` | JSON Traces (13 MB) | Raw Jaeger distributed trace JSON exports (`compose-post`, `read-home-timeline`, `read-user-timeline`) allowing end-to-end reproduction from Stage 1 (Trace Projection). |
| `data/benchmarks/drift/` | CSV Benchmark Suites | 9 stepped pure label drift benchmark directories (`logs_drift_0` through `logs_drift_20` in 2.5% increments) simulating operation aliasing. |
| `data/benchmarks/partial/` | CSV Benchmark Suites | 9 stepped pure truncation loss benchmark directories (`logs_partial_0` through `logs_partial_20` in 2.5% increments) simulating tail-loss omissions. |
| `data/benchmarks/mixed/` | CSV Benchmark Suites | 25 compound defect suites representing the $5 \times 5$ defect matrix published in Table 4 of the paper ($D \in \{0, 5, 10, 15, 20\} \times L \in \{0, 5, 10, 15, 20\}$). |
| `data/composed/` | LoLA / Visual Nets | Pre-synthesized composed models for immediate model checking (`post_repair_baseline`, `pre_repair_drift_10`, `post_repair_drift_10`). |
| `data/evaluation_report.json` | Master JSON Report | Master evaluation report containing complete numerical metrics, SAT/UNSAT verdicts, retention ratios, and model checking certificates across benchmark suites. |
| `data/evaluation_summary.csv` | Master CSV Table | Tabular benchmark results matching Table 3 and Table 4 of the paper. |

---

## 8. Unit Test Suites (`tests/`)

| Test File | Target Module | Scope |
| :--- | :--- | :--- |
| `tests/test_build_reference_net.py` | `build_reference_net.py` | Validates reference Petri net construction and invariants. |
| `tests/test_contract_drop_repair.py` | `contract_drop_repair.py` | Tests non-conformant gap trace purging and zero synthetic event preservation. |
| `tests/test_detector.py` | `detector.py` | Tests dynamic observer place instrumentation and CTL reachability queries. |
| `tests/test_generate_drift_logs.py` | `generate_drift_logs.py` | Validates deterministic case hashing and alias injection. |
| `tests/test_generate_mixed_logs.py` | `generate_mixed_logs.py` | Tests compound drift and truncation loss composition. |
| `tests/test_generate_partial_logs.py` | `generate_partial_logs.py` | Validates tail-loss truncation simulation. |
| `tests/test_idl_parser.py` | `idl_parser.py` | Tests Apache Thrift parsing and ZOF=0 invariant validation. |
| `tests/test_miner.py` | `miner.py` | Tests Inductive Miner integration and noise threshold enforcement. |
| `tests/test_pipeline.py` | `pipeline.py` | End-to-end integration tests for single and batch pipeline execution. |
| `tests/test_proof_of_call_relabeler.py` | `proof_of_call_relabeler.py` | Tests cross-service caller-callee correlation and lossless relabeling. |
| `tests/test_property_checker.py` | `verify_properties.py` | Tests 8 temporal control-flow CTL properties and BFS state-space search. |
| `tests/test_repair_pipeline.py` | `repair_pipeline.py` | Integration test for the standalone repair workflow. |
| `tests/test_topology_enricher.py` | `topology_enricher.py` | Tests topology extraction and phase graph partitioning. |
| `tests/test_trace_projection.py` | `project_service_traces.py` | Tests trace deduplication and projection to per-service CSV logs. |
| `tests/test_workflow_net_composer.py` | `workflow_net_composer.py` | Tests phased asynchronous channel fusion, barrier synthesis, and composition verification. |
