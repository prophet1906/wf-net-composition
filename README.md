# Artifact Evaluation & Reproducibility Guide

[![Rocq Prover](https://img.shields.io/badge/Rocq-9.2+-blue.svg)](https://rocq-prover.org/)
[![Python](https://img.shields.io/badge/Python-3.8+-green.svg)](https://www.python.org/)
[![Process Mining](https://img.shields.io/badge/PM4Py-2.7+-orange.svg)](https://pm4py.fit.fraunhofer.de/)
[![Model Checker](https://img.shields.io/badge/LoLA-2.0-purple.svg)](https://service-technology.org/lola/)

---

## 1. Overview of the Artifact

This artifact provides the complete toolchain, formal specifications, machine-checked interactive proofs, and benchmark telemetry to reproduce all claims, theorems, algorithms, and empirical results reported in the paper.

The package consists of two tightly coupled pillars:
1. **Machine-Checked Rocq Formal Proofs (`proofs/`)**:  
   Formal proofs in the Rocq Prover (v9.2+, standard library) certifying van der Aalst Workflow Net soundness, Interface Patterns IP-1/IP-4, Theorem 1 (Repair Monotonicity & Soundness Restoration), Theorem 2 (Phased Composition Soundness Preservation: option to complete, proper completion, clean channel drainage, 1-boundedness, barrier liveness, and dead-transition freedom), negative control silent $\tau$-skip deadlocks, and structural isomorphism with DeathStarBench *socialNetwork*.
2. **End-to-End Discovery, Repair & Verification Pipeline (`src/`, `pipeline.py`)**:  
   An automated 6-stage toolchain implementing:
   - **Stage 1**: Distributed trace ingestion and deterministic per-service projection from Jaeger telemetry.
   - **Stage 2**: Noise-unfiltered inductive process mining ($\texttt{noise\\_threshold}=0.0$) guaranteeing 100% variant retention.
   - **Stage 3**: Deductive $\tau$-skip model checking using dynamically instrumented observer places ($obs_x$) evaluated via CTL reachability queries ($\Phi_{\text{obs}} = \mathbf{EF}(\text{sink} > 0 \land obs_x = 0)$).
   - **Stage 4**: Interface-guided formal repair combining lossless caller-callee Proof-of-Call relabeling ($\rho_{\text{ret}}=1.0$) and contract-guided DROP-repair ($\Delta_{\text{synth}}=0$).
   - **Stage 5**: Phased Microservice Composition fusing Generalized Workflow nets ($N_C = \bigoplus_{\text{phased}} R_i^*$) across asynchronous channels with synchronization join barriers ($t_{\mathcal{B}}$).
   - **Stage 6**: Temporal control-flow property verification checking 8 domain-specific CTL properties across all reachable markings using LoLA or our built-in state-space exploration engine.

---

## 2. Directory Structure

```
wf-net-composition/
├── README.md               # This artifact evaluation & reproducibility guide
├── CODE_OVERVIEW.md        # File-by-file architectural and component catalog
├── Makefile                # Unified build, test, and verification automation interface
├── requirements.txt        # Python library dependencies
├── pipeline.py             # Top-level CLI entry point for evaluation
├── IDL/
│   └── social_network.thrift # Apache Thrift IDL contract ground truth (ZOF=0)
├── proofs/                 # Rocq (Coq) formal proof development
│   ├── _CoqProject         # Logical namespace mapping (-Q . MicroserviceComposition)
│   ├── composition.v       # 1,489-line complete machine-checked formal proof
│   ├── Makefile            # Build rules for Rocq compilation
│   ├── Makefile.local      # Local targets (make check for kernel verification)
│   ├── Makefile.conf       # Build configuration flags
│   └── README.md           # Documentation & paper-to-lemma mapping table
├── src/                    # Python implementation of discovery, repair, and verification
│   ├── pipeline.py         # End-to-end verification harness and benchmark driver
│   ├── miner.py            # Inductive process mining under zero-noise threshold
│   ├── detector.py         # Observer place instrumentation and CTL reachability queries
│   ├── proof_of_call_relabeler.py # Cross-service span correlation & lossless relabeling
│   ├── contract_drop_repair.py    # Non-conformant gap trace purging without synthetic events
│   ├── workflow_net_composer.py   # Phased composition with join barrier & channel fusion
│   ├── verify_properties.py       # CTL model checker for 8 temporal control-flow properties
│   ├── idl_parser.py       # Thrift IDL parser enforcing Zero Optional Fields
│   ├── topology_enricher.py# Phase graph and synchronization barrier extractor
│   ├── build_reference_net.py # Programmatic reference net builder
│   ├── project_service_traces.py # Trace deduplication & per-service projection
│   ├── export_traces.py    # Raw Jaeger trace exporter
│   ├── repair_pipeline.py  # Standalone 4-phase repair CLI
│   └── generate_*_logs.py  # Parametric benchmark suite generators (drift, partial, mixed)
├── interfaces/             # Machine-readable contract oracles, topologies, and models
│   ├── idl-contracts.json  # Extracted RPC contracts and interaction patterns (IP-1, IP-4)
│   ├── social-network.json # Service bindings, phases (P1 fan-out, barrier, P2 dispatch)
│   ├── control-flow-properties.json # Specifications for 8 CTL temporal properties
│   ├── mined-nets.json     # Mined baseline workflow nets
│   ├── composed-net.json   # Composed multi-service system net
│   ├── lola/               # 13 canonical LoLA net specifications
│   └── diagrams/           # Canonical Petri net diagrams (DOT, PNG, SVG)
├── specs/
│   └── lola/social_network_properties.lola # Standalone CTL formulas for LoLA CLI
├── tests/                  # 15 automated unit and integration test suites
│   └── test_*.py
└── data/                   # Telemetry event logs and evaluation benchmark suites
    ├── logs/               # 12 clean baseline service event logs (1,081 cases, 3,646 spans)
    ├── traces/             # Raw Jaeger distributed traces (5,000 requests, 13 MB)
    ├── benchmarks/         # Stepped defect suites (0% to 20% in 2.5% increments)
    │   ├── drift/          # 9 pure label drift benchmark directories
    │   ├── partial/        # 9 pure truncation loss benchmark directories
    │   └── mixed/          # 81 compound defect benchmark directories (full 9x9 D x L grid; Table 4 shows a readable 5x5 excerpt)
    ├── composed/           # Pre-synthesized composed models for immediate checking
    ├── evaluation_report.json # Pre-computed master evaluation report with certificates
    └── evaluation_summary.csv  # Per-suite metrics for all 100 benchmark suites (Table 3 & 4 + aggregate totals)
```

---

## 3. System Requirements & Environment Setup

### 3.1 Hardware & OS
- **OS**: Linux (Ubuntu 20.04+, Debian 11+, RHEL 8+), macOS (Big Sur through Sequoia), or Windows via WSL2.
- **CPU**: Dual-core x86_64 or Apple Silicon ARM64.
- **Memory**: Minimum 4 GB RAM (8 GB recommended for batch sweeps).
- **Disk Space**: ~250 MB total for repository, datasets, and generated models.

### 3.2 Software Dependencies
1. **Python (3.8+)**:
   Install requirements using `pip`:
   ```bash
   pip3 install -r requirements.txt
   ```
2. **Rocq Prover (v9.2+)** (for formal proofs):
   - **macOS (via Homebrew)**:
     ```bash
     brew install rocq
     ```
   - **Linux / macOS (via OPAM)**:
     ```bash
     opam repo add coq-released https://coq.inria.fr/opam/released
     opam install rocq-prover
     ```
   Verify installation:
   ```bash
   rocq --version   # Expected: The Rocq Prover, version 9.2 (or higher)
   ```
3. **Graphviz (Optional)**:
   Used for rendering DOT diagrams into SVG/PNG (`brew install graphviz` or `sudo apt-get install graphviz`).
4. **LoLA Model Checker (Optional / Recommended)**:
   Used for external explicit-state model checking. A prebuilt macOS arm64 binary
   (LoLA 2.0) ships at the repo root as `./lola`; select it with
   `--engine lola --lola-bin ./lola`. On other platforms, install LoLA and pass
   `--engine lola` (it is picked up from `$PATH`).
   > **Built-in Fallback**: The framework includes an internal, zero-dependency pure-Python BFS state-space reachability solver. If `lola` is not present in `$PATH`, the pipeline automatically activates this internal solver with 100% feature and verdict parity.

---

## 4. Pre-Flight Diagnostic Check

Run the environment validation tool:
```bash
python3 pipeline.py --check-env
# or: make check-env
```

**Expected Output**:
```text
======================================================================
  Artifact Evaluation Environment Pre-Flight Diagnostics
======================================================================
  * Python Runtime         : [OK] 3.8+ (/path/to/python3)
  * PM4Py Process Mining   : [OK] 2.7+
  * LoLA Model Checker     : [OK or OPTIONAL (Internal Solver Active)]
  * Graphviz Dot           : [OK or OPTIONAL]
----------------------------------------------------------------------
  [+] Environment is ready for pipeline execution.
======================================================================
```

---

## 5. Quick Start: Rocq Formal Proofs (10 Seconds)

To compile and verify all theoretical proofs in the Rocq Prover:

```bash
# Compile proofs to bytecode
make proofs
# or: cd proofs && make

# Validate proof terms with the independent Rocq kernel proof checker
make check
# or: cd proofs && make check
```

**Why this matters**:
`rocq check` invokes Rocq's stand-alone minimal kernel verifier to independently check every proof term in `composition.v`. It guarantees:
- Zero unproven holes (`admit`, `Admitted` are absent).
- Zero speculative axioms (`Axiom` is absent).
- Every lemma and theorem is closed and certified.

**Expected Output from `make check`**:
```text
==> Validating proofs with kernel checker (rocq check)...
rocq check -Q . MicroserviceComposition MicroserviceComposition.composition
...
Modules were successfully checked
==> All proof terms successfully verified by the kernel.
```

---

## 6. Quick Start: 60-Second Empirical Pipeline Demo

Reviewers can execute the complete end-to-end empirical verification harness across representative defect tiers (10% Label Drift and 10% Truncation Loss) in under 60 seconds:

```bash
python3 pipeline.py --demo
# or: make demo
```

### What the Demo Executes:
1. **Phase 1 (Pre-Repair Defect Demonstration)**:
   - Mines flawed logs under `noise_threshold = 0.0`.
   - Traps false silent $\tau$-skips via observer reachability queries (`SAT` verdicts).
   - Composes multi-service net and traps deadlock (`DEADLOCK / VIOLATED`).
2. **Phase 2 (Formal Repair)**:
   - Lossless Proof-of-Call relabeling (rescues 100% of drifted client spans via callee server spans).
   - Contract-guided DROP-repair (purges unobservable gap traces with $\Delta_{\text{synth}} = 0$).
3. **Phase 3 (Post-Repair Re-Verification)**:
   - Re-mines repaired logs under `noise_threshold = 0.0`.
   - Formally certifies elimination of false $\tau$-skips (`UNSAT` certificates).
   - Composes multi-service net with join barrier $t_{\mathcal{B}}$ and channel fusion.
   - Model-checks 4 composition properties and 8 temporal control-flow properties (`VERIFIED`).
4. **Phase 4 (Reporting & Cataloging)**:
   - Emits ANSI summary table, updates `data/evaluation_report.json`, and catalogs `.lola` model files.

---

## 7. Mapping Paper Claims to Artifact Evidence

| Paper Element | Claim / Finding | Artifact Command / Location | Expected Result |
| :--- | :--- | :--- | :--- |
| **Theorem 1** | Monotone gap reduction and soundness restoration by repair without synthetic data ($\Delta_{\text{synth}}=0$). | `cd proofs && make check` <br> Look for `relabeling_monotone_gap_reduction`, `repaired_log_contains_mandatory`, `repair_guarantees_alpha_conformance`. | Certified closed by Rocq kernel; `synthetic_events_inserted: 0` in empirical logs. |
| **Theorem 2** | Phased Composition ($N_C = \bigoplus_{\text{phased}} R_i^*$) preserves option to complete, proper completion, clean drainage, 1-boundedness, barrier liveness, and dead-transition freedom. | `cd proofs && make check` <br> Look for `generic_phased_composition_soundness_preservation` and sub-lemmas. | Certified closed by Rocq kernel without axioms. |
| **Negative Control (Fig. 1a)** | Unrepaired silent $\tau$-skip bypassing mandatory send induces callee starvation deadlock. | `cd proofs && make check` <br> Look for `generic_tau_skip_leads_to_callee_starvation_deadlock`. | Certified closed in Rocq; trapped in LoLA (`DEADLOCK`). |
| **Table 1** | All 8 temporal control-flow properties hold on post-repair composed net $N_C$ (7 UNSAT, 1 SAT for P8 async witness). | `python3 src/verify_properties.py --net data/composed/post_repair_baseline/lola/composed-net.lola --properties interfaces/control-flow-properties.json` | 8/8 properties match target verdicts (P1--P7: UNSAT, P8: SAT). |
| **Table 2** | Model metrics and verification verdicts across clean, flawed (25% loss), and post-repair logs. | `python3 pipeline.py --logs data/benchmarks/drift/logs_drift_10/` | Flawed: $\tau = 2$, Deadlock: SAT. <br> Repaired: $\tau = 0$, Deadlock: UNSAT, 1-Bounded: SAT. |
| **Table 3** | Pure drift suites achieve $\rho_{\text{ret}} = 100.00\%$ trace retention (1,670 rescued spans, 72 $\text{SAT}\to\text{UNSAT}$); pure truncation loss retains $\ge 99.78\%$ traces with 0 synthetic events. | `python3 pipeline.py --benchmark drift` <br> `python3 pipeline.py --benchmark partial` <br> (or inspect `data/evaluation_summary.csv`) | Matches Table 3 values row-by-row for all 18 suites ($0.0\%$ to $20.0\%$). |
| **Table 4** | Compound defect grid, run as the full $9 \times 9$ matrix ($D \times L$, 81 suites); the paper's Table 4 reports a readable $5 \times 5$ excerpt. Retains $\ge 99.78\%$ traces across all tiers with all post-repair composed nets verified sound. | Inspect the `mixed_*` rows of `data/evaluation_summary.csv` or run: <br> `python3 pipeline.py --benchmark mixed --engine lola --lola-bin ./lola` | Retention ratios and rescued spans match the Table 4 excerpt exactly (full grid superset available). |
| **Aggregate (100 suites)** | Across all 9 drift + 9 truncation + 81 mixed + 1 baseline suites: 98,760 traces ingested, 98,630 retained (**99.87%**), 16,042 drifted spans rescued, 776 $\text{SAT}\to\text{UNSAT}$ transitions (100% of false $\tau$-skips eliminated), 100/100 composed nets sound. | `python3 pipeline.py --benchmark all --engine lola --lola-bin ./lola` <br> (writes `data/evaluation_summary.csv` + `data/evaluation_report.json`) | Aggregate totals over all 100 rows match the paper's headline numbers exactly. |

---

## 8. Full Benchmark Suite Reproduction

### 8.1 Evaluating Specific Defect Suites
```bash
# 1. Pure Label Drift benchmarks (0.0% to 20.0% in 2.5% steps)
python3 pipeline.py --benchmark drift
# or: make benchmark-drift

# 2. Pure Truncation Loss benchmarks (0.0% to 20.0% in 2.5% steps)
python3 pipeline.py --benchmark partial
# or: make benchmark-partial

# 3. Clean Baseline Telemetry
python3 pipeline.py --benchmark baseline

# 4. Mixed Compound Defect Matrix (full 9x9 grid, 81 suites)
python3 pipeline.py --benchmark mixed
```

### 8.2 Parametric Defect Suite Generation
To generate custom defect sweeps from clean baseline telemetry:
```bash
python3 pipeline.py --generate-benchmarks --range 0 20 --step 2.5 --defect-type all
```

### 8.3 Single Log Directory Evaluation
Run the pipeline on any specific log directory:
```bash
python3 pipeline.py --logs data/benchmarks/drift/logs_drift_10/
```

---

## 9. Direct Model Checking with LoLA CLI

All synthesized Petri net models are saved in standard LoLA format (`.lola`) in `data/composed/` and `interfaces/lola/`. If LoLA is installed, reviewers can run ad-hoc CTL queries directly from the command line:

### 1. Composition Soundness / Deadlock Freedom
Verify that no reachable deadlock states exist prior to terminal completion:
```bash
lola data/composed/post_repair_baseline/lola/composed-net.lola \
  --formula="EF(DEADLOCK AND NOT (p_end_1 > 0 AND p_end_2 > 0))" \
  --search=covergraph
```
*Expected Result*: `result: no` ($\text{UNSAT} \implies$ Deadlock-Free / Sound).

### 2. Channel 1-Boundedness
Verify that asynchronous channel capacity never exceeds 1 token:
```bash
lola data/composed/post_repair_baseline/lola/composed-net.lola \
  --formula="AG(ch_ComposeText <= 1)" \
  --search=covergraph
```
*Expected Result*: `result: yes` ($\text{TRUE} \implies$ 1-Bounded Channel).

### 3. Verification of All 8 Temporal Control-Flow Properties via Python CLI
```bash
python3 src/verify_properties.py \
  --net data/composed/post_repair_baseline/lola/composed-net.lola \
  --properties interfaces/control-flow-properties.json \
  --output data/composed/post_repair_baseline/property_report.json
```
*Expected Result*: All 8 properties hold with 0 violations.

---

## 10. Automated Test Suite

To run all 15 unit and integration tests:
```bash
python3 -m unittest discover tests
# or: make test
```

All tests pass, verifying IDL parsing, trace projection, observer place construction, relabeling, drop-repair, phased composition, and property checking.
