# Rocq Formal Proofs: Interface-Guided Verification of Microservice Architecture

Formal Rocq (formerly Coq) proofs accompanying the paper:  
**"Interface-Guided Verification of Control-Flow Properties in Microservice Architecture"**

This directory contains machine-checked proofs for all theoretical claims, theorems, interface patterns, and temporal invariants presented in the paper, grounded in the classical Workflow Net foundations of van der Aalst (1998, 2020) and Nesterov et al. (2023), and mirroring the Python implementation in `src/`.

---

## 1. Prerequisites

The proofs are compatible with **Rocq 9.x** (and Coq 8.18+):

- **Rocq Prover**: Version 9.2 (or later)
- **GNU Make**: Version 3.81 (or later)
- **Standard Library**: `From Stdlib Require Import ...` (Rocq 9 standard layout)

### Installation (macOS via Homebrew)
```bash
brew install rocq
```

### Installation (Linux / macOS via OPAM)
```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam install rocq-prover
```

Verify your installation:
```bash
rocq --version
# Output: The Rocq Prover, version 9.2 (or higher)
```

---

## 2. Directory Structure

```
proofs/
├── _CoqProject         # Rocq project configuration (-Q logical mapping & source list)
├── Makefile            # Rocq-generated build system (rocq makefile -f _CoqProject -o Makefile)
├── Makefile.conf       # Rocq configuration generated from _CoqProject
├── Makefile.local      # Local build hooks for custom targets (check, rebuild)
├── README.md           # This documentation
├── composition.v       # The primary Rocq formalization source file
└── *.pdf / *.org       # Literature references (van der Aalst 2020, Nesterov 2023)
```

---

## 3. Step-by-Step Build and Run Instructions

### Generating the Makefile
The build system is generated from [`_CoqProject`](file://proofs/_CoqProject) using `rocq makefile`:
```bash
cd proofs
rocq makefile -f _CoqProject -o Makefile
```
*(Note: `Makefile` already contains an internal dependency rule to automatically re-run `rocq makefile` whenever `_CoqProject` is modified).*

---

### Option A: Standard Build via `make` (Recommended)

From within the `proofs/` directory (or from the project root):

```bash
cd proofs
make
```
*(Or from the repository root: `make`)*

This compiles [`composition.v`](file://proofs/composition.v) into binary bytecode artifacts (`composition.vo`, `composition.glob`).

> [!NOTE]
> `make` is an incremental build tool. If `composition.v` has already been compiled and hasn't changed, `make` will report:
> ```text
> make[1]: Nothing to be done for 'real-all'.
> ```
> To force a clean re-compilation from scratch, run `make rebuild`.

---

### Option B: Force Re-compilation (`make rebuild`)

To delete existing build artifacts and re-compile all proof files from scratch:

```bash
make rebuild
# or: cd proofs && make rebuild
```

---

### Option C: Independent Kernel Verification (`make check`)

To run Rocq's stand-alone kernel proof checker (`rocq check` / `rocqchk`) over the compiled binary module:

```bash
make check
```

**Why this matters**:  
`rocq check` validates that every theorem and lemma was checked strictly by the trusted minimal kernel, certifying that:
- No unproven `admit` or `Axiom` holes exist.
- All proof terms are mathematically sound and closed.

Expected output:
```text
==> Validating proofs with kernel checker (rocq check)...
rocq check -Q . MicroserviceComposition MicroserviceComposition.composition
...
Modules were successfully checked
==> All proof terms successfully verified by the kernel.
```

---

### Option D: Cleaning Build Artifacts

- **Remove compiled object files (`.vo`, `.glob`, `.aux`)**:
  ```bash
  make clean
  ```

- **Complete wipe including generated makefiles (`Makefile.coq`)**:
  ```bash
  make distclean
  ```

---

### Option E: Direct CLI Compilation (Without `make`)

You can also invoke the Rocq compiler directly:

```bash
# Using logical mapping matching _CoqProject
rocq compile -Q . MicroserviceComposition composition.v

# Or standalone compilation
rocq compile composition.v
```

---

### Option F: Interactive Proof Development (IDE)

`_CoqProject` enables immediate language server discovery:
- **VS Code / Cursor**: Install the **VsCoq** extension (`maximedenes.vscoq`). Opening `proofs/composition.v` will automatically bind the logical module path.
- **Emacs**: Install **Proof General**. Open `composition.v` and step through proofs using `C-c C-n` / `C-c C-u`.
- **RocqIDE**: Launch `rocq ide -Q . MicroserviceComposition composition.v`.

---

## 4. Mapping: Paper Theorems vs. Formal Rocq Definitions

The proofs in [`composition.v`](file://proofs/composition.v) are organized into six logical sections matching the structure and claims in `draft.pdf`:

| Paper Claim / Concept | Paper Reference | Rocq Construct in `composition.v` | Description |
| :--- | :--- | :--- | :--- |
| **Workflow Net Soundness** | Section 3, Def. 5 & 6 | [`WorkflowNet`](file://proofs/composition.v#L225), [`is_sound`](file://proofs/composition.v#L230) | Option to complete, proper completion, and dead-transition freedom (van der Aalst 1998, Nesterov 2023). |
| **Interface Pattern IP-1** | Section 3.2, Fig. 3 | [`ip1_composed_net`](file://proofs/composition.v#L278), [`ip1_reaches_final`](file://proofs/composition.v#L324), [`ip1_orphan_freedom`](file://proofs/composition.v#L329) | One-way asynchronous dispatch reaching final marking with 0 orphan channel tokens. |
| **Interface Pattern IP-4** | Section 3.2, Fig. 3 | [`ip4_composed_net`](file://proofs/composition.v#L338), [`ip4_reaches_final`](file://proofs/composition.v#L384), [`ip4_orphan_freedom`](file://proofs/composition.v#L388) | Two-way asynchronous request/reply with complete bilateral channel drainage. |
| **Theorem 1 (Arm 1)** | Section 4, Theorem 1 | [`relabeling_monotone_gap_reduction`](file://proofs/composition.v#L456) | Proof-of-call relabeling $\rho$ monotonically reduces contract gaps without introducing spurious gap violations. |
| **Theorem 1 (Arm 2)** | Section 4, Theorem 1 | [`repaired_log_contains_mandatory`](file://proofs/composition.v#L471) | Contract DROP-repair ensures trace completeness over interface alphabet $A$. |
| **Theorem 1 (Synthesis)** | Section 4, Stage 4/5 | [`phi_obs`](file://proofs/composition.v#L487), [`repair_guarantees_alpha_conformance`](file://proofs/composition.v#L496) | Observer net property $\Phi_{obs}$ evaluates to UNSAT, certifying that repair restores $\alpha$-refinement ($R_i^* \to_\alpha A_i$). |
| **Theorem 2 (Part 1)** | Section 5, Theorem 2 | [`generic_phased_can_complete`](file://proofs/composition.v#L688), [`generic_phased_proper_completion`](file://proofs/composition.v#L694) | Phased composition preserves global option to complete and unique termination at $M_{f,C}$. |
| **Theorem 2 (Part 2)** | Section 5, Theorem 2 | [`generic_phased_clean_channel_drainage`](file://proofs/composition.v#L700) | Clean channel drainage: all interface channels $ch \in P_{chan}$ contain exactly 0 tokens at termination (orphan freedom). |
| **Theorem 2 (Part 3)** | Section 5, Theorem 2 | [`generic_phased_channels_1_bounded`](file://proofs/composition.v#L716) | Channel 1-boundedness: $\forall ch \in P_{chan}, \forall m \in [M_0\rangle, m(ch) \le 1$. |
| **Theorem 2 (Part 4)** | Section 5, Theorem 2 | [`generic_phased_barrier_is_live`](file://proofs/composition.v#L738) | Barrier liveness: synchronization barrier $t_B$ is fireable once Phase 1 completions arrive. |
| **Theorem 2 (Part 5)** | Section 5, Theorem 2 | [`generic_phased_dead_transition_freedom`](file://proofs/composition.v#L745) | Dead-transition freedom: every transition in the composed net is fireable from the initial marking. |
| **Theorem 2 (Synthesis)** | Section 5, Theorem 2 | [`generic_phased_composition_soundness_preservation`](file://proofs/composition.v#L790) | Comprehensive soundness preservation of phased composition. |
| **Negative Control** | Section 2, Fig. 1a | [`generic_tau_skip_leads_to_callee_starvation_deadlock`](file://proofs/composition.v#L903) | Unrepaired silent $\tau$-skip bypassing mandatory send starves downstream callee, trapping net in premature deadlock. |
| **Temporal Property 1** | Section 5.3 (Stage 6) | [`generic_prop_fork_join_precedence`](file://proofs/composition.v#L917) | `PROP_FORK_JOIN`: Join barrier $t_B$ strictly precedes Phase 2 dispatches. |
| **Temporal Property 2** | Section 5.3 (Stage 6) | [`generic_prop_mutex_source_sink`](file://proofs/composition.v#L925) | `PROP_MUTEX`: Orchestrator entry place $p_{in}$ and sink place $p_{sink}$ are mutually exclusive. |
| **Case Study Instantiation** | Section 6 (Evaluation) | [`Section DeathStarBenchInstantiation`](file://proofs/composition.v#L947) | Structural isomorphism mapping generic places to DeathStarBench socialNetwork (`MediaService`, `TextService`, etc.). |

---

## 5. Verification Principles Followed

1. **Domain Generality**: Core theorems use generic mathematical identifiers ($P_1, B, P_2, P_{chan}, ch_k$). Application benchmarks (e.g. DeathStarBench) are isolated in Section VII.
2. **Transparent, Human-Readable Proofs**:
   - Zero opaque computation (`vm_compute` is forbidden).
   - Zero automated guessing (`assumption`, `auto`, `easy`, `tauto` are avoided).
   - Explicit named markings (`gm0` to `gm10`) and transition steps (`gstep0` to `gstep9`).
   - Clean, linear forward reachability proofs via [`reachable_step_forward`](file://proofs/composition.v#L214).
