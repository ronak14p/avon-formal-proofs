# Avon Labs — Machine-Verified Lean 4 Formalizations

**Author:** Ronak Patel, Avon Labs (`@ronak14p`)  
**Technical Report (PDF):** [`paper/Avon-Labs-Lean4-Formalizations-2026-11-27.pdf`](paper/Avon-Labs-Lean4-Formalizations-2026-11-27.pdf)  
**License:** Apache-2.0 (see [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE))  
**Toolchain:** Lean 4 (`v4.33.1`) · Zero `sorry` · Zero `admit` · Zero `native_decide` / `ofReduceBool` · Standard axioms only (`propext`, `Classical.choice`, `Quot.sound`)

---

## Overview

This repository publishes **9 standalone, kernel-verified Lean 4 formalizations totaling 11,677 lines** across extremal combinatorics, finite group theory, graph theory, and irrationality theory, verified and timestamped on **November 27, 2026 (04:08–05:10 UTC)** against statement definitions from Google DeepMind's Apache-2.0 [`formal-conjectures`](https://github.com/google-deepmind/formal-conjectures) benchmark.

Full technical proof summaries, methodology notes, immutable GitHub submission timestamps, and SHA-256 digests are compiled in [`paper/Avon-Labs-Lean4-Formalizations-2026-11-27.pdf`](paper/Avon-Labs-Lean4-Formalizations-2026-11-27.pdf).

> **Attribution:** Our contribution is the machine-verified Lean 4 formalization and kernel-checkable certificate design. All underlying mathematical theorems, bounds, and counterexample constructions are credited to their original authors below and inside each file.

---

## Verified Standalone Proofs (`proofs/`, 9 files · 11,677 lines)

| Benchmark Declaration | Domain | Lines | Submitted (2026-11-27 UTC) | Upstream Status | Mathematical Source Credited |
|---|---|---:|---|---|---|
| [`Constant6a.c6a_lower_bound_improved.lean`](proofs/Constant6a.c6a_lower_bound_improved.lean) | Union-Closed | 1,549 | `05:01:59Z` | PR `#3208` (CI green) | Liu (`arXiv:2306.08824`) + Costa & Sadhu (`arXiv:2610.02295`), proving `0.382725 ≤ C6a` |
| [`UnionClosed.union_closed.variants.yu.lean`](proofs/UnionClosed.union_closed.variants.yu.lean) | Union-Closed | 1,612 | `05:09:53Z` | PR `#3250` (CI green) | Yu (*Entropy* 2023) arbitrary ground type via Liu + Costa & Sadhu coupling |
| [`Constant6a.c6a_lower_bound.lean`](proofs/Constant6a.c6a_lower_bound.lean) | Union-Closed | 1,547 | `04:49:49Z` | PR `#3191` (closed: superseded upstream by `#3085`) | Liu (`arXiv:2306.08824`, `0.38271 ≤ C6a`) |
| [`Constant6a.c6a_lower_bound_intermediate.lean`](proofs/Constant6a.c6a_lower_bound_intermediate.lean) | Union-Closed | 2,648 | `04:34:20Z` | PR `#3049` (**Merged**) | Sawin (`2211.11504`), Yu (`2212.00658`), Cambie (`2212.12500`, `0.38234 ≤ C6a`) |
| [`Constant6a.c6a_lower_bound_first.lean`](proofs/Constant6a.c6a_lower_bound_first.lean) | Union-Closed | 1,251 | `04:19:06Z` | PR `#2846` (**Merged**) | Gilmer (2022) / Chase & Lovett (`2211.11689`)* |
| [`Mathoverflow508539.mathoverflow_508539.lean`](proofs/Mathoverflow508539.mathoverflow_508539.lean) | Hypercube | 451 | `04:26:37Z` | PR `#2945` (**Merged**) | MathOverflow 508539 (`E · V ≥ N²/4` via fibre induction) |
| [`Erdos267.erdos_267.variants.fibonacci_inverse_sum.lean`](proofs/Erdos267.erdos_267.variants.fibonacci_inverse_sum.lean) | Number Theory | 1,180 | `05:00:07Z` | PR `#3207` (CI green) | André-Jeannin (1989), irrationality of `∑ 1/F_n` via Fibonomial Padé forms |
| [`Kourovka.19.25.kourovka_19_25.lean`](proofs/Kourovka.19.25.kourovka_19_25.lean) | Group Theory | 1,030 | `05:05:37Z` | PR `#3214` (CI green) | Explicit order-6,048 witness `PSU(3,3)` vs `C_6 × S_4 × (C_7 ⋊ C_6)` (`arXiv:2607.17477`) |
| [`WrittenOnTheWallII.GraphConjecture72.conjecture72.lean`](proofs/WrittenOnTheWallII.GraphConjecture72.conjecture72.lean) | Graph Theory | 409 | `04:08:43Z` | PR `#2740` (CI green · Lean checker accepted · `needs-human-review`) | Gebendorfer's 31-vertex graph `G(2,24)` (DeLaViña WOWII disproof) |

*\*`Constant6a.c6a_lower_bound_first.lean` adapts the scalar entropy inequality from Ho Boon Suan & Aristotle (Harmonic) under the MIT License (full notice retained in-file and in [`NOTICE`](NOTICE)).*

---

### Upstream Status Snapshot (2026-11-27, 05:44 UTC)

Submitted to the public [`open-math-agents`](https://github.com/GuillaumeBAUD-coder/open-math-agents) Lean 4 checker:

- **Merged (3):** `#2846` `Constant6a.c6a_lower_bound_first` · `#2945` `Mathoverflow508539.mathoverflow_508539` · `#3049` `Constant6a.c6a_lower_bound_intermediate`. Each was kernel-accepted with axioms limited to `propext`, `Classical.choice`, `Quot.sound`.
- **CI green, open (5):** `#3208` `c6a_lower_bound_improved` · `#3250` `union_closed.variants.yu` · `#3207` `erdos_267` Fibonacci variant · `#3214` `kourovka_19_25` · `#2740` `GraphConjecture72` (accepted by the Lean checker; awaiting maintainer statement review, as is standard for open-problem disproofs).
- **Closed as superseded (1):** `#3191` `Constant6a.c6a_lower_bound`. Upstream merged a separate proof (`#3085`) first. Our independent formalization is kept here unchanged.

The technical report PDF records the status as of report generation (05:26 UTC). The list above is the later snapshot. Live status can always be checked on the linked pull requests.

---

## Independent Verification

1. Verify file integrity against the published manifest:
   ```bash
   sha256sum -c SHA256SUMS.txt
   ```
2. Compile any proof against Lean `v4.33.1`, Mathlib, and `google-deepmind/formal-conjectures`:
   ```bash
   lake env lean proofs/Constant6a.c6a_lower_bound_improved.lean
   ```
3. Confirm standard axioms only (`propext`, `Classical.choice`, `Quot.sound`) with `#print axioms OMA.solution` (or `#print axioms OMA.disproof` for Graph Conjecture 72).
4. Download the immutable release bundle (PDF + `SHA256SUMS.txt`) from [Release `v1.0.0`](https://github.com/ronak14p/avon-formal-proofs/releases/tag/v1.0.0).
