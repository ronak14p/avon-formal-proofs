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

*\*`Constant6a.c6a_lower_bound_first.lean` adapts the scalar entropy inequality from Ho Boon Suan & Aristotle (Harmonic) under the MIT License (full notice retained in-file and in [`NOTICE`](NOTICE)). That inequality generalizes R. B. Boppana's binary-entropy inequality `h(x²) ≥ φ·x·h(x)` (R. B. Boppana, [*A Useful Inequality for the Binary Entropy Function*](https://arxiv.org/abs/2301.09664), `arXiv:2301.09664`; Ho Boon Suan, *A generalization of Boppana's entropy inequality*, `arXiv:2601.19327`); credit for the inequality belongs to Boppana, Ho and Aristotle.*

---

### Upstream Status Snapshot (2026-11-27, 05:44 UTC)

Submitted to the public [`open-math-agents`](https://github.com/GuillaumeBAUD-coder/open-math-agents) Lean 4 checker:

- **Merged (3):** `#2846` `Constant6a.c6a_lower_bound_first` · `#2945` `Mathoverflow508539.mathoverflow_508539` · `#3049` `Constant6a.c6a_lower_bound_intermediate`. Each was kernel-accepted with axioms limited to `propext`, `Classical.choice`, `Quot.sound`.
- **CI green, open (5):** `#3208` `c6a_lower_bound_improved` · `#3250` `union_closed.variants.yu` · `#3207` `erdos_267` Fibonacci variant · `#3214` `kourovka_19_25` · `#2740` `GraphConjecture72` (accepted by the Lean checker; awaiting maintainer statement review, as is standard for open-problem disproofs).
- **Closed as superseded (1):** `#3191` `Constant6a.c6a_lower_bound`. Upstream merged a separate proof (`#3085`) first. Our independent formalization is kept here unchanged.

The technical report PDF records the status as of report generation (05:26 UTC). The list above is the later snapshot. Live status can always be checked on the linked pull requests.

---

## Ben Green's Open Problem 19: the popular-corner exponent `C = 4` in `𝔽₂ⁿ × 𝔽₂ⁿ` (release `v1.1.0-green19`)

**Paper:** [`paper/Kernel-Checked-Green-Problem-19-2026-11-27-v2.pdf`](paper/Kernel-Checked-Green-Problem-19-2026-11-27-v2.pdf). *A Kernel-Checked Lean 4 Formalization of the Popular-Corner Exponent C = 4 in F_2^n x F_2^n (Ben Green's Open Problem 19)*, Ronak Patel (Avon Labs), November 27, 2026.

| File | Lines | SHA-256 | Role |
|---|---:|---|---|
| [`proofs/Green19.green_19.lean`](proofs/Green19.green_19.lean) | 7,001 | `30dfe0c581913817fc3f2feeb25b0cad7d080c5c54a384b4040236a2ebf6f9ee` | Imports `FormalConjectures.GreensOpenProblems.«19»` and proves the upstream statements `Green19.green_19`, `.lower` and `.upper` (`upstream_green_19*` at the end of the file, typed by `type_of%`); the standalone definitions are checked equal to the upstream ones by `rfl`. |
| [`proofs/Green19.green_19.standalone.lean`](proofs/Green19.green_19.standalone.lean) | 6,975 | `4032046c1b6f4916311301822d867c44b2a6848f705be94ed26214b03733036d` | The same proof with `import Mathlib` only. |
| [`paper/Kernel-Checked-Green-Problem-19-2026-11-27-v2.pdf`](paper/Kernel-Checked-Green-Problem-19-2026-11-27-v2.pdf) | 10 pages | `f0e681faa049334193924fe166ba5b7c1edf1e8d4e54285b9deaa61703f6f3a5` | Note: statement, proof outline, verification receipt, scope and limits. |
| [`receipts/green19/`](receipts/green19/) | | | Recompile logs with axiom output, static token scan, and the diff from the audited files. |

**What is proved.** For every real `c`, `c` is a valid exponent in Green's Problem 19 if and only if `c ≥ 4`, so the infimum `C` equals `4` (and hence `3.13 ≤ C ≤ 4`, the upstream `.lower` and `.upper`). The mathematics is due to M. Mandache (*A variant of the corners theorem*, `arXiv:1804.03972`) and to J. Fox, A. Sah, M. Sawhney, D. Stoner and Y. Zhao (*Triforce and corners*, `arXiv:1903.04863`). This repository adds only the Lean 4 formalization.

**Prior and related formal work.** In `open-math-agents`, PR #3878 proves a reduction `H1 → H2 → green_19` and PR #4879 proves `H2`; we found no public proof of `H1` or of `green_19` itself. As far as we could determine from public repositories on November 27, 2026, this is the first complete Lean 4 proof of `Green19.green_19`. Searches are not exhaustive; this is a statement about what we found, not a claim of priority.

**Provenance.** The Lean files were written by AI agents and have not been read line by line by a human. Two independent AI audits checked them (clean compilation, axioms, statement fidelity, paper-to-Lean correspondence); the text of the note is AI-assisted. Nothing here has been submitted to or reviewed by the `formal-conjectures` or `open-math-agents` maintainers.

**Receipt.** Lean `4.33.1`, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, `formal-conjectures` `9097e2f90e66d2f6244209cb1c07f7120d17ec53`. Audited on 2026-11-27 (08:05 to 08:30 AM ET): both files compile with exit code 0 and no diagnostics under `-D autoImplicit=false -D relaxedAutoImplicit=false`; all declarations depend only on `propext`, `Classical.choice`, `Quot.sound`; `leanchecker` replays both modules; no `sorry`, `admit`, `native_decide`, `ofReduceBool`, `set_option` or custom axiom. The published files differ from the audited ones only in three documentation comments per file (they no longer call the formalization a "resolution"); both were recompiled after that change on 2026-11-27 (finished 1:33 PM ET) with the same results (`receipts/green19/`).

```bash
# from a formal-conjectures checkout at 9097e2f with its pinned Mathlib
lake build FormalConjectures.GreensOpenProblems.«19»
lake env lean -D autoImplicit=false -D relaxedAutoImplicit=false proofs/Green19.green_19.lean
lake env lean -D autoImplicit=false -D relaxedAutoImplicit=false proofs/Green19.green_19.standalone.lean   # needs Mathlib only
```

---

## Ben Green's Open Problem 95: Zakharov's theorem on sums of two palindromes (release `v1.2.0-green95`)

**Paper:** [`paper/Lean4-Formalization-Zakharov-Sums-of-Two-Palindromes-2026-11-27-v2.pdf`](paper/Lean4-Formalization-Zakharov-Sums-of-Two-Palindromes-2026-11-27-v2.pdf). *A Lean 4 Formalization of Zakharov's Theorem on Sums of Two Palindromes (Ben Green's Open Problem 95)*, Ronak Patel (Avon Labs), November 27, 2026.

| File | Lines | SHA-256 | Role |
|---|---:|---|---|
| [`proofs/Green95.green_95.lean`](proofs/Green95.green_95.lean) | 2,240 | `12f69a63ecbe3d160efe69d13c6682458c44654797d0cdb099bf5fee300be394` | Imports `FormalConjectures.GreensOpenProblems.«95»`; `bridge_green_95` and `bridge_zakharov` have types `type_of% @Green95.green_95` and `type_of% @Green95.green_95.variants.zakharov`. Contains the complete development. |
| [`paper/Lean4-Formalization-Zakharov-Sums-of-Two-Palindromes-2026-11-27-v2.pdf`](paper/Lean4-Formalization-Zakharov-Sums-of-Two-Palindromes-2026-11-27-v2.pdf) | 13 pages | `18172e0a814b34a1f27d425b7c990783adc2a0d8184f5f611714ca1c9cfd5239` | Note: statements, proof architecture, verification receipt, scope. |
| [`receipts/green95/`](receipts/green95/) | | | Recompile output, static scan, assembly script and doc-comment diff. |

**What is proved.** For every base `g ≥ 2`, the number of `n < X` that are sums of two base-`g` palindromes is at most `X / (log X)^(1/10)` for all large `X`; hence these sums have natural density 0, a negative answer to Green's Problem 95. The mathematics is D. Zakharov's (*Most integers are not a sum of two palindromes*, Math. Proc. Cambridge Philos. Soc. 177 (2024), `arXiv:2402.10808`). This repository adds only the Lean 4 formalization.

**Prior formal work.** In `open-math-agents`, PRs #3689 (`green_95.variants.zakharov`) and #3699 (`green_95`) by another contributor, opened at 1:57 and 1:59 AM ET and merged at 2:01 and 2:04 AM ET on November 27, 2026, prove both targets. This development was produced separately but is published later, so it is not the first public Lean proof of either target. Upstream `formal-conjectures` still has both statements as `sorry` with no `formal_proof` link (checked November 27, 2026).

**Provenance.** The Lean file was written by AI agents and has not been read line by line by a human; it was audited by AI agents (clean compile, axioms, statement fidelity). The note is AI-assisted. Nothing has been submitted to `formal-conjectures`.

**Receipt.** Lean `4.33.1`, Mathlib `0df444a3`, `formal-conjectures` `9097e2f9`. Recompiled as published on 2026-11-27 (finished 1:34 PM ET): exit 0, no errors (style-linter warnings only), all exported and bridge theorems depend only on `propext`, `Classical.choice`, `Quot.sound`; no `sorry`, `admit` or `native_decide` (`receipts/green95/`).

```bash
# from a formal-conjectures checkout at 9097e2f with its pinned Mathlib
lake build FormalConjectures.GreensOpenProblems.«95»
lake env lean -D autoImplicit=false -D relaxedAutoImplicit=false proofs/Green95.green_95.lean
```

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
