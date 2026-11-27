# Avon Labs — Machine-Verified Lean 4 Formalizations

**Author:** Ronak Patel, Avon Labs (`@ronak14p`)  
**Technical Report (PDF):** [`paper/Avon-Labs-Lean4-Formalizations-2026-11-27.pdf`](paper/Avon-Labs-Lean4-Formalizations-2026-11-27.pdf)  
**License:** Apache-2.0 (see [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE))  
**Toolchain:** Lean 4 (`v4.33.1`) · Zero `sorry` · Zero `admit` · Zero `native_decide` / `ofReduceBool` · Standard axioms only (`propext`, `Classical.choice`, `Quot.sound`)

---

> **v2 (Tier 3 cohort):** a second release adds 23 AI-produced, AI-audited Lean 4 papers with audited sources and receipts; see [v2 Cohort](#v2-cohort-tier-3) below. Most entries re-prove known results; each row states its prior work. Not refereed.

## Overview

This repository publishes **9 standalone, kernel-verified Lean 4 formalizations totaling 11,677 lines** across extremal combinatorics, finite group theory, graph theory, and irrationality theory, verified and timestamped on **November 27, 2026 (04:08–05:10 UTC)** against statement definitions from Google DeepMind's Apache-2.0 [`formal-conjectures`](https://github.com/google-deepmind/formal-conjectures) benchmark.

Full technical proof summaries, methodology notes, immutable GitHub submission timestamps, and SHA-256 digests are compiled in [`paper/Avon-Labs-Lean4-Formalizations-2026-11-27.pdf`](paper/Avon-Labs-Lean4-Formalizations-2026-11-27.pdf).

> **Attribution:** Our contribution is the machine-verified Lean 4 formalization and kernel-checkable certificate design. All underlying mathematical theorems, bounds, and counterexample constructions are credited to their original authors below and inside each file.

---

## Verified Standalone Proofs (`proofs/`, 9 files · 11,677 lines)

| Benchmark Declaration | Domain | Lines | Submitted (2026-11-27 UTC) | Upstream Status | Mathematical Source Credited |
|---|---|---:|---|---|---|
| [`Constant6a.c6a_lower_bound_improved.lean`](proofs/Constant6a.c6a_lower_bound_improved.lean) | Union-Closed | 1,549 | `05:01:59Z` | PR `#3208` (closed in favour of `#2871`) | Liu (`arXiv:2306.08824`) + Costa & Sadhu (`arXiv:2610.02295`), proving `0.382725 ≤ C6a` |
| [`UnionClosed.union_closed.variants.yu.lean`](proofs/UnionClosed.union_closed.variants.yu.lean) | Union-Closed | 1,612 | `05:09:53Z` | PR `#3250` (**Merged**) | Yu (*Entropy* 2023) arbitrary ground type via Liu + Costa & Sadhu coupling |
| [`Constant6a.c6a_lower_bound.lean`](proofs/Constant6a.c6a_lower_bound.lean) | Union-Closed | 1,547 | `04:49:49Z` | PR `#3191` (closed: superseded upstream by `#3085`) | Liu (`arXiv:2306.08824`, `0.38271 ≤ C6a`) |
| [`Constant6a.c6a_lower_bound_intermediate.lean`](proofs/Constant6a.c6a_lower_bound_intermediate.lean) | Union-Closed | 2,648 | `04:34:20Z` | PR `#3049` (**Merged**) | Sawin (`2211.11504`), Yu (`2212.00658`), Cambie (`2212.12500`, `0.38234 ≤ C6a`) |
| [`Constant6a.c6a_lower_bound_first.lean`](proofs/Constant6a.c6a_lower_bound_first.lean) | Union-Closed | 1,251 | `04:19:06Z` | PR `#2846` (**Merged**) | Gilmer (2022) / Chase & Lovett (`2211.11689`)* |
| [`Mathoverflow508539.mathoverflow_508539.lean`](proofs/Mathoverflow508539.mathoverflow_508539.lean) | Hypercube | 451 | `04:26:37Z` | PR `#2945` (**Merged**) | MathOverflow 508539 (`E · V ≥ N²/4` via fibre induction) |
| [`Erdos267.erdos_267.variants.fibonacci_inverse_sum.lean`](proofs/Erdos267.erdos_267.variants.fibonacci_inverse_sum.lean) | Number Theory | 1,180 | `05:00:07Z` | PR `#3207` (**Merged**) | André-Jeannin (1989), irrationality of `∑ 1/F_n` via Fibonomial Padé forms |
| [`Kourovka.19.25.kourovka_19_25.lean`](proofs/Kourovka.19.25.kourovka_19_25.lean) | Group Theory | 1,030 | `05:05:37Z` | PR `#3214` (**Merged**) | Explicit order-6,048 witness `PSU(3,3)` vs `C_6 × S_4 × (C_7 ⋊ C_6)` (`arXiv:2607.17477`) |
| [`WrittenOnTheWallII.GraphConjecture72.conjecture72.lean`](proofs/WrittenOnTheWallII.GraphConjecture72.conjecture72.lean) | Graph Theory | 409 | `04:08:43Z` | PR `#2740` (CI green · Lean checker accepted · `needs-human-review`) | Gebendorfer's 31-vertex graph `G(2,24)` (DeLaViña WOWII disproof) |

*\*`Constant6a.c6a_lower_bound_first.lean` adapts the scalar entropy inequality from Ho Boon Suan & Aristotle (Harmonic) under the MIT License (full notice retained in-file and in [`NOTICE`](NOTICE)). That inequality generalizes R. B. Boppana's binary-entropy inequality `h(x²) ≥ φ·x·h(x)` (R. B. Boppana, [*A Useful Inequality for the Binary Entropy Function*](https://arxiv.org/abs/2301.09664), `arXiv:2301.09664`; Ho Boon Suan, *A generalization of Boppana's entropy inequality*, `arXiv:2601.19327`); credit for the inequality belongs to Boppana, Ho and Aristotle.*

---

### Upstream Status Snapshot (2026-11-27, 2:12 PM ET / 19:12 UTC)

Submitted to the public [`open-math-agents`](https://github.com/GuillaumeBAUD-coder/open-math-agents) Lean 4 checker:

- **Merged (6):** `#2846` `Constant6a.c6a_lower_bound_first` · `#2945` `Mathoverflow508539.mathoverflow_508539` · `#3049` `Constant6a.c6a_lower_bound_intermediate` · `#3207` `erdos_267` Fibonacci variant · `#3214` `kourovka_19_25` · `#3250` `union_closed.variants.yu`. Each was accepted by the repository's Lean checker with axioms limited to `propext`, `Classical.choice`, `Quot.sound`.
- **Open (1):** `#2740` `GraphConjecture72` (accepted by the Lean checker; awaiting maintainer statement review, as is standard for open-problem disproofs).
- **Closed as superseded (1):** `#3191` `Constant6a.c6a_lower_bound`. Upstream merged a separate proof (`#3085`) first. Our independent formalization is kept here unchanged.
- **Closed in favour of an earlier PR (2026-11-27, 18:58 UTC):** `#3208` `Constant6a.c6a_lower_bound_improved`. PR `#2871` (another contributor, opened 41 minutes earlier, proving `0.38273 ≤ C6a`) addresses the same declaration and was merged. Our formalization is kept here unchanged.

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

## Tier 2 (release `v1.3.0-tier2`): MathOverflow 508539, Kourovka 20.75/20.76, Sidon autocorrelation constant C1a

| Paper | Lean files | What is proved | Prior work |
|---|---|---|---|
| [*A Kernel-Checked Elementary Proof of the Half-Size Edge-Vertex Boundary Inequality on the Hamming Cube (MathOverflow 508539)*](paper/Kernel-Checked-Hypercube-Edge-Vertex-Inequality-MO508539-2026-11-27.pdf) (7 pages; sha256 `fdb57ae22eccf6421316528fa1aa781a4ad0e4a6367ff2797bdd780b84e6dd82`) | [`proofs/Mathoverflow508539.mathoverflow_508539.lean`](proofs/Mathoverflow508539.mathoverflow_508539.lean) (unchanged since v1.0.0) | For `A ⊆ {0,1}^n` with `|A| = 2^(n-1)`: `|∂_E A| · |∂_V A| ≥ 4^(n-1)`, the formal-conjectures statement `Mathoverflow508539.mathoverflow_508539`, by an elementary fibre induction. | This file was merged in open-math-agents PR #2945; the note discusses the literature on the inequality. |
| [*A Lean 4 Verification of a 2^141 Counterexample to Kourovka Notebook Problems 20.75 and 20.76*](paper/Lean4-Kourovka-20-75-20-76-2026-11-27-v3.pdf) (11 pages, version 3; sha256 `2e1d7144acfa0d943a142e4dbed9892aef521d55e156676f8e5590d32ced2266`) | [`proofs/Kourovka.20_76.kourovka_20_76.lean`](proofs/Kourovka.20_76.kourovka_20_76.lean) (Mathlib only), [`proofs/Kourovka.20_76.bridge.lean`](proofs/Kourovka.20_76.bridge.lean) (imports `FormalConjectures.Kourovka.«20_76»`; `upstream_type_match : type_of% @Kourovka.«20.76».kourovka_20_76`) | A 2-group of order `2^141` with all abelian normal subgroups of order at most `2^80` but an abelian subgroup of order `2^81`, refuting Pyber's Problems 20.75 and 20.76; quadratic upper bound; no linear exponent bound. | Muliarchyk resolved both problems (order `2^145`); `2^141` is a re-parametrization of his construction. A Lean proof of `kourovka_20_76` was merged earlier in open-math-agents PR #2860 (another contributor). |
| [*A Kernel-Checked Lean 4 Lower Bound C1a ≥ 1.2976 for Tao's Sidon Autocorrelation Constant*](paper/Kernel-Checked-Sidon-Autocorrelation-C1a-2026-11-27.pdf) (8 pages; sha256 `d483ee47283a326a4ef2f3cb1544ccf77417cb971d0b433a85098d7564e38dc4`) | [`proofs/Constant1a.c1a_lower_bound.lean`](proofs/Constant1a.c1a_lower_bound.lean) (Mathlib only), [`proofs/Constant1a.c1a_lower_bound.bridge.lean`](proofs/Constant1a.c1a_lower_bound.bridge.lean) (imports the upstream module and the development compiled as module `Constant1aLocal`) | `C1a ≥ 4055172655215574821001279/3125000000000000000000000 > 1.2976` via an exactly checked sum-of-squares certificate, for the formal-conjectures constant `Constant1a.C1a`; also `C1a ≤ 1.521 < π/2`. | Not a record: a preprint (Tomar) claims `C1a ≥ 1.337`; open-math-agents PR #3757 proves `1.286`. |

**Provenance.** All Lean files were written by AI agents and audited by AI agents (clean compile, axioms, statement fidelity, paper-to-Lean correspondence); the notes are AI-assisted; no human has reviewed them line by line. All declarations depend only on `propext`, `Classical.choice`, `Quot.sound`. Receipts: [`receipts/mo-508539/`](receipts/mo-508539/), [`receipts/kourovka-20-76/`](receipts/kourovka-20-76/), [`receipts/constant1a-sidon/`](receipts/constant1a-sidon/). The Kourovka files differ from the audited ones only in documentation comments and were recompiled on 2026-11-27 (finished 1:40 PM ET); the other files are byte-identical to the audited ones. Nothing here has been submitted to `formal-conjectures`.

---

## v2 Cohort (Tier 3)

**23 papers** (PDF, audited Lean sources, `AUDIT.md` and `VERIFICATION.md` receipts where they exist, `SHA256SUMS.txt`) are provided as release assets (release [`v2.0.0-tier3`](https://github.com/ronak14p/avon-formal-proofs/releases/tag/v2.0.0-tier3), asset `release-v2.tar.gz`); the proofs are not copied into `proofs/`. All were produced and audited by AI agents; none is refereed and no human mathematician has reviewed them. This is the Tier 3 set: second proofs, re-formalizations of known results, or duplicates of already merged proofs, as stated per row.

| Slug | Verdict | Upstream declaration | Prior work / novelty |
|---|---|---|---|
| `kourovka-19-25` | PASS WITH CAVEATS | `Kourovka.«19.25».kourovka_19_25` | Witness and a prior Lean formalization in arXiv:2607.17477 (Jul 20 2026); our proof merged as OMA #3214 |
| `erdos-267-fibonacci` | PASS WITH CAVEATS | `Erdos267.erdos_267.variants.fibonacci_inverse_sum` | André-Jeannin 1989; our proof is the merged OMA #3207 (no earlier Lean proof found; search limited) |
| `union-closed` | PASS WITH CAVEATS | `Constant6a.c6a_lower_bound_first (+4)` | Costa-Sadhu 0.38288... > ours; Liu 0.38271 conditional; OMA #2871 same parameters; #3085 superseded our #3191 |
| `kaplansky-char0` | PASS WITH CAVEATS | `Kaplansky.direct_finiteness_conjecture.variants.char_zero` | Duplicate: OMA #2419 (kintonc, merged Nov 26 11:28 PM ET) proves the same declaration |
| `green26-additive-basis` | PASS WITH CAVEATS | `Green26.green_26 (+1)` | Duplicate: OMA #3664 (yu25) and #3700 (green_26), merged about 1 hour earlier |
| `tx-graffiti-1` | PASS WITH CAVEATS | `Arxiv.«2507.17780».tx_graffiti_conjecture_1` | Duplicate: OMA #2789 (merged 12:21 AM ET) and Gupta's Lean repo (since Jun 30 2026) |
| `furstenberg-x2x3` | PASS WITH CAVEATS | `Bugeaud06.furstenberg_two_three` | Duplicate: OMA #3435 (merged 1:23 AM ET) proves the same declaration |
| `koksma` | PASS WITH CAVEATS | `Bugeaud61.problem_10_61.variants.almost_every` | Duplicate: OMA #2437 (RichieRichest, merged Nov 26 11:30 PM ET) |
| `subgroup-counts` | PASS WITH CAVEATS | `Arxiv.«2604.08040».nilpotent_of_cyc_lt (+3)` | Duplicate: formal-conjectures #6621 (Kitamura, Conj 5.5); OMA #356, #3272, #3335 merged |
| `green31-sidon` | PASS WITH CAVEATS | `Green31.green_31.variants.upper_hz26 (+8)` | Not new: Madeiros 0.943244, Akwei 0.9428095, Carter-O'Bryant-Tao 0.94304; OMA #3819 formalized HZ earlier |
| `erdos-fuchs` | PASS WITH CAVEATS | `Erdos763.erdos_763.variants.erdos_fuchs (+1)` | Duplicate: OMA #3355 (marcusbuffett, merged 1:17 AM ET) |
| `vaughan` | PASS WITH CAVEATS | `Erdos764.erdos_764.variants.vaughan (+1)` | Duplicate for k=3: OMA #3552 (merged 1:29 AM ET); upstream erdos_764 already has a formal_proof link |
| `constant7a-pi` | PASS WITH CAVEATS | `Constant7a.irrationalityExponent_ratCast (+5)` | Very low novelty: surpassed 1974; OpenAI claims C7a = 2; OMA #3351 c7a_le_42 |
| `wowii-372` | PASS WITH CAVEATS | `WrittenOnTheWallII.GraphConjecture372.conjecture372 (+2)` | Duplicate: OMA #435/#442/#454 (merged 5:44 AM ET); formal-conjectures #8305 pending; DeLaViña 2009 |
| `erdos297` | PASS WITH CAVEATS | `Erdos297.erdos_297.variants.steinerberger (+3)` | Known: Lucia 2017 (MO 281124) gives the same ~2^{0.911n}; OMA #5375 proves erdos_297 in full; #246 steinerberger |
| `erdos792` | PASS WITH CAVEATS | `Erdos792.erdos_792.variants.bourgain (+5)` | Duplicate: OMA #542 (alon_kleitman) and #4072 (bourgain), both in much shorter files |
| `pfister` | PASS WITH CAVEATS | `PfisterPythagorasNumber.isLeast_pythagorasBounds_real (+5)` | Duplicate for upper_bound and cassels: upstream already has complete Lean proofs (PR 6834, formal_proof links) |
| `green44` | PASS WITH CAVEATS | `Green44.green_44 (disproved) (+2)` | Known: Price + GPT-5.4 Pro (erdosproblems.com/1202); plby Erdos1202.lean; OMA #1457; formal-conjectures #8125 |
| `green43` | PASS WITH CAVEATS | `Green43.green_43.variants.general_exponent_lt_half (+3)` | Duplicate: OMA #791 (philipsaint, Nov 26 7:01 PM ET); Green calls alpha<1/2 straightforward; Alon-Peres 1992 |
| `egh` | PASS WITH CAVEATS | `EisenbudGreenHarris.eisenbud_green_harris.variants.macaulay (+1)` | Classical (Macaulay 1927, Clements-Lindstrom 1969); both upstream variants already proved in open-math-agents #3560 and #3659 (merged Nov 27 1:29/1:52 AM ET) |
| `green32` | PASS WITH CAVEATS | `Green32.green_32.variants.sh20_general (+3)` | All four declarations already proved: OMA #239, #1993, #2011; dirichlet_regime already linked to an external Lean proof on formal-conjectures (PR #6954) |
| `finite-group-scheme` | PASS WITH CAVEATS | `FiniteLocallyFreeGroupSchemeExponent.killed_by_rank.variants.field (+2)` | All three variants already merged: OMA #3233 (adapted from the Tau Ceti library), #4358, #4381; external claim for the open optimal_exponent in formal-conjectures PR #8097 (unverified) |
| `cho-kim-kim-oum` | PASS WITH CAVEATS | `Arxiv.2107.00295.independentDominationEven (+1)` | Both parity cases already merged: OMA #1488 (even) and #3686 (odd), far shorter; subcubic bound in #1434 and #3686; Brooks's theorem in three public Lean repos |

Archive: `release-v2.tar.gz`, 4,797,704 bytes, SHA-256 `96625b261d2fe3042b73f56bdf5214d492857c59afe76437987c284f426603ee`; it contains its own `SHA256SUMS.txt` (146 files; run `sha256sum -c SHA256SUMS.txt` inside the extracted folder). In nine Lean files of five papers (constant7a-pi, furstenberg-x2x3, green26-additive-basis, green31-sidon, wowii-372) one internal comment label was removed after the audit; each was recompiled with the same result, and the papers cite the audited hashes (see `receipts/<slug>/comment-edit-receipt.md` in the archive).

Published separately (not part of the v2 archive): `green19` ([`v1.1.0-green19`](https://github.com/ronak14p/avon-formal-proofs/releases/tag/v1.1.0-green19)); `green95-palindromes` ([`v1.2.0-green95`](https://github.com/ronak14p/avon-formal-proofs/releases/tag/v1.2.0-green95)); `mo-508539` ([`v1.3.0-tier2`](https://github.com/ronak14p/avon-formal-proofs/releases/tag/v1.3.0-tier2)); `kourovka-20-76` ([`v1.3.0-tier2`](https://github.com/ronak14p/avon-formal-proofs/releases/tag/v1.3.0-tier2)); `constant1a-sidon` ([`v1.3.0-tier2`](https://github.com/ronak14p/avon-formal-proofs/releases/tag/v1.3.0-tier2)).

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
