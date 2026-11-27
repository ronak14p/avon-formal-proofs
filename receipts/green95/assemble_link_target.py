#!/usr/bin/env python3
"""Assemble the single self-contained link-target proof file for formal-conjectures
GreensOpenProblems/95 from the AUDITED inputs (read-only):
  bridge/Green95Local.lean  (sha 1277c579...; Green95.lean 851867d5... with ONLY a mechanical renaming)
  bridge/Bridge.lean        (sha 7572ecd5...)
Nothing inside the two bodies is edited; only a new header, two set_option lines, and
the concatenation are added.  Usage: assemble_link_target.py <audit_bridge_dir> <out.lean>"""
import sys, hashlib, pathlib
d = pathlib.Path(sys.argv[1])
loc = (d / 'Green95Local.lean').read_text(encoding='utf-8')
br = (d / 'Bridge.lean').read_text(encoding='utf-8')
assert hashlib.sha256(loc.encode()).hexdigest().startswith('1277c579')
assert hashlib.sha256(br.encode()).hexdigest().startswith('7572ecd5')
ll = loc.split('\n')
assert ll[15] == 'import Mathlib' and ll[17] == 'open Filter Topology', (ll[15], ll[17])
body_loc = '\n'.join(ll[17:])          # from `open Filter Topology` to the end
bl = br.split('\n')
i = bl.index('namespace GreenBridge')
body_br = '\n'.join(bl[i:])
header = '''import FormalConjectures.GreensOpenProblems.«95»
import Mathlib

/-
Copyright 2026 Ronak Patel (Avon Labs).
Released under Apache 2.0 license as described in the file LICENSE.

Link target for the `formal_proof` attributes of
`Green95.green_95` and `Green95.green_95.variants.zakharov`
in google-deepmind/formal-conjectures (`FormalConjectures/GreensOpenProblems/95.lean`).

WHAT THIS FILE PROVES.  The last section (`bridge_green_95`, `bridge_zakharov`) proves
theorems whose types are, by `type_of%`, EXACTLY the types of the upstream declarations
`Green95.green_95` and `Green95.green_95.variants.zakharov`; there is no retyping by hand.
They are derived from a complete development of Zakharov's quantitative sumset bound for
base-g palindromes, which lives in the non-clashing namespaces `Green95Local` and
`LocalDensity` and re-declares the definitions (for standalone checking); the seven
definition-agreement lemmas in `GreenBridge` are all `rfl`.

References:
  - D. Zakharov, "Most integers are not a sum of two palindromes",
    Math. Proc. Cambridge Philos. Soc. 177 (2024), 363-366 (arXiv:2402.10808).
  - J. Cilleruelo, F. Luca, and L. Baxter, "Every positive integer is a sum of
    three palindromes", Math. Comp. 87 (2018), 3023-3055 (arXiv:1602.06208).
  - B. Green, "100 Open Problems", Problem 95 (2024).

PROVENANCE AND DISCLOSURE.  The development was produced by AI agents operated by Avon Labs
(a Gemini 4 "Carbon" lead with "Hydrogen" workers) and machine-checked by Lean; the mathematics
is Zakharov's, and the only increment over [Za24, Theorem 1] is the statement for all large
natural X.  An AI audit (Claude Opus 5.5) recompiled the unmodified development (Green95.lean,
SHA-256 851867d5eec5c05a2aff7286e489a3fcf57eb482fae961a61cbe4725db7ca0ab, 2,168 lines) and
checked the renaming; no human has reviewed the proof text.  Sources assembled by
`assemble_link_target.py` from `Green95Local.lean` (SHA-256 1277c579...0648d) and `Bridge.lean`
(SHA-256 7572ecd5...5e12d) with no edit to either body.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

'''
out = header + body_loc.rstrip('\n') + '\n\n' + body_br.rstrip('\n') + '\n'
pathlib.Path(sys.argv[2]).write_text(out, encoding='utf-8')
print(hashlib.sha256(out.encode()).hexdigest(), out.count('\n'))
