# Receipt: MathOverflow 508539 (`proofs/Mathoverflow508539.mathoverflow_508539.lean`, published in v1.0.0, unchanged)

- File sha256 `24b7b8418f83dd37671112d564e21d95b8a822ea2be18f99482b9967cb0da82d` (451 lines); identical to the file merged in open-math-agents PR #2945 (merge commit `89b82b479c4c61365931ea884885c5c525932846`, Nov 27, 2026, 12:26 AM ET).
- Toolchain: Lean `4.33.1`, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, `formal-conjectures` `9097e2f90e66d2f6244209cb1c07f7120d17ec53` (module `FormalConjectures.Mathoverflow.«508539»` built).
- Independent recompile on Nov 27, 2026, 2:19 AM ET of a copy with `#print axioms OMA.solution` and `#check @Mathoverflow508539.mathoverflow_508539` appended: exit 0, no errors, no `sorry` warning; 3 style-linter warnings (`recompile_output.txt`). `OMA.solution` depends only on `propext`, `Classical.choice`, `Quot.sound`; it is stated as `type_of% @Mathoverflow508539.mathoverflow_508539`.
- Source grep: the words `sorry` and `native_decide` occur once each, in the header comment ("No sorry, no axiom, no native_decide"); no code occurrence of `sorry`, `admit`, `native_decide`, `ofReduceBool`, `implemented_by`, `extern`, `axiom`, `unsafe`, `opaque`, `set_option`.
- Not part of the proof: `sanity_bruteforce.py` checks the induction invariant and `E·V ≥ 4^(n-1)` exhaustively for n ≤ 4 (0 violations; `sanity_bruteforce.out`).
- Checks run by AI agents; no human has reviewed the Lean source.
