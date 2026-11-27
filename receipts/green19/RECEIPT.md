# Recompile receipt: Green 19 Lean files as published

- Toolchain: Lean `4.33.1` (`leanprover/lean4:v4.33.1`), Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, `formal-conjectures` `9097e2f90e66d2f6244209cb1c07f7120d17ec53` (module `FormalConjectures.GreensOpenProblems.«19»` prebuilt).
- Command: `lake env lean -D autoImplicit=false -D relaxedAutoImplicit=false <file>` on a copy of each published file with an audit footer appended (the published bytes are an unmodified prefix; footers in `audit_footer_*.lean.txt`).
- `proofs/Green19.green_19.standalone.lean` (sha256 `4032046c1b6f4916311301822d867c44b2a6848f705be94ed26214b03733036d`): exit 0, no errors, no warnings, finished 2026-11-27 13:33:05 ET. Output: `recompile_Check_Green19.txt`.
- `proofs/Green19.green_19.lean` (sha256 `30dfe0c581913817fc3f2feeb25b0cad7d080c5c54a384b4040236a2ebf6f9ee`): exit 0, no errors, no warnings, finished 2026-11-27 13:33:28 ET. Output: `recompile_Check_Bridge.txt`.
- Axioms: every headline theorem and every constant in the transitive closure of all local constants depends only on `propext`, `Classical.choice`, `Quot.sound`. The two `partial ... _unsafe_rec` entries are auxiliaries that Lean generates for two `def`s defined by well-founded recursion; they are not used by any theorem's proof term (the axiom closure contains no `sorryAx`, `ofReduceBool` or `trustCompiler`).
- Statement fidelity: `upstream_green_19`, `upstream_green_19_lower`, `upstream_green_19_upper` have types `Expr`-identical to the upstream `Green19.green_19`, `.lower`, `.upper` (`EXPRCHK` lines), with proof terms the standalone theorems; the definitions `IsCorner`, `S`, `ValidExponent`, `C` agree with upstream.
- Static scan (comments and strings stripped): no `sorry`, `admit`, `native_decide`, `ofReduceBool`, `trustCompiler`, `implemented_by`, `extern`, `unsafe`, `axiom`, `opaque`, `partial`, `set_option` in either file (`static_token_scan.txt`).
- Difference from the audited files: three documentation comments per file, no code (`header-comment-diff.txt`).
- These checks were run by an AI agent. No human has reviewed the Lean source.
