# Recompile receipt: Kourovka 20.75 / 20.76 Lean files as published

- Toolchain: Lean `4.33.1`, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, `formal-conjectures` `9097e2f90e66d2f6244209cb1c07f7120d17ec53` (module `FormalConjectures.Kourovka.«20_76»` built).
- `proofs/Kourovka.20_76.kourovka_20_76.lean` (sha256 `9c10115489490cefaa0a8ce45218d189d36b7fc7201d37e63fbb7c297882b72a`, 2,159 lines, Mathlib only): `lake env lean -D autoImplicit=false -D relaxedAutoImplicit=false`: exit 0, no output (no errors, no warnings), finished Nov 27, 2026, 1:39 PM ET.
- `proofs/Kourovka.20_76.bridge.lean` (sha256 `a0605949877710f1a1175b6fe4ffc7b7ca2eaf4cc3305767984aa9b1df7b614a`): the same development with `import FormalConjectures.Kourovka.«20_76»` prepended and the bridge appended. Exit 0, no errors, one style-linter warning; finished 1:40 PM ET (`recompile_Kourovka.20_76.bridge.txt`).
- `upstream_type_match : type_of% @Kourovka.«20.76».kourovka_20_76` is proved by `Kourovka20_76.kourovka_20_76`; a separate `rfl` checks the two types are equal. All 15 printed declarations depend only on `propext`, `Classical.choice`, `Quot.sound`; the upstream declaration itself shows `sorryAx` because upstream states it with `sorry`.
- Difference from the audited files (sha256 `56d598af…` and `9210c39f…`, cited in the note): documentation comments only (`doc-comment-diff.txt`).
- Checks run by AI agents; no human has reviewed the Lean source.
