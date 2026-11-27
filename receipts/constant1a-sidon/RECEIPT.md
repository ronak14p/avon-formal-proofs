# Receipt: Tao's Sidon autocorrelation constant C1a ≥ 1.2976 (files published unchanged from the audit)

- `proofs/Constant1a.c1a_lower_bound.lean` (sha256 `550e18bf8623877c2b7047934382aa62614f8c5895481c817b90450810aacdc6`, 3,951 lines, Mathlib only).
- `proofs/Constant1a.c1a_lower_bound.bridge.lean` (sha256 `175b731435260b00e96b4f0b20561095971cb11f5976d1988659a187eb67f2a0`): written by the audit. It imports `FormalConjectures.OptimizationConstants.«1a»` and the development compiled as a module named `Constant1aLocal`, and states its results with the upstream constant `Constant1a.C1a` (`bridge_C1a_def_eq : Constant1a.C1a = Constant1aProof.C1a := rfl`; `bridge_c1a_lower_bound : type_of% @Constant1a.c1a_lower_bound`).
- Toolchain: Lean `4.33.1`, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, `formal-conjectures` `9097e2f90e66d2f6244209cb1c07f7120d17ec53`.
- Clean recompile of the development, Nov 27, 2026, 7:43–7:44 AM ET: exit 0, no error, no `sorry` warning (`local.log.txt`). `leanchecker` kernel replay of the module: exit 0 (`leanchecker.log.txt`). Bridge: exit 0; all bridge theorems depend only on `propext`, `Classical.choice`, `Quot.sound` (`bridge.log.txt`). Enumeration of all 633 constants of the module: no non-standard axiom (`audit.log.txt`, metaprogram `Audit.lean.txt`).
- Static scan with comments and strings stripped: 0 `sorry`, `admit`, `native_decide`, `ofReduceBool`, `implemented_by`, `extern`, `unsafe`, `axiom`, `opaque`; one `set_option maxRecDepth 4096` (`strip_scan.txt`).
- Independent exact-rational re-check of the SOS certificate data parsed from the Lean file (`recheck_certificate.txt`): Gram matrices PSD, constant `4055172655215574821001279/3125000000000000000000000 = 1.29765…`.
- Not the best known bound: a Zenodo preprint (Tomar) claims C1a ≥ 1.337, and open-math-agents PR #3757 proves 1.286; see the note.
- Checks run by AI agents; no human has reviewed the Lean source.
