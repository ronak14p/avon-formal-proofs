/-
Statement-fidelity bridge for the Avon Labs development `Constant1a.lean` (delivered unchanged; compiled
here as module `Constant1aLocal`, namespace `Constant1aProof`).  This file imports the *upstream* module
`FormalConjectures.OptimizationConstants.«1a»` (google-deepmind/formal-conjectures @ 9097e2f9) and derives,
from the local development, theorems stated with the UPSTREAM constant `Constant1a.C1a`.
Written by the auditor (Claude Sonnet 5.5); it replaces the bridge theorems that VERIFY.md lists but that
are absent from the delivered file.
-/
import FormalConjectures.OptimizationConstants.«1a»
import Constant1aLocal

open MeasureTheory Set

/-! ### 1. Definitional agreement (the decisive check) -/

theorem bridge_C1a_def_eq : Constant1a.C1a = Constant1aProof.C1a := rfl

/-- The same, with the outer set spelled out (the exact set of the upstream definition body). -/
theorem bridge_set_eq :
    {C : ℝ | ∀ ⦃f : ℝ → ℝ⦄, 0 ≤ f → MemLp f 2 →
      C * (∫ x in (- 1 / 4)..(1 / 4), f x) ^ 2
        ≤ sSup {∫ x, f (t - x) * f x | t ∈ Icc (- 1 / 2 : ℝ) (1 / 2)}}
    = {C : ℝ | ∀ ⦃f : ℝ → ℝ⦄, 0 ≤ f → MemLp f 2 →
      C * (∫ x in (- 1 / 4)..(1 / 4), f x) ^ 2
        ≤ sSup {∫ x, f (t - x) * f x | t ∈ Icc (- 1 / 2 : ℝ) (1 / 2)}} := rfl

/-! ### 2. Bridge theorems: types are exactly those of the upstream statements -/

theorem bridge_c1a_lower_bound : type_of% @Constant1a.c1a_lower_bound :=
  @Constant1aProof.c1a_lower_bound

/-- The headline certificate, stated with the UPSTREAM constant. -/
theorem bridge_c1a_ge_cert80 :
    (4055172655215574821001279 / 3125000000000000000000000 : ℝ) ≤ Constant1a.C1a :=
  Constant1aProof.c1a_ge_cert80_exact

theorem bridge_c1a_ge_12976 : (12976 / 10000 : ℝ) ≤ Constant1a.C1a :=
  Constant1aProof.c1a_ge_12976

/-- `1.292 < 1.2976 <= C1a`, i.e. the *existential* content of the open `mem_Ioc_c1a`. -/
theorem bridge_exists_mem_Ioc : ∃ a : ℝ, a ∈ Set.Ioc 1.292 Constant1a.C1a :=
  ⟨12976 / 10000, Constant1aProof.mem_Ioc_c1a⟩

theorem bridge_c1a_le_1521 : Constant1a.C1a ≤ 1521 / 1000 :=
  Constant1aProof.c1a_le_1521

theorem bridge_c1a_lt_pi_div_two : Constant1a.C1a < Real.pi / 2 :=
  Constant1aProof.c1a_lt_pi_div_two

/-! ### 3. Junk-value guards, stated with the upstream definition -/

theorem bridge_set_bddAbove :
    BddAbove {C : ℝ | ∀ ⦃f : ℝ → ℝ⦄, 0 ≤ f → MemLp f 2 →
      C * (∫ x in (- 1 / 4)..(1 / 4), f x) ^ 2
        ≤ sSup {∫ x, f (t - x) * f x | t ∈ Icc (- 1 / 2 : ℝ) (1 / 2)}} :=
  Constant1aProof.c1a_set_bddAbove

theorem bridge_one_le : 1 ≤ Constant1a.C1a := Constant1aProof.one_le_c1a
theorem bridge_le_two : Constant1a.C1a ≤ 2 := Constant1aProof.c1a_le_two

theorem bridge_inner_bddAbove {f : ℝ → ℝ} (hf : MemLp f 2) :
    BddAbove {∫ x, f (t - x) * f x | t ∈ Icc (- 1 / 2 : ℝ) (1 / 2)} :=
  Constant1aProof.autoconvValues_bddAbove hf

/-! ### 4. The statements as elaborated -/
set_option pp.numericTypes true in
#check @bridge_c1a_lower_bound
#check @Constant1a.c1a_lower_bound
#check @bridge_c1a_ge_cert80
#check @bridge_exists_mem_Ioc
#check @bridge_c1a_le_1521

open Lean Meta Elab in
#eval show MetaM Unit from do
  let a ← getConstInfo ``Constant1a.C1a
  let b ← getConstInfo ``Constant1aProof.C1a
  let va := a.value!; let vb := b.value!
  IO.println s!"C1a bodies: beq (eqv) = {va == vb}; strict Expr.equal = {Expr.equal va vb}; types eqv = {a.type == b.type}"
  IO.println s!"upstream body:\n{← ppExpr va}\nlocal body:\n{← ppExpr vb}"

#print axioms bridge_C1a_def_eq
#print axioms bridge_c1a_lower_bound
#print axioms bridge_c1a_ge_cert80
#print axioms bridge_c1a_ge_12976
#print axioms bridge_exists_mem_Ioc
#print axioms bridge_c1a_le_1521
#print axioms bridge_c1a_lt_pi_div_two
#print axioms bridge_set_bddAbove
#print axioms bridge_one_le
#print axioms bridge_le_two
#print axioms bridge_inner_bddAbove
