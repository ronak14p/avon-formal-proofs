import FormalConjectures.Kourovka.«20_76»
/-
Copyright (c) 2026 Ronak Patel (Avon Labs). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ronak Patel
-/
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Tactic

/-!
# Abelian Subgroups and Abelian Normal Subgroups in Finite `p`-Groups:
# Counterexamples to Kourovka Problems 20.75 and 20.76 (after Muliarchyk), `Θ(k^2)` Asymptotics,
# and a `2^141` Re-parametrization of Muliarchyk's Construction

This standalone Lean 4 file develops both the positive structural bounds and the negative
counterexample theory for Pyber's twin problems in *The Kourovka Notebook* (20th ed., 2022,
p. 154, Problems 20.75 and 20.76):

1. **Class-2 Rigidity (`abelian_card_le_of_commutator_le_center`,
   `pyber_bound_of_nilpotencyClass_le_two`)**: In any finite group `G` with `[G, G] ≤ Z(G)`
   (nilpotency class `≤ 2`), every abelian subgroup `B` embeds in the abelian normal subgroup
   `B ⊔ Z(G)`, forcing `|B| ≤ p ^ k`.
2. **Burnside–Alperin–Roquette Quadratic Upper Bound (`centralizer_eq_self_of_max_normal_abelian`,
   `card_group_le_pow_quadratic`, `abelian_card_le_pow_quadratic`)**: Any maximum-order abelian
   normal subgroup `A` of a finite `p`-group is self-centralizing (`C_G(A) = A`), yielding the
   universal bound `|B| ≤ |G| ≤ p ^ (k * (k + 1) / 2)`.
3. **Bipartite Gaussian-Binomial Non-Isotropy & Class-4 Swap-Semidirect Engine (`exists_good_M`,
   `nilpotencyClass_G76_le_four`, `nilpotencyClass_G76_eq_four`, `exists_counterexample_family`)**:
   Grassmannian-free bipartite double counting over linearly independent `d`-tuples in `𝔽₂ⁿ`
   constructs `G(n, z₀, M) = M(f) ⋊ C₂` of order `2 ^ (2n + 2z₀ + 1)` and exact nilpotency class `4`
   (when `ω M ≠ 0`), bounding all abelian normal subgroups by `2 ^ (2(d - 1) + 2z₀)` while
   exhibiting an elementary abelian subgroup of order `2 ^ (n + 2z₀)`.
4. **`2^141` Counterexample to Both Kourovka Problems (`exists_counterexample_two_pow_141`,
   `exists_counterexample_two_pow_145`, `kourovka_20_76`, `kourovka_20_75`)**: Specializing
   `(n, z₀, d) = (59, 11, 10)` gives a counterexample of order `2 ^ 141` (`k = 40`,
   `|B₁| = 2 ^ 81 > 2 ^ 80`), a re-parametrization of Muliarchyk's `2 ^ 145` construction, refuting both
   Kourovka 20.76 and Kourovka 20.75.
5. **Exact `Θ(k^2)` Extremal Separation (`no_linear_exponent_bound`)**: Refutes any linear exponent
   bound `2 ^ (C * k)` for every `C : ℕ`, matching Burnside's `O(k^2)` bound up to a constant factor.
-/

namespace Kourovka20_76

/- ## Part 1: Positive Structural Bounds (Class-2 Rigidity & Burnside Quadratic Ceiling) -/

section Helpers

open Subgroup

/-- If two subgroups are commutative and one lies in the centralizer of the other, their join is
commutative. -/
private lemma isMulCommutative_sup_of_le_centralizer {G : Type*} [Group G] {H K : Subgroup G}
    (hH : IsMulCommutative H) (hK : IsMulCommutative K)
    (hHK : H ≤ Subgroup.centralizer (K : Set G)) :
    IsMulCommutative ↥(H ⊔ K) := by
  have h1 : H ⊔ K ≤ Subgroup.centralizer (H : Set G) :=
    sup_le (Subgroup.le_centralizer_iff_isMulCommutative.mpr hH)
      (Subgroup.le_centralizer_iff.mp hHK)
  have h2 : H ⊔ K ≤ Subgroup.centralizer (K : Set G) :=
    sup_le hHK (Subgroup.le_centralizer_iff_isMulCommutative.mpr hK)
  have hH' : H ≤ Subgroup.centralizer ((H ⊔ K : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.mp h1
  have hK' : K ≤ Subgroup.centralizer ((H ⊔ K : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.mp h2
  exact Subgroup.le_centralizer_iff_isMulCommutative.mp (sup_le hH' hK')

private lemma isMulCommutative_zpowers {G : Type*} [Group G] (x : G) :
    IsMulCommutative (Subgroup.zpowers x) := by
  refine Subgroup.le_centralizer_iff_isMulCommutative.mp ?_
  rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact (Commute.refl x).zpow_left n

private lemma normal_of_le_center {G : Type*} [Group G] {K : Subgroup G}
    (hK : K ≤ Subgroup.center G) : K.Normal :=
  ⟨fun k hk q => by
    have hk' := Subgroup.mem_center_iff.mp (hK hk) q
    simpa [mul_assoc, hk'] using hk⟩

private lemma map_mk'_ne_bot_of_lt {G : Type*} [Group G] {A C : Subgroup G}
    [A.Normal] (hlt : A < C) :
    C.map (QuotientGroup.mk' A) ≠ ⊥ := by
  obtain ⟨c, hcC, hcA⟩ := (SetLike.lt_iff_le_and_exists.mp hlt).2
  intro hbot
  have hmem : QuotientGroup.mk' A c ∈ C.map (QuotientGroup.mk' A) :=
    Subgroup.mem_map_of_mem _ hcC
  rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
  exact hcA hmem

/-- Every nontrivial normal subgroup of a finite `p`-group intersects the center nontrivially. -/
private lemma exists_mem_normal_inf_center_ne_one {p : ℕ} (hp : p.Prime)
    {Q : Type*} [Group Q] [Finite Q] (hQ : IsPGroup p Q)
    (N : Subgroup Q) [N.Normal] (hN : N ≠ ⊥) :
    ∃ y : Q, y ∈ N ∧ y ∈ Subgroup.center Q ∧ y ≠ 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hN_pg : IsPGroup p N := hQ.to_subgroup N
  have : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hN
  obtain ⟨r, hr, hcard⟩ := hN_pg.nontrivial_iff_card.mp inferInstance
  have hdvd : p ∣ Nat.card N := hcard ▸ dvd_pow_self p hr.ne'
  have hfix1 : (1 : N) ∈ MulAction.fixedPoints (ConjAct Q) N := fun g => smul_one g
  have hConj : IsPGroup p (ConjAct Q) := hQ.of_equiv ConjAct.toConjAct
  obtain ⟨b, hb_fix, hb_ne⟩ :=
    hConj.exists_fixed_point_of_prime_dvd_card_of_fixed_point (N : Type _) hdvd hfix1
  refine ⟨b.1, b.2, ?_, fun h1 => hb_ne (Subtype.ext h1.symm)⟩
  rw [Subgroup.mem_center_iff]
  intro g
  have hcoe := congrArg Subtype.val (hb_fix (ConjAct.toConjAct g))
  rw [ConjAct.Subgroup.val_conj_smul, ConjAct.toConjAct_smul] at hcoe
  exact mul_inv_eq_iff_eq_mul.mp hcoe

private lemma triangle_step_identity (j : ℕ) : j * (j - 1) / 2 + j = (j + 1) * j / 2 := by
  cases j with
  | zero => simp
  | succ n =>
    have hmul : (n + 1 + 1) * (n + 1) = (n + 1) * n + 2 * (n + 1) := by ring
    rw [Nat.succ_sub_one, hmul, Nat.add_mul_div_left _ _ (by decide : 0 < 2)]

end Helpers

section ClassTwo

/-- If `[G, G] ≤ Z(G)` in a finite group `G`, every abelian subgroup has order bounded by the
maximum order of an abelian normal subgroup of `G`. -/
theorem abelian_card_le_of_commutator_le_center
    {G : Type*} [Group G] [Finite G]
    (hclass : commutator G ≤ Subgroup.center G) {M : ℕ}
    (hnorm : ∀ H : Subgroup G, H.Normal ∧ IsMulCommutative H → Nat.card H ≤ M)
    (B : Subgroup G) (hB : IsMulCommutative B) :
    Nat.card B ≤ M := by
  let H : Subgroup G := B ⊔ Subgroup.center G
  have hHnorm : H.Normal := Subgroup.Normal.of_commutator_le G (hclass.trans le_sup_right)
  have hHcomm : IsMulCommutative H :=
    isMulCommutative_sup_of_le_centralizer hB inferInstance
      (Subgroup.le_centralizer_iff.mp (Subgroup.center_le_centralizer _))
  exact (Subgroup.card_le_of_le (le_sup_left : B ≤ H)).trans (hnorm H ⟨hHnorm, hHcomm⟩)

/-- Pyber's bound `|B| ≤ p ^ k` holds sharply whenever `G` has nilpotency class at most `2`. -/
theorem pyber_bound_of_nilpotencyClass_le_two
    {p : ℕ} (G : Type*) [Group G] [Finite G] [Group.IsNilpotent G]
    (hclass : Group.nilpotencyClass G ≤ 2) (k : ℕ)
    (hnorm : ∀ H : Subgroup G, H.Normal ∧ IsMulCommutative H → Nat.card H ≤ p ^ k)
    (B : Subgroup G) (hB : IsMulCommutative B) :
    Nat.card B ≤ p ^ k := by
  have h2 : Subgroup.upperCentralSeries G 2 = ⊤ :=
    Subgroup.upperCentralSeries_eq_top_iff_nilpotencyClass_le.mpr hclass
  have hcom : commutator G ≤ Subgroup.center G := calc
    commutator G = ⁅(⊤ : Subgroup G), ⊤⁆ := commutator_def G
    _ = ⁅Subgroup.upperCentralSeries G 2, ⊤⁆ := by rw [h2]
    _ ≤ Subgroup.upperCentralSeries G 1 := Subgroup.commutator_upperCentralSeries_top_le G 1
    _ = Subgroup.center G := Subgroup.upperCentralSeries_one G
  exact abelian_card_le_of_commutator_le_center hcom hnorm B hB

end ClassTwo

section BurnsideMaxAbelian

/-- **Burnside's Theorem**: In a finite `p`-group `G`, any abelian normal subgroup `A` of maximum
cardinality among abelian normal subgroups is self-centralizing (`C_G(A) = A`). -/
theorem centralizer_eq_self_of_max_normal_abelian
    {p : ℕ} (hp : p.Prime) {G : Type*} [Group G] [Finite G] (hG : IsPGroup p G)
    (A : Subgroup G) (hAnorm : A.Normal) (hAab : IsMulCommutative A)
    (hAmax : ∀ H : Subgroup G, H.Normal ∧ IsMulCommutative H → Nat.card H ≤ Nat.card A) :
    Subgroup.centralizer (A : Set G) = A := by
  have hle : A ≤ Subgroup.centralizer (A : Set G) := Subgroup.le_centralizer A
  by_contra hne
  have hlt : A < Subgroup.centralizer (A : Set G) := lt_of_le_of_ne hle (Ne.symm hne)
  let C := Subgroup.centralizer (A : Set G)
  let π := QuotientGroup.mk' A
  let N := C.map π
  have hCnorm : C.Normal := Subgroup.normal_centralizer
  have hNnorm : N.Normal := hCnorm.map π (QuotientGroup.mk'_surjective A)
  have hNne : N ≠ ⊥ := map_mk'_ne_bot_of_lt hlt
  obtain ⟨y, hyN, hycenter, hy1⟩ :=
    exists_mem_normal_inf_center_ne_one hp (hG.to_quotient A) N hNne
  obtain ⟨x, hxC, rfl⟩ := Subgroup.mem_map.mp hyN
  have hxA : x ∉ A := by
    intro hx
    apply hy1
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  let K : Subgroup (G ⧸ A) := Subgroup.zpowers (π x)
  have hKnorm : K.Normal := normal_of_le_center (Subgroup.zpowers_le.mpr hycenter)
  let A' : Subgroup G := K.comap π
  have hA'norm : A'.Normal := hKnorm.comap π
  have hA'eq : A' = A ⊔ Subgroup.zpowers x := by
    dsimp [A', K]
    rw [← MonoidHom.map_zpowers, Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_comm]
  have hA'comm : IsMulCommutative A' := by
    rw [hA'eq]
    exact isMulCommutative_sup_of_le_centralizer hAab (isMulCommutative_zpowers x)
      (Subgroup.le_centralizer_iff.mp (Subgroup.zpowers_le.mpr hxC))
  have hAlt : A < A' := by
    rw [hA'eq]
    exact lt_of_le_of_ne le_sup_left fun h => hxA (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
  have hcardlt : Nat.card A < Nat.card A' := by
    by_contra hle_card
    exact hAlt.ne (Subgroup.eq_of_le_of_card_ge hAlt.le (Nat.le_of_not_lt hle_card))
  exact absurd (hAmax A' ⟨hA'norm, hA'comm⟩) (not_le_of_gt hcardlt)

end BurnsideMaxAbelian

section QuadraticBound

/-- Inductive step for the Alperin–Roquette–Burnside index bound: given a proper normal subgroup
`B < A` of order `p ^ j` inside an abelian normal subgroup `A`, finds a normal subgroup `B'` with
`B ≤ B' ≤ A`, `|B'| = p ^ (j + 1)`, and `[C_G(B) : C_G(B')] ≤ p ^ j`. -/
private lemma centralizer_index_step
    {p : ℕ} (hp : p.Prime) {G : Type*} [Group G] [Finite G] (hG : IsPGroup p G)
    {A : Subgroup G} (hAnorm : A.Normal) (hAab : IsMulCommutative A)
    {B : Subgroup G} (hBnorm : B.Normal) (hBA : B ≤ A) (hBltA : B < A)
    {j : ℕ} (hBcard : Nat.card B = p ^ j)
    (hBidx : (Subgroup.centralizer (B : Set G)).index ≤ p ^ (j * (j - 1) / 2)) :
    ∃ B' : Subgroup G, B'.Normal ∧ B' ≤ A ∧ Nat.card B' = p ^ (j + 1) ∧
      (Subgroup.centralizer (B' : Set G)).index ≤ p ^ ((j + 1) * j / 2) := by
  have : Fact p.Prime := ⟨hp⟩
  let π := QuotientGroup.mk' B
  let N := A.map π
  have hNnorm : N.Normal := hAnorm.map π (QuotientGroup.mk'_surjective B)
  have hNne : N ≠ ⊥ := map_mk'_ne_bot_of_lt hBltA
  have : Nontrivial ↥(N ⊓ Subgroup.center (G ⧸ B)) := by
    obtain ⟨y, hyN, hyC, hy1⟩ :=
      exists_mem_normal_inf_center_ne_one hp (hG.to_quotient B) N hNne
    exact ⟨⟨1, ⟨y, hyN, hyC⟩, fun h => hy1 (congrArg Subtype.val h).symm⟩⟩
  have hInf_pg : IsPGroup p ↥(N ⊓ Subgroup.center (G ⧸ B)) :=
    (hG.to_quotient B).to_subgroup _
  obtain ⟨r, hr, hr_card⟩ := hInf_pg.nontrivial_iff_card.mp inferInstance
  have hdvd : p ∣ Nat.card ↥(N ⊓ Subgroup.center (G ⧸ B)) :=
    hr_card ▸ dvd_pow_self p hr.ne'
  obtain ⟨u0, hu0_ord⟩ := exists_prime_orderOf_dvd_card' p hdvd
  let u_bar : G ⧸ B := u0.1
  have hu_N : u_bar ∈ N := u0.2.1
  have hu_C : u_bar ∈ Subgroup.center (G ⧸ B) := u0.2.2
  have hu_ord : orderOf u_bar = p := by
    simpa [u_bar, Subgroup.orderOf_coe] using hu0_ord
  obtain ⟨u, _, hu_mk⟩ := Subgroup.mem_map.mp hu_N
  let K : Subgroup (G ⧸ B) := Subgroup.zpowers u_bar
  have hKnorm : K.Normal := normal_of_le_center (Subgroup.zpowers_le.mpr hu_C)
  have hKcard : Nat.card K = p := by
    rw [Nat.card_zpowers, hu_ord]
  let B' : Subgroup G := K.comap π
  have hB'norm : B'.Normal := hKnorm.comap π
  have hBB' : B ≤ B' := by
    intro b hb
    change π b ∈ K
    have hker : π b = 1 := (QuotientGroup.eq_one_iff b).mpr hb
    rw [hker]
    exact K.one_mem
  have hB'A : B' ≤ A := by
    intro z hz
    have hz_comap : z ∈ (A.map π).comap π := (Subgroup.zpowers_le.mpr hu_N) hz
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_of_le_left hBA] at hz_comap
    exact hz_comap
  have hB'card : Nat.card B' = p ^ (j + 1) := by
    have hrel : B.relIndex B' = p := by
      rw [← QuotientGroup.ker_mk' B, Subgroup.relIndex_ker]
      have hmap : B'.map π = K :=
        Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective B) K
      rw [hmap, hKcard]
    have hmul := (B.subgroupOf B').card_mul_index
    have hsub : Nat.card (B.subgroupOf B') = Nat.card B :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBB').toEquiv
    change Nat.card (B.subgroupOf B') * B.relIndex B' = Nat.card B' at hmul
    rw [hsub, hBcard, hrel] at hmul
    rw [← hmul, pow_succ]
  have hCB'le : Subgroup.centralizer (B' : Set G) ≤ Subgroup.centralizer (B : Set G) :=
    Subgroup.centralizer_le hBB'
  -- The map `g ↦ [g, u]` sends `C_G(B)` homomorphically into `B` with kernel `C_G(B')`.
  have hcomm_mem : ∀ x : G, x * u * x⁻¹ * u⁻¹ ∈ B := by
    intro x
    rw [← QuotientGroup.ker_mk' B, MonoidHom.mem_ker, map_mul, map_mul, map_mul,
      map_inv, map_inv, hu_mk]
    have hcomm := Subgroup.mem_center_iff.mp hu_C (π x)
    change π x * u_bar * (π x)⁻¹ * u_bar⁻¹ = 1
    rw [hcomm, mul_inv_cancel_right, mul_inv_cancel]
  let δ : Subgroup.centralizer (B : Set G) →* B :=
    { toFun := fun g => ⟨g.1 * u * g.1⁻¹ * u⁻¹, hcomm_mem g.1⟩
      map_one' := by
        ext
        simp
      map_mul' := fun g h => by
        ext
        have hconj : g.1 * (h.1 * u * h.1⁻¹ * u⁻¹) * g.1⁻¹ = h.1 * u * h.1⁻¹ * u⁻¹ := by
          have hgcomm := Subgroup.mem_centralizer_iff.mp g.2 _ (hcomm_mem h.1)
          exact mul_inv_eq_iff_eq_mul.mpr hgcomm.symm
        have hcommB : (h.1 * u * h.1⁻¹ * u⁻¹) * (g.1 * u * g.1⁻¹ * u⁻¹) =
            (g.1 * u * g.1⁻¹ * u⁻¹) * (h.1 * u * h.1⁻¹ * u⁻¹) :=
          Subgroup.mem_centralizer_iff.mp
            (Subgroup.le_centralizer A (hBA (hcomm_mem g.1))) _ (hBA (hcomm_mem h.1))
        calc
          (g.1 * h.1) * u * (g.1 * h.1)⁻¹ * u⁻¹
              = (g.1 * (h.1 * u * h.1⁻¹ * u⁻¹) * g.1⁻¹) * (g.1 * u * g.1⁻¹ * u⁻¹) := by
                group
          _ = (h.1 * u * h.1⁻¹ * u⁻¹) * (g.1 * u * g.1⁻¹ * u⁻¹) := by rw [hconj]
          _ = (g.1 * u * g.1⁻¹ * u⁻¹) * (h.1 * u * h.1⁻¹ * u⁻¹) := hcommB }
  have hker : δ.ker =
      (Subgroup.centralizer (B' : Set G)).subgroupOf (Subgroup.centralizer (B : Set G)) := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subtype.ext_iff]
    change g.1 * u * g.1⁻¹ * u⁻¹ = 1 ↔ g.1 ∈ Subgroup.centralizer (B' : Set G)
    constructor
    · intro h1
      have hgu : u * g.1 = g.1 * u :=
        (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)).symm
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hz : π z ∈ K)
      have hmemB : z * (u ^ n)⁻¹ ∈ B := by
        rw [← QuotientGroup.ker_mk' B, MonoidHom.mem_ker, map_mul, map_inv, map_zpow, hu_mk,
          hn, mul_inv_cancel]
      set b := z * (u ^ n)⁻¹
      have hzb : z = b * u ^ n := by simp [b, mul_assoc]
      have hbg : b * g.1 = g.1 * b := Subgroup.mem_centralizer_iff.mp g.2 b hmemB
      have hung : u ^ n * g.1 = g.1 * u ^ n := (Commute.zpow_left hgu n).eq
      rw [hzb, mul_assoc, hung, ← mul_assoc, hbg, mul_assoc]
    · intro hgB'
      have huB' : u ∈ B' := by
        change π u ∈ K
        rw [hu_mk]
        exact Subgroup.mem_zpowers u_bar
      have hgu : u * g.1 = g.1 * u := Subgroup.mem_centralizer_iff.mp hgB' u huB'
      rw [← hgu, mul_inv_cancel_right, mul_inv_cancel]
  have hrelIdx :
      (Subgroup.centralizer (B' : Set G)).relIndex (Subgroup.centralizer (B : Set G)) ≤
        p ^ j := by
    change ((Subgroup.centralizer (B' : Set G)).subgroupOf
      (Subgroup.centralizer (B : Set G))).index ≤ p ^ j
    rw [← hker, Subgroup.index_ker, ← hBcard]
    exact Subgroup.card_le_card_group δ.range
  have hB'idx : (Subgroup.centralizer (B' : Set G)).index ≤ p ^ ((j + 1) * j / 2) := by
    rw [← Subgroup.relIndex_mul_index hCB'le]
    calc
      (Subgroup.centralizer (B' : Set G)).relIndex (Subgroup.centralizer (B : Set G)) *
          (Subgroup.centralizer (B : Set G)).index
          ≤ p ^ j * p ^ (j * (j - 1) / 2) := Nat.mul_le_mul hrelIdx hBidx
      _ = p ^ (j * (j - 1) / 2 + j) := by rw [mul_comm, pow_add]
      _ = p ^ ((j + 1) * j / 2) := by rw [triangle_step_identity]
  exact ⟨B', hB'norm, hB'A, hB'card, hB'idx⟩

/-- **Burnside–Alperin–Roquette Quadratic Bound**: If every abelian normal subgroup of a finite
`p`-group `G` has order at most `p ^ k`, then `|G| ≤ p ^ (k * (k + 1) / 2)`. -/
theorem card_group_le_pow_quadratic
    {p : ℕ} (hp : p.Prime) (G : Type*) [Group G] [Finite G] (hG : IsPGroup p G) (k : ℕ)
    (hnorm : ∀ H : Subgroup G, H.Normal ∧ IsMulCommutative H → Nat.card H ≤ p ^ k) :
    Nat.card G ≤ p ^ (k * (k + 1) / 2) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (Subgroup G) := Finite.of_injective SetLike.coe SetLike.coe_injective
  let S : Set (Subgroup G) := {H : Subgroup G | H.Normal ∧ IsMulCommutative H}
  have hbot_mem : (⊥ : Subgroup G) ∈ S :=
    ⟨inferInstance, Subgroup.le_centralizer_iff_isMulCommutative.mp bot_le⟩
  obtain ⟨A, hAmem, hAmax⟩ := Set.exists_max_image S (fun H => Nat.card H)
    (Set.toFinite S) ⟨⊥, hbot_mem⟩
  have hAnorm : A.Normal := hAmem.1
  have hAab : IsMulCommutative A := hAmem.2
  have hCA : Subgroup.centralizer (A : Set G) = A :=
    centralizer_eq_self_of_max_normal_abelian hp hG A hAnorm hAab (fun H hH => hAmax H hH)
  obtain ⟨m, hm_card⟩ := IsPGroup.iff_card.mp (hG.to_subgroup A)
  have hmk : m ≤ k := by
    have hpow : p ^ m ≤ p ^ k := hm_card ▸ hnorm A hAmem
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hpow
  have hind : ∀ j : ℕ, j ≤ m →
      ∃ B : Subgroup G, B.Normal ∧ B ≤ A ∧ Nat.card B = p ^ j ∧
        (Subgroup.centralizer (B : Set G)).index ≤ p ^ (j * (j - 1) / 2) := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨⊥, inferInstance, bot_le, by simp, ?_⟩
      have htop : Subgroup.centralizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
        Subgroup.centralizer_eq_top_iff_subset.mpr (by simp)
      rw [htop]
      simp
    | succ j ih =>
      intro hj
      obtain ⟨B, hBnorm, hBA, hBcard, hBidx⟩ := ih (Nat.le_of_succ_le hj)
      have hBltA : B < A := by
        refine lt_of_le_of_ne hBA ?_
        intro hEq
        have hlt_pow : p ^ j < p ^ m := Nat.pow_lt_pow_right hp.one_lt hj
        rw [← hBcard, ← hm_card, hEq] at hlt_pow
        exact lt_irrefl _ hlt_pow
      exact centralizer_index_step hp hG hAnorm hAab hBnorm hBA hBltA hBcard hBidx
  obtain ⟨B, _, hBA, hBcard, hBidx⟩ := hind m le_rfl
  have hBeqA : B = A := Subgroup.eq_of_le_of_card_ge hBA (by rw [hBcard, hm_card])
  rw [hBeqA, hCA] at hBidx
  calc
    Nat.card G = Nat.card A * A.index := A.card_mul_index.symm
    _ ≤ p ^ m * p ^ (m * (m - 1) / 2) := Nat.mul_le_mul (le_of_eq hm_card) hBidx
    _ = p ^ (m * (m - 1) / 2 + m) := by rw [mul_comm, pow_add]
    _ = p ^ ((m + 1) * m / 2) := by rw [triangle_step_identity]
    _ = p ^ (m * (m + 1) / 2) := by rw [mul_comm (m + 1) m]
    _ ≤ p ^ (k * (k + 1) / 2) := by
      refine Nat.pow_le_pow_right hp.pos ?_
      exact Nat.div_le_div_right (Nat.mul_le_mul hmk (Nat.add_le_add_right hmk 1))

/-- Every subgroup (in particular every abelian subgroup) of a finite `p`-group whose abelian
normal subgroups have order at most `p ^ k` has order at most `p ^ (k * (k + 1) / 2)`. -/
theorem abelian_card_le_pow_quadratic
    {p : ℕ} (hp : p.Prime) (G : Type*) [Group G] [Finite G] (hG : IsPGroup p G) (k : ℕ)
    (hnorm : ∀ H : Subgroup G, H.Normal ∧ IsMulCommutative H → Nat.card H ≤ p ^ k)
    (B : Subgroup G) :
    Nat.card B ≤ p ^ (k * (k + 1) / 2) :=
  (Subgroup.card_le_card_group (H := B)).trans (card_group_le_pow_quadratic hp G hG k hnorm)

end QuadraticBound

/- ## Part 2: Bipartite `𝔽₂` Non-Isotropy, Swap-Semidirect Engine & Kourovka 20.75 / 20.76 -/

section BaseField

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Ambient F_2-vector space of dimension n. -/
abbrev W (n : ℕ) : Type := Fin n → ZMod 2

/-- Target F_2-vector space of dimension z0. -/
abbrev Z0 (z₀ : ℕ) : Type := Fin z₀ → ZMod 2

/-- Strictly upper-triangular index pairs on Fin n. -/
abbrev UpperTriIdx (n : ℕ) : Type := { p : Fin n × Fin n // p.1 < p.2 }

/-- Space of strictly upper-triangular bilinear forms W n x W n -> Z0 z0. -/
abbrev UpperTri (n z₀ : ℕ) : Type := UpperTriIdx n → Z0 z₀

lemma zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  rcases zmod2_cases x with rfl | rfl
  · simp
  · decide

lemma zmod2_neg_eq (x : ZMod 2) : -x = x :=
  neg_eq_iff_add_eq_zero.mpr (zmod2_add_self x)

lemma w_add_self {n : ℕ} (u : W n) : u + u = 0 := by
  ext i
  exact zmod2_add_self (u i)

lemma w_eq_of_add_eq_zero {n : ℕ} {u v : W n} (h : u + v = 0) : u = v := by
  have := congrArg (· + v) h
  simpa [add_assoc, w_add_self] using this

lemma z0_add_self {z₀ : ℕ} (z : Z0 z₀) : z + z = 0 := by
  ext i
  exact zmod2_add_self (z i)

lemma card_w (n : ℕ) : Fintype.card (W n) = 2 ^ n := by
  simp [ZMod.card]

lemma card_z0 (z₀ : ℕ) : Fintype.card (Z0 z₀) = 2 ^ z₀ := by
  simp [ZMod.card]

lemma card_upperTriIdx (d : ℕ) : Fintype.card (UpperTriIdx d) = d * (d - 1) / 2 := by
  let s₁ : Finset (Fin d × Fin d) := Finset.univ.filter (fun q => q.1 < q.2)
  let s₂ : Finset (Fin d × Fin d) := Finset.univ.filter (fun q => q.2 < q.1)
  let s₃ : Finset (Fin d × Fin d) := Finset.univ.filter (fun q => q.1 = q.2)
  have hs₁ : Fintype.card (UpperTriIdx d) = s₁.card := by
    rw [Fintype.card_subtype]
  have hs₂ : s₂.card = s₁.card := by
    refine Finset.card_bij (fun q _ => q.swap) ?_ ?_ ?_
    · intro q hq
      simp only [s₁, s₂, Finset.mem_filter, Finset.mem_univ, true_and, Prod.fst_swap,
        Prod.snd_swap] at hq ⊢
      exact hq
    · intro q₁ _ q₂ _ h
      exact Prod.swap_inj.mp h
    · intro q hq
      refine ⟨q.swap, ?_, Prod.swap_swap q⟩
      simp only [s₁, s₂, Finset.mem_filter, Finset.mem_univ, true_and, Prod.fst_swap,
        Prod.snd_swap] at hq ⊢
      exact hq
  have hs₃ : s₃.card = d := by
    refine (Finset.card_bij (fun i _ => (i, i)) ?_ ?_ ?_).symm.trans (Finset.card_fin d)
    · intro i _
      simp [s₃]
    · intro i j _ _ h
      exact (Prod.ext_iff.mp h).1
    · intro q hq
      simp only [s₃, Finset.mem_filter, Finset.mem_univ, true_and] at hq
      exact ⟨q.1, Finset.mem_univ _, Prod.ext rfl hq⟩
  have hdisj₁₂ : Disjoint s₁ s₂ := by
    rw [Finset.disjoint_left]
    intro q hq₁ hq₂
    simp only [s₁, s₂, Finset.mem_filter, Finset.mem_univ, true_and] at hq₁ hq₂
    exact lt_asymm hq₁ hq₂
  have hdisj₁₃ : Disjoint s₁ s₃ := by
    rw [Finset.disjoint_left]
    intro q hq₁ hq₃
    simp only [s₁, s₃, Finset.mem_filter, Finset.mem_univ, true_and] at hq₁ hq₃
    exact hq₁.ne hq₃
  have hdisj₂₃ : Disjoint s₂ s₃ := by
    rw [Finset.disjoint_left]
    intro q hq₂ hq₃
    simp only [s₂, s₃, Finset.mem_filter, Finset.mem_univ, true_and] at hq₂ hq₃
    exact hq₂.ne hq₃.symm
  have hunion : s₁ ∪ s₂ ∪ s₃ = Finset.univ := by
    ext q
    simp only [s₁, s₂, s₃, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      iff_true]
    rcases lt_trichotomy q.1 q.2 with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
    · exact Or.inl (Or.inr h)
  have htot : s₁.card + s₂.card + s₃.card = d * d := by
    have h12 : (s₁ ∪ s₂).card = s₁.card + s₂.card := Finset.card_union_of_disjoint hdisj₁₂
    have h123 : (s₁ ∪ s₂ ∪ s₃).card = (s₁ ∪ s₂).card + s₃.card :=
      Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hdisj₁₃, hdisj₂₃⟩)
    rw [← h12, ← h123, hunion, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  have hmul : 2 * s₁.card = d * (d - 1) := by
    rcases d with _ | d
    · have hs₁_empty : s₁ = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro ⟨i, _⟩
        exact Fin.elim0 i
      simp [hs₁_empty]
    · have hmul' : (d + 1) * (d + 1) = (d + 1) * d + (d + 1) := by ring
      change 2 * s₁.card = (d + 1) * d
      omega
  rw [hs₁, ← hmul]
  omega

end BaseField

section BilinearForms

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Bilinear pairing associated to an upper-triangular form M. -/
def fBil {n z₀ : ℕ} (M : UpperTri n z₀) (u v : W n) : Z0 z₀ :=
  ∑ p : UpperTriIdx n, (u p.1.1 * v p.1.2) • M p

/-- Alternating symmetric bilinear form omega(M, u, v) = f(u, v) + f(v, u). -/
def ω {n z₀ : ℕ} (M : UpperTri n z₀) (u v : W n) : Z0 z₀ :=
  fBil M u v + fBil M v u

@[simp]
lemma fBil_zero_left {n z₀ : ℕ} (M : UpperTri n z₀) (v : W n) : fBil M 0 v = 0 := by
  simp [fBil]

@[simp]
lemma fBil_zero_right {n z₀ : ℕ} (M : UpperTri n z₀) (u : W n) : fBil M u 0 = 0 := by
  simp [fBil]

lemma fBil_add_left {n z₀ : ℕ} (M : UpperTri n z₀) (u₁ u₂ v : W n) :
    fBil M (u₁ + u₂) v = fBil M u₁ v + fBil M u₂ v := by
  simp only [fBil, Pi.add_apply, add_mul, add_smul, Finset.sum_add_distrib]

lemma fBil_add_right {n z₀ : ℕ} (M : UpperTri n z₀) (u v₁ v₂ : W n) :
    fBil M u (v₁ + v₂) = fBil M u v₁ + fBil M u v₂ := by
  simp only [fBil, Pi.add_apply, mul_add, add_smul, Finset.sum_add_distrib]

lemma fBil_smul_left {n z₀ : ℕ} (M : UpperTri n z₀) (c : ZMod 2) (u v : W n) :
    fBil M (c • u) v = c • fBil M u v := by
  simp only [fBil, Pi.smul_apply, smul_eq_mul, mul_assoc, ← smul_smul, ← Finset.smul_sum]

lemma fBil_smul_right {n z₀ : ℕ} (M : UpperTri n z₀) (c : ZMod 2) (u v : W n) :
    fBil M u (c • v) = c • fBil M u v := by
  simp only [fBil, Pi.smul_apply, smul_eq_mul, mul_left_comm, ← smul_smul, ← Finset.smul_sum]

lemma fBil_add_form {n z₀ : ℕ} (M₁ M₂ : UpperTri n z₀) (u v : W n) :
    fBil (M₁ + M₂) u v = fBil M₁ u v + fBil M₂ u v := by
  simp only [fBil, Pi.add_apply, smul_add, Finset.sum_add_distrib]

lemma fBil_smul_form {n z₀ : ℕ} (c : ZMod 2) (M : UpperTri n z₀) (u v : W n) :
    fBil (c • M) u v = c • fBil M u v := by
  simp only [fBil, Pi.smul_apply, smul_comm _ c, ← Finset.smul_sum]

@[simp]
lemma ω_self {n z₀ : ℕ} (M : UpperTri n z₀) (u : W n) : ω M u u = 0 :=
  z0_add_self (fBil M u u)

lemma ω_symm {n z₀ : ℕ} (M : UpperTri n z₀) (u v : W n) : ω M u v = ω M v u :=
  add_comm _ _

lemma ω_add_left {n z₀ : ℕ} (M : UpperTri n z₀) (u₁ u₂ v : W n) :
    ω M (u₁ + u₂) v = ω M u₁ v + ω M u₂ v := by
  simp only [ω, fBil_add_left, fBil_add_right]
  abel

lemma ω_add_right {n z₀ : ℕ} (M : UpperTri n z₀) (u v₁ v₂ : W n) :
    ω M u (v₁ + v₂) = ω M u v₁ + ω M u v₂ := by
  simp only [ω, fBil_add_left, fBil_add_right]
  abel

lemma ω_smul_left {n z₀ : ℕ} (M : UpperTri n z₀) (c : ZMod 2) (u v : W n) :
    ω M (c • u) v = c • ω M u v := by
  simp only [ω, fBil_smul_left, fBil_smul_right, smul_add]

lemma ω_smul_right {n z₀ : ℕ} (M : UpperTri n z₀) (c : ZMod 2) (u v : W n) :
    ω M u (c • v) = c • ω M u v := by
  simp only [ω, fBil_smul_left, fBil_smul_right, smul_add]

lemma ω_add_form {n z₀ : ℕ} (M₁ M₂ : UpperTri n z₀) (u v : W n) :
    ω (M₁ + M₂) u v = ω M₁ u v + ω M₂ u v := by
  simp only [ω, fBil_add_form]
  abel

lemma ω_smul_form {n z₀ : ℕ} (c : ZMod 2) (M : UpperTri n z₀) (u v : W n) :
    ω (c • M) u v = c • ω M u v := by
  simp only [ω, fBil_smul_form, smul_add]

/-- Evaluation of omega(M, -, -) on all strictly upper pairs of a tuple T : Fin d -> W n. -/
def evalT {n z₀ d : ℕ} (T : Fin d → W n) :
    UpperTri n z₀ →ₗ[ZMod 2] (UpperTriIdx d → Z0 z₀) where
  toFun M q := ω M (T q.1.1) (T q.1.2)
  map_add' M₁ M₂ := by
    ext q k
    simp [ω_add_form]
  map_smul' c M := by
    ext q k
    simp [ω_smul_form]

lemma dual_of_linearIndependent {n d : ℕ} {T : Fin d → W n}
    (hT : LinearIndependent (ZMod 2) T) :
    ∃ f : Fin d → (W n →ₗ[ZMod 2] ZMod 2),
      ∀ a b : Fin d, f a (T b) = if a = b then 1 else 0 := by
  let b := Module.Basis.span hT
  have hmem : ∀ i : Fin d, T i ∈ Submodule.span (ZMod 2) (Set.range T) :=
    fun i => Submodule.subset_span (Set.mem_range_self i)
  have hcoord : ∀ a : Fin d, ∃ fa : W n →ₗ[ZMod 2] ZMod 2,
      fa.comp (Submodule.span (ZMod 2) (Set.range T)).subtype = b.coord a :=
    fun a => LinearMap.exists_extend (b.coord a)
  refine ⟨fun a => (hcoord a).choose, fun a i => ?_⟩
  have hfa := (hcoord a).choose_spec
  have h1 : (hcoord a).choose (T i) =
      ((hcoord a).choose.comp (Submodule.span (ZMod 2) (Set.range T)).subtype) ⟨T i, hmem i⟩ := rfl
  rw [h1, hfa]
  change b.repr ⟨T i, hmem i⟩ a = _
  rw [Module.Basis.span_repr_eq_single hT i (hmem i), Finsupp.single_apply]
  by_cases h : a = i <;> simp [h, eq_comm]

lemma w_eq_sum_single {n : ℕ} (u : W n) :
    u = ∑ i : Fin n, u i • Pi.single i (1 : ZMod 2) := by
  ext k
  simp [Finset.sum_apply, Pi.single_apply]

lemma linearMap_apply_w {n : ℕ} (g : W n →ₗ[ZMod 2] ZMod 2) (u : W n) :
    g u = ∑ i : Fin n, u i * g (Pi.single i 1) := by
  conv_lhs => rw [w_eq_sum_single u]
  simp [map_sum, map_smul, smul_eq_mul]

lemma ω_rankOne {n z₀ : ℕ} (fa fb : W n →ₗ[ZMod 2] ZMod 2) (z : Z0 z₀) (u v : W n) :
    ω (fun p : UpperTriIdx n =>
      (fa (Pi.single p.1.1 1) * fb (Pi.single p.1.2 1) +
        fa (Pi.single p.1.2 1) * fb (Pi.single p.1.1 1)) • z) u v =
      (fa u * fb v + fa v * fb u) • z := by
  let C : Fin n → Fin n → ZMod 2 := fun i j =>
    fa (Pi.single i 1) * fb (Pi.single j 1) + fa (Pi.single j 1) * fb (Pi.single i 1)
  have hCsymm : ∀ i j, C j i = C i j := fun i j => add_comm _ _
  have hCdiag : ∀ i, C i i = 0 := fun i => zmod2_add_self _
  let M₀ : UpperTri n z₀ := fun p => C p.1.1 p.1.2 • z
  have hLHS : ω M₀ u v =
      (∑ p : UpperTriIdx n, (u p.1.1 * v p.1.2 + v p.1.1 * u p.1.2) * C p.1.1 p.1.2) • z := by
    simp only [ω, fBil, M₀, ← Finset.sum_add_distrib]
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [smul_smul, smul_smul, ← add_smul, ← add_mul]
  have hsplit : (∑ p : UpperTriIdx n, (u p.1.1 * v p.1.2 + v p.1.1 * u p.1.2) * C p.1.1 p.1.2) =
      ∑ p : Fin n × Fin n, (u p.1 * v p.2) * C p.1 p.2 := by
    let s₁ : Finset (Fin n × Fin n) := Finset.univ.filter (fun q => q.1 < q.2)
    let s₂ : Finset (Fin n × Fin n) := Finset.univ.filter (fun q => q.2 < q.1)
    let s₃ : Finset (Fin n × Fin n) := Finset.univ.filter (fun q => q.1 = q.2)
    have hdisj₁₂ : Disjoint s₁ s₂ := by
      rw [Finset.disjoint_left]
      intro q hq₁ hq₂
      simp only [s₁, s₂, Finset.mem_filter, Finset.mem_univ, true_and] at hq₁ hq₂
      exact lt_asymm hq₁ hq₂
    have hdisj₁₃ : Disjoint s₁ s₃ := by
      rw [Finset.disjoint_left]
      intro q hq₁ hq₃
      simp only [s₁, s₃, Finset.mem_filter, Finset.mem_univ, true_and] at hq₁ hq₃
      exact hq₁.ne hq₃
    have hdisj₂₃ : Disjoint s₂ s₃ := by
      rw [Finset.disjoint_left]
      intro q hq₂ hq₃
      simp only [s₂, s₃, Finset.mem_filter, Finset.mem_univ, true_and] at hq₂ hq₃
      exact hq₂.ne hq₃.symm
    have hunion : s₁ ∪ s₂ ∪ s₃ = Finset.univ := by
      ext q
      simp only [s₁, s₂, s₃, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        iff_true]
      rcases lt_trichotomy q.1 q.2 with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
      · exact Or.inl (Or.inr h)
    have hsum_s₁ : (∑ p : UpperTriIdx n, (u p.1.1 * v p.1.2 + v p.1.1 * u p.1.2) * C p.1.1 p.1.2) =
        ∑ q ∈ s₁, (u q.1 * v q.2 + v q.1 * u q.2) * C q.1 q.2 := by
      refine Finset.sum_bij (fun p _ => p.1) ?_ ?_ ?_ ?_
      · intro p _
        simp only [s₁, Finset.mem_filter, Finset.mem_univ, true_and]
        exact p.2
      · intro p₁ _ p₂ _ h
        exact Subtype.ext h
      · intro q hq
        simp only [s₁, Finset.mem_filter, Finset.mem_univ, true_and] at hq
        exact ⟨⟨q, hq⟩, Finset.mem_univ _, rfl⟩
      · intro p _
        rfl
    have hs₂_eq : (∑ q ∈ s₂, (u q.1 * v q.2) * C q.1 q.2) =
        ∑ q ∈ s₁, (v q.1 * u q.2) * C q.1 q.2 := by
      refine Finset.sum_bij (fun q _ => q.swap) ?_ ?_ ?_ ?_
      · intro q hq
        simp only [s₁, s₂, Finset.mem_filter, Finset.mem_univ, true_and, Prod.fst_swap,
          Prod.snd_swap] at hq ⊢
        exact hq
      · intro q₁ _ q₂ _ h
        exact Prod.swap_inj.mp h
      · intro q hq
        refine ⟨q.swap, ?_, Prod.swap_swap q⟩
        simp only [s₁, s₂, Finset.mem_filter, Finset.mem_univ, true_and, Prod.fst_swap,
          Prod.snd_swap] at hq ⊢
        exact hq
      · intro q _
        simp only [Prod.fst_swap, Prod.snd_swap, hCsymm]
        ring
    have hs₃_eq : (∑ q ∈ s₃, (u q.1 * v q.2) * C q.1 q.2) = 0 := by
      refine Finset.sum_eq_zero fun q hq => ?_
      simp only [s₃, Finset.mem_filter, Finset.mem_univ, true_and] at hq
      rw [hq, hCdiag, mul_zero]
    rw [hsum_s₁]
    simp only [add_mul, Finset.sum_add_distrib]
    rw [← hs₂_eq, ← add_zero ((∑ q ∈ s₁, _) + (∑ q ∈ s₂, _)), ← hs₃_eq]
    rw [← Finset.sum_union hdisj₁₂,
      ← Finset.sum_union (Finset.disjoint_union_left.mpr ⟨hdisj₁₃, hdisj₂₃⟩), hunion]
  have hRHS : fa u * fb v + fa v * fb u =
      ∑ p : Fin n × Fin n, (u p.1 * v p.2) * C p.1 p.2 := by
    rw [linearMap_apply_w fa u, linearMap_apply_w fb v, linearMap_apply_w fa v,
      linearMap_apply_w fb u]
    simp only [Finset.sum_mul_sum, C, Fintype.sum_prod_type]
    have hswap : (∑ x : Fin n, ∑ y : Fin n, (v x * fa (Pi.single x 1)) * (u y * fb (Pi.single y 1))) =
        ∑ y : Fin n, ∑ x : Fin n, (u y * v x) * (fa (Pi.single x 1) * fb (Pi.single y 1)) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by ring
    rw [hswap, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => by ring
  rw [hLHS, hsplit, hRHS]

lemma evalT_surjective {n z₀ d : ℕ} {T : Fin d → W n}
    (hT : LinearIndependent (ZMod 2) T) :
    Function.Surjective (evalT T : UpperTri n z₀ →ₗ[ZMod 2] (UpperTriIdx d → Z0 z₀)) := by
  obtain ⟨f, hf⟩ := dual_of_linearIndependent hT
  intro g
  have hsingle : ∀ (q₀ : UpperTriIdx d) (z : Z0 z₀),
      ∃ M₀ : UpperTri n z₀, evalT T M₀ = fun q => if q = q₀ then z else 0 := by
    intro q₀ z
    let a := q₀.1.1
    let b := q₀.1.2
    have hab : a ≠ b := ne_of_lt q₀.2
    refine ⟨fun p => (f a (Pi.single p.1.1 1) * f b (Pi.single p.1.2 1) +
        f a (Pi.single p.1.2 1) * f b (Pi.single p.1.1 1)) • z, ?_⟩
    ext q k
    change (ω _ (T q.1.1) (T q.1.2)) k = _
    rw [ω_rankOne (f a) (f b) z (T q.1.1) (T q.1.2)]
    rw [hf a q.1.1, hf b q.1.2, hf a q.1.2, hf b q.1.1]
    by_cases hq : q = q₀
    · subst hq
      simp [a, b, hab, hab.symm]
    · have hneq : (q.1.1, q.1.2) ≠ (a, b) := fun h => hq (Subtype.ext h)
      have h3 : ¬ (a = q.1.2 ∧ b = q.1.1) := by
        rintro ⟨ha2, hb1⟩
        have hlt1 : q.1.2 < q.1.1 := by
          rw [← ha2, ← hb1]
          exact q₀.2
        exact lt_asymm q.2 hlt1
      have hprod2 : (if a = q.1.2 then (1 : ZMod 2) else 0) *
          (if b = q.1.1 then 1 else 0) = 0 := by
        by_cases ha2 : a = q.1.2 <;> by_cases hb1 : b = q.1.1 <;> simp_all
      have hprod1 : (if a = q.1.1 then (1 : ZMod 2) else 0) *
          (if b = q.1.2 then 1 else 0) = 0 := by
        by_cases ha1 : a = q.1.1 <;> by_cases hb2 : b = q.1.2
        · exfalso; exact hneq (Prod.ext ha1.symm hb2.symm)
        · simp [ha1, hb2]
        · simp [ha1, hb2]
        · simp [ha1, hb2]
      simp [hq, hprod1, hprod2]
  choose Mfun hMfun using fun q₀ : UpperTriIdx d => hsingle q₀ (g q₀)
  refine ⟨∑ q₀ : UpperTriIdx d, Mfun q₀, ?_⟩
  rw [map_sum]
  ext q k
  simp only [Finset.sum_apply, hMfun]
  have hite : ∀ c : UpperTriIdx d, (if q = c then g c else 0) k = if q = c then g c k else 0 := by
    intro c
    split_ifs <;> rfl
  simp_rw [hite]
  simp

lemma card_ker_evalT {n z₀ d : ℕ} {T : Fin d → W n}
    (hT : LinearIndependent (ZMod 2) T) :
    Nat.card (LinearMap.ker (evalT T : UpperTri n z₀ →ₗ[ZMod 2] (UpperTriIdx d → Z0 z₀))) *
        2 ^ (z₀ * (d * (d - 1) / 2)) =
      Nat.card (UpperTri n z₀) := by
  classical
  have hsurj := evalT_surjective (n := n) (z₀ := z₀) (d := d) hT
  have heq1 : Nat.card (UpperTri n z₀ ⧸ LinearMap.ker (evalT T : UpperTri n z₀ →ₗ[ZMod 2] _)) =
      2 ^ (z₀ * (d * (d - 1) / 2)) := by
    rw [Nat.card_congr ((evalT T).quotKerEquivOfSurjective hsurj).toEquiv]
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, card_z0, card_upperTriIdx, ← pow_mul]
  rw [← heq1, mul_comm]
  have hlag := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
    (LinearMap.ker (evalT T : UpperTri n z₀ →ₗ[ZMod 2] (UpperTriIdx d → Z0 z₀))).toAddSubgroup
  exact hlag.symm

end BilinearForms

section ProbabilisticNonIsotropy

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Probabilistic existence of M : UpperTri n z0 admitting no d-dimensional isotropic subspace. -/
lemma exists_good_M (n z₀ d : ℕ) (hd : 1 ≤ d) (hnd : d ≤ n)
    (hprob : (∏ i ∈ Finset.range d, (2 ^ n - 2 ^ i)) <
      (∏ i ∈ Finset.range d, (2 ^ d - 2 ^ i)) * 2 ^ (z₀ * (d * (d - 1) / 2))) :
    ∃ M : UpperTri n z₀,
      ∀ S : Submodule (ZMod 2) (W n),
        (∀ x ∈ S, ∀ y ∈ S, ω M x y = 0) →
        Module.finrank (ZMod 2) S ≤ d - 1 := by
  classical
  by_contra hall
  push Not at hall
  choose S_M hS_iso hS_dim using hall
  let LIW := { T : Fin d → W n // LinearIndependent (ZMod 2) T }
  let I : Finset (UpperTri n z₀ × LIW) :=
    Finset.univ.filter (fun p => evalT p.2.1 p.1 = 0)
  let C_d := 2 ^ (z₀ * (d * (d - 1) / 2))
  have hcard_LIW : Fintype.card LIW = ∏ i ∈ Finset.range d, (2 ^ n - 2 ^ i) := by
    have hn : d ≤ Module.finrank (ZMod 2) (W n) := by
      simpa [Module.finrank_fintype_fun_eq_card] using hnd
    have hcl := card_linearIndependent (K := ZMod 2) (V := W n) hn
    rw [Nat.card_eq_fintype_card] at hcl
    rw [hcl]
    simp only [ZMod.card, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    rw [← Fin.prod_univ_eq_prod_range]
  have hupper : I.card * C_d =
      (∏ i ∈ Finset.range d, (2 ^ n - 2 ^ i)) * Fintype.card (UpperTri n z₀) := by
    have hsum : I.card = ∑ T : LIW,
        (Finset.univ.filter (fun M : UpperTri n z₀ => evalT T.1 M = 0)).card := by
      have hIeq : I.card = (Finset.univ.sigma (fun T : LIW =>
          Finset.univ.filter (fun M : UpperTri n z₀ => evalT T.1 M = 0))).card := by
        refine Finset.card_bij (fun p _ => ⟨p.2, p.1⟩) ?_ ?_ ?_
        · intro p hp
          simp only [I, Finset.mem_filter, Finset.mem_univ, true_and] at hp
          simp [hp]
        · rintro ⟨a₁, a₂⟩ _ ⟨b₁, b₂⟩ _ h
          simp only [Sigma.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          rfl
        · rintro ⟨T, M⟩ hq
          simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and] at hq
          exact ⟨(M, T), by simp [I, hq], rfl⟩
      rw [hIeq, Finset.card_sigma]
    rw [hsum, Finset.sum_mul]
    have hfiber : ∀ T : LIW,
        (Finset.univ.filter (fun M : UpperTri n z₀ => evalT T.1 M = 0)).card * C_d =
          Fintype.card (UpperTri n z₀) := by
      intro T
      have hker : (Finset.univ.filter (fun M : UpperTri n z₀ => evalT T.1 M = 0)).card =
          Nat.card (LinearMap.ker (evalT T.1 : UpperTri n z₀ →ₗ[ZMod 2] _)) := by
        rw [← Fintype.card_subtype, Nat.card_eq_fintype_card]
        exact Fintype.card_congr
          ⟨fun ⟨M, hM⟩ => ⟨M, LinearMap.mem_ker.mpr hM⟩,
           fun ⟨M, hM⟩ => ⟨M, LinearMap.mem_ker.mp hM⟩,
           fun _ => rfl, fun _ => rfl⟩
      rw [hker, ← Nat.card_eq_fintype_card (α := UpperTri n z₀)]
      exact card_ker_evalT (n := n) (z₀ := z₀) (d := d) T.2
    simp_rw [hfiber, Finset.sum_const, Finset.card_univ, smul_eq_mul, hcard_LIW]
  have hlower : Fintype.card (UpperTri n z₀) * (∏ i ∈ Finset.range d, (2 ^ d - 2 ^ i)) ≤ I.card := by
    have hsum : I.card = ∑ M : UpperTri n z₀,
        (Finset.univ.filter (fun T : LIW => evalT T.1 M = 0)).card := by
      have hIeq : I.card = (Finset.univ.sigma (fun M : UpperTri n z₀ =>
          Finset.univ.filter (fun T : LIW => evalT T.1 M = 0))).card := by
        refine Finset.card_bij (fun p _ => ⟨p.1, p.2⟩) ?_ ?_ ?_
        · intro p hp
          simp only [I, Finset.mem_filter, Finset.mem_univ, true_and] at hp
          simp [hp]
        · rintro ⟨a₁, a₂⟩ _ ⟨b₁, b₂⟩ _ h
          simp only [Sigma.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          rfl
        · rintro ⟨M, T⟩ hq
          simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and] at hq
          exact ⟨(M, T), by simp [I, hq], rfl⟩
      rw [hIeq, Finset.card_sigma]
    rw [hsum]
    have hfib_lb : ∀ M : UpperTri n z₀,
        (∏ i ∈ Finset.range d, (2 ^ d - 2 ^ i)) ≤
          (Finset.univ.filter (fun T : LIW => evalT T.1 M = 0)).card := by
      intro M
      let S := S_M M
      have hdS : d ≤ Module.finrank (ZMod 2) S := by
        have hdimM := hS_dim M
        dsimp [S]
        omega
      let LIS := { T' : Fin d → S // LinearIndependent (ZMod 2) T' }
      have hcard_LIS : (∏ i ∈ Finset.range d, (2 ^ d - 2 ^ i)) ≤ Fintype.card LIS := by
        have hcl := card_linearIndependent (K := ZMod 2) (V := S) hdS
        rw [Nat.card_eq_fintype_card] at hcl
        rw [hcl, ZMod.card, ← Fin.prod_univ_eq_prod_range]
        refine Finset.prod_le_prod' fun i _ => ?_
        exact Nat.sub_le_sub_right (Nat.pow_le_pow_right (by decide) hdS) _
      have hinj : Function.Injective (fun T' : LIS =>
          (⟨⟨fun i => (T'.1 i : W n),
              T'.2.map' S.subtype (Submodule.ker_subtype S)⟩,
            by
              ext q k
              change (ω M (T'.1 q.1.1 : W n) (T'.1 q.1.2 : W n)) k = 0
              rw [hS_iso M _ (T'.1 q.1.1).2 _ (T'.1 q.1.2).2]
              rfl⟩ :
            { T : LIW // evalT T.1 M = 0 })) := by
        intro T₁ T₂ h
        ext i k
        exact congrFun (congrArg (· i) (congrArg Subtype.val (congrArg Subtype.val h))) k
      calc
        ∏ i ∈ Finset.range d, (2 ^ d - 2 ^ i) ≤ Fintype.card LIS := hcard_LIS
        _ ≤ Fintype.card { T : LIW // evalT T.1 M = 0 } := Fintype.card_le_of_injective _ hinj
        _ = (Finset.univ.filter (fun T : LIW => evalT T.1 M = 0)).card := Fintype.card_subtype _
    calc
      Fintype.card (UpperTri n z₀) * (∏ i ∈ Finset.range d, (2 ^ d - 2 ^ i))
          = ∑ _M : UpperTri n z₀, (∏ i ∈ Finset.range d, (2 ^ d - 2 ^ i)) := by
              rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
      _ ≤ ∑ M : UpperTri n z₀, (Finset.univ.filter (fun T : LIW => evalT T.1 M = 0)).card :=
            Finset.sum_le_sum fun M _ => hfib_lb M
  have hcombined : Fintype.card (UpperTri n z₀) *
      ((∏ i ∈ Finset.range d, (2 ^ d - 2 ^ i)) * C_d) ≤
      Fintype.card (UpperTri n z₀) * (∏ i ∈ Finset.range d, (2 ^ n - 2 ^ i)) := by
    calc
      Fintype.card (UpperTri n z₀) * ((∏ i ∈ Finset.range d, (2 ^ d - 2 ^ i)) * C_d)
          = (Fintype.card (UpperTri n z₀) * (∏ i ∈ Finset.range d, (2 ^ d - 2 ^ i))) * C_d := by
              ring
      _ ≤ I.card * C_d := Nat.mul_le_mul_right C_d hlower
      _ = Fintype.card (UpperTri n z₀) * (∏ i ∈ Finset.range d, (2 ^ n - 2 ^ i)) := by
              rw [hupper, mul_comm]
  have hpos : 0 < Fintype.card (UpperTri n z₀) := Fintype.card_pos_iff.mpr ⟨0⟩
  have hle := Nat.le_of_mul_le_mul_left hcombined hpos
  exact not_le_of_gt hprob hle

lemma exists_ne_zero_ω {n z₀ d : ℕ} (M : UpperTri n z₀) (hd : 1 ≤ d) (hnd : d ≤ n)
    (hiso : ∀ S : Submodule (ZMod 2) (W n),
      (∀ x ∈ S, ∀ y ∈ S, ω M x y = 0) → Module.finrank (ZMod 2) S ≤ d - 1) :
    ∃ u v : W n, ω M u v ≠ 0 := by
  by_contra h
  push Not at h
  have htop := hiso ⊤ (fun x _ y _ => h x y)
  have hdim : Module.finrank (ZMod 2) (⊤ : Submodule (ZMod 2) (W n)) = n := by
    rw [finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  rw [hdim] at htop
  omega

end ProbabilisticNonIsotropy

section SemidirectTwoGroup

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Underlying 2-group M(f) on W n x W n x Z0 z0 x Z0 z0. -/
@[ext]
structure MGrp {n z₀ : ℕ} (M : UpperTri n z₀) : Type where
  u : W n
  v : W n
  a : Z0 z₀
  b : Z0 z₀
  deriving DecidableEq

namespace MGrp

variable {n z₀ : ℕ} {M : UpperTri n z₀}

instance : Group (MGrp M) where
  mul x y :=
    { u := x.u + y.u
      v := x.v + y.v
      a := x.a + y.a + fBil M x.u y.v
      b := x.b + y.b + fBil M x.v y.u }
  one := { u := 0, v := 0, a := 0, b := 0 }
  inv x :=
    { u := x.u
      v := x.v
      a := x.a + fBil M x.u x.v
      b := x.b + fBil M x.v x.u }
  mul_assoc x y z := by
    refine MGrp.ext (add_assoc _ _ _) (add_assoc _ _ _) ?_ ?_
    · change x.a + y.a + fBil M x.u y.v + z.a + fBil M (x.u + y.u) z.v =
          x.a + (y.a + z.a + fBil M y.u z.v) + fBil M x.u (y.v + z.v)
      rw [fBil_add_left, fBil_add_right]; abel
    · change x.b + y.b + fBil M x.v y.u + z.b + fBil M (x.v + y.v) z.u =
          x.b + (y.b + z.b + fBil M y.v z.u) + fBil M x.v (y.u + z.u)
      rw [fBil_add_left, fBil_add_right]; abel
  one_mul x := by
    refine MGrp.ext (zero_add _) (zero_add _) ?_ ?_
    · change 0 + x.a + fBil M 0 x.v = x.a
      rw [zero_add, fBil_zero_left, add_zero]
    · change 0 + x.b + fBil M 0 x.u = x.b
      rw [zero_add, fBil_zero_left, add_zero]
  mul_one x := by
    refine MGrp.ext (add_zero _) (add_zero _) ?_ ?_
    · change x.a + 0 + fBil M x.u 0 = x.a
      rw [add_zero, fBil_zero_right, add_zero]
    · change x.b + 0 + fBil M x.v 0 = x.b
      rw [add_zero, fBil_zero_right, add_zero]
  inv_mul_cancel x := by
    refine MGrp.ext ?_ ?_ ?_ ?_
    · exact w_add_self x.u
    · exact w_add_self x.v
    · have h1 : x.a + fBil M x.u x.v + x.a + fBil M x.u x.v =
          (x.a + x.a) + (fBil M x.u x.v + fBil M x.u x.v) := by abel
      exact h1.trans (by rw [z0_add_self, z0_add_self, add_zero]; rfl)
    · have h1 : x.b + fBil M x.v x.u + x.b + fBil M x.v x.u =
          (x.b + x.b) + (fBil M x.v x.u + fBil M x.v x.u) := by abel
      exact h1.trans (by rw [z0_add_self, z0_add_self, add_zero]; rfl)

@[simp] lemma mul_u (x y : MGrp M) : (x * y).u = x.u + y.u := rfl
@[simp] lemma mul_v (x y : MGrp M) : (x * y).v = x.v + y.v := rfl
@[simp] lemma mul_a (x y : MGrp M) : (x * y).a = x.a + y.a + fBil M x.u y.v := rfl
@[simp] lemma mul_b (x y : MGrp M) : (x * y).b = x.b + y.b + fBil M x.v y.u := rfl
@[simp] lemma one_u : (1 : MGrp M).u = 0 := rfl
@[simp] lemma one_v : (1 : MGrp M).v = 0 := rfl
@[simp] lemma one_a : (1 : MGrp M).a = 0 := rfl
@[simp] lemma one_b : (1 : MGrp M).b = 0 := rfl
@[simp] lemma inv_u (x : MGrp M) : x⁻¹.u = x.u := rfl
@[simp] lemma inv_v (x : MGrp M) : x⁻¹.v = x.v := rfl
@[simp] lemma inv_a (x : MGrp M) : x⁻¹.a = x.a + fBil M x.u x.v := rfl
@[simp] lemma inv_b (x : MGrp M) : x⁻¹.b = x.b + fBil M x.v x.u := rfl

lemma mul_comm_of_uv_zero {x y : MGrp M} (hx : x.u = 0 ∧ x.v = 0) : x * y = y * x := by
  refine MGrp.ext ?_ ?_ ?_ ?_ <;> simp [hx.1, hx.2, add_comm]

def equivProd (M : UpperTri n z₀) : MGrp M ≃ W n × W n × Z0 z₀ × Z0 z₀ where
  toFun x := (x.u, x.v, x.a, x.b)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv x := by cases x; rfl
  right_inv p := by rcases p with ⟨_, _, _, _⟩; rfl

instance : Fintype (MGrp M) := Fintype.ofEquiv _ (equivProd M).symm

lemma card_MGrp (M : UpperTri n z₀) : Nat.card (MGrp M) = 2 ^ (2 * n + 2 * z₀) := by
  rw [Nat.card_eq_fintype_card, Fintype.card_congr (equivProd M)]
  simp only [Fintype.card_prod, card_w]
  ring

/-- Involution swapping (u, v, a, b) -> (v, u, b, a). -/
def swapAut (M : UpperTri n z₀) : MulAut (MGrp M) where
  toFun x := ⟨x.v, x.u, x.b, x.a⟩
  invFun x := ⟨x.v, x.u, x.b, x.a⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl
  map_mul' x y := by refine MGrp.ext ?_ ?_ ?_ ?_ <;> simp

@[simp] lemma swapAut_u (x : MGrp M) : (swapAut M x).u = x.v := rfl
@[simp] lemma swapAut_v (x : MGrp M) : (swapAut M x).v = x.u := rfl
@[simp] lemma swapAut_a (x : MGrp M) : (swapAut M x).a = x.b := rfl
@[simp] lemma swapAut_b (x : MGrp M) : (swapAut M x).b = x.a := rfl

lemma swapAut_sq (M : UpperTri n z₀) : swapAut M * swapAut M = 1 := by
  ext x <;> rfl

/-- Action of Multiplicative (ZMod 2) on MGrp M by swapAut. -/
def actionHom (M : UpperTri n z₀) : Multiplicative (ZMod 2) →* MulAut (MGrp M) where
  toFun e := if Multiplicative.toAdd e = 0 then 1 else swapAut M
  map_one' := by simp
  map_mul' e₁ e₂ := by
    have ha : Multiplicative.toAdd (e₁ * e₂) =
        Multiplicative.toAdd e₁ + Multiplicative.toAdd e₂ := rfl
    rcases zmod2_cases (Multiplicative.toAdd e₁) with h₁ | h₁ <;>
      rcases zmod2_cases (Multiplicative.toAdd e₂) with h₂ | h₂
    · simp [ha, h₁, h₂]
    · simp [ha, h₁, h₂]
    · simp [ha, h₁, h₂]
    · have h11 : (1 : ZMod 2) + 1 = 0 := zmod2_add_self 1
      simp [ha, h₁, h₂, h11, swapAut_sq]

lemma actionHom_eq_uv_of_u_eq_v (e : Multiplicative (ZMod 2)) (z : MGrp M) (h : z.u = z.v) :
    (actionHom M e z).u = z.u ∧ (actionHom M e z).v = z.v := by
  simp only [actionHom, MonoidHom.coe_mk, OneHom.coe_mk]
  split_ifs
  · simp
  · exact ⟨h.symm, h⟩

lemma actionHom_mul_self_of_uv_zero (e : Multiplicative (ZMod 2)) (z : MGrp M)
    (hu : z.u = 0) (hv : z.v = 0) :
    (z * actionHom M e z).u = 0 ∧
    (z * actionHom M e z).v = 0 ∧
    (z * actionHom M e z).a = (z * actionHom M e z).b := by
  simp only [actionHom, MonoidHom.coe_mk, OneHom.coe_mk]
  split_ifs
  · refine ⟨by simp [hu], by simp [hv], ?_⟩
    simp only [mul_a, mul_b, MulAut.one_apply, hu, hv, fBil_zero_left, add_zero]
    rw [z0_add_self, z0_add_self]
  · refine ⟨by simp [hu, hv], by simp [hu, hv], ?_⟩
    simp only [mul_a, mul_b, swapAut_u, swapAut_v, swapAut_a, swapAut_b, hu, hv,
      fBil_zero_left, add_zero]
    exact add_comm z.a z.b

lemma actionHom_fix_of_uv_zero_ab_eq (e : Multiplicative (ZMod 2)) (z : MGrp M)
    (hu : z.u = 0) (hv : z.v = 0) (hab : z.a = z.b) :
    actionHom M e z = z := by
  simp only [actionHom, MonoidHom.coe_mk, OneHom.coe_mk]
  split_ifs
  · rfl
  · refine MGrp.ext ?_ ?_ ?_ ?_ <;> simp [hu, hv, hab]

end MGrp

/-- Semidirect product 2-group G = M(f) x| C_2. -/
abbrev G76 {n z₀ : ℕ} (M : UpperTri n z₀) : Type :=
  MGrp M ⋊[MGrp.actionHom M] Multiplicative (ZMod 2)

section G76Properties

open scoped commutatorElement

variable {n z₀ : ℕ} (M : UpperTri n z₀)

instance : Fintype (G76 M) :=
  Fintype.ofEquiv _ (SemidirectProduct.equivProd).symm

lemma card_G76 : Nat.card (G76 M) = 2 ^ (2 * n + 2 * z₀ + 1) := by
  rw [SemidirectProduct.card, MGrp.card_MGrp, Nat.card_eq_fintype_card]
  have hc : Fintype.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Fintype.card_congr Multiplicative.toAdd, ZMod.card]
  rw [hc]
  ring

lemma isPGroup_G76 : IsPGroup 2 (G76 M) :=
  IsPGroup.of_card (card_G76 M)

/-- Nilpotency class of G76 M is at most 4. -/
lemma nilpotencyClass_G76_le_four :
    Group.IsNilpotent (G76 M) ∧ Group.nilpotencyClass (G76 M) ≤ 4 := by
  have hnil : Group.IsNilpotent (G76 M) := (isPGroup_G76 M).isNilpotent
  refine ⟨hnil, ?_⟩
  rw [← Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le]
  let L₁ : Subgroup (G76 M) :=
    { carrier := { g | g.right = 1 ∧ g.left.u = g.left.v }
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_ofPred_eq, SemidirectProduct.mul_right, hx.1, hy.1, mul_one,
          SemidirectProduct.mul_left, map_one, MulAut.one_apply, MGrp.mul_u, MGrp.mul_v,
          hx.2, hy.2, and_self]
      one_mem' := by simp
      inv_mem' := by
        intro x hx
        simp only [Set.mem_ofPred_eq, SemidirectProduct.inv_right, hx.1, inv_one,
          SemidirectProduct.inv_left, map_one, MulAut.one_apply, MGrp.inv_u, MGrp.inv_v,
          hx.2, and_self] }
  let L₂ : Subgroup (G76 M) :=
    { carrier := { g | g.right = 1 ∧ g.left.u = 0 ∧ g.left.v = 0 }
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_ofPred_eq, SemidirectProduct.mul_right, hx.1, hy.1, mul_one,
          SemidirectProduct.mul_left, map_one, MulAut.one_apply, MGrp.mul_u, MGrp.mul_v,
          hx.2.1, hy.2.1, hx.2.2, hy.2.2, add_zero, and_self]
      one_mem' := by simp
      inv_mem' := by
        intro x hx
        simp only [Set.mem_ofPred_eq, SemidirectProduct.inv_right, hx.1, inv_one,
          SemidirectProduct.inv_left, map_one, MulAut.one_apply, MGrp.inv_u, MGrp.inv_v,
          hx.2.1, hx.2.2, and_self] }
  let L₃ : Subgroup (G76 M) :=
    { carrier := { g | g.right = 1 ∧ g.left.u = 0 ∧ g.left.v = 0 ∧ g.left.a = g.left.b }
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_ofPred_eq, SemidirectProduct.mul_right, hx.1, hy.1, mul_one,
          SemidirectProduct.mul_left, map_one, MulAut.one_apply, MGrp.mul_u, MGrp.mul_v,
          MGrp.mul_a, MGrp.mul_b, hx.2.1, hy.2.1, hx.2.2.1, hy.2.2.1, add_zero,
          fBil_zero_left, hx.2.2.2, hy.2.2.2, and_self]
      one_mem' := by simp
      inv_mem' := by
        intro x hx
        simp only [Set.mem_ofPred_eq, SemidirectProduct.inv_right, hx.1, inv_one,
          SemidirectProduct.inv_left, map_one, MulAut.one_apply, MGrp.inv_u, MGrp.inv_v,
          MGrp.inv_a, MGrp.inv_b, hx.2.1, hx.2.2.1, fBil_zero_left, add_zero,
          hx.2.2.2, and_self] }
  have h1 : Subgroup.lowerCentralSeries (⊤ : Subgroup (G76 M)) 1 ≤ L₁ := by
    rw [Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_zero, Subgroup.commutator_le]
    intro x _ y _
    have hcomm_r : ⁅x, y⁆.right = 1 := by
      change (x * y * x⁻¹ * y⁻¹).right = 1
      simp only [SemidirectProduct.mul_right, SemidirectProduct.inv_right]
      rw [mul_comm x.right y.right]
      group
    have huv_hom : ∀ a b : G76 M, (a * b).left.u + (a * b).left.v =
        (a.left.u + a.left.v) + (b.left.u + b.left.v) := by
      intro a b
      simp only [SemidirectProduct.mul_left, MGrp.mul_u, MGrp.mul_v]
      have hact : (MGrp.actionHom M a.right b.left).u + (MGrp.actionHom M a.right b.left).v =
          b.left.u + b.left.v := by
        simp only [MGrp.actionHom, MonoidHom.coe_mk, OneHom.coe_mk]
        split_ifs
        · simp
        · simp [add_comm]
      have hre : a.left.u + (MGrp.actionHom M a.right b.left).u +
            (a.left.v + (MGrp.actionHom M a.right b.left).v) =
          (a.left.u + a.left.v) +
            ((MGrp.actionHom M a.right b.left).u + (MGrp.actionHom M a.right b.left).v) := by abel
      rw [hre, hact]
    have huv_inv : ∀ a : G76 M, a⁻¹.left.u + a⁻¹.left.v = a.left.u + a.left.v := by
      intro a
      simp only [SemidirectProduct.inv_left, MGrp.actionHom, MonoidHom.coe_mk, OneHom.coe_mk]
      split_ifs <;> simp [add_comm]
    have hsum_zero : ⁅x, y⁆.left.u + ⁅x, y⁆.left.v = 0 := by
      change (x * y * x⁻¹ * y⁻¹).left.u + (x * y * x⁻¹ * y⁻¹).left.v = 0
      rw [huv_hom, huv_hom, huv_hom, huv_inv, huv_inv]
      have hre : (x.left.u + x.left.v + (y.left.u + y.left.v) + (x.left.u + x.left.v) +
          (y.left.u + y.left.v)) =
          ((x.left.u + x.left.u) + (x.left.v + x.left.v)) +
          ((y.left.u + y.left.u) + (y.left.v + y.left.v)) := by abel
      rw [hre, w_add_self x.left.u, w_add_self x.left.v, w_add_self y.left.u,
        w_add_self y.left.v]
      simp
    exact ⟨hcomm_r, w_eq_of_add_eq_zero hsum_zero⟩
  have h2 : Subgroup.lowerCentralSeries (⊤ : Subgroup (G76 M)) 2 ≤ L₂ := by
    rw [Subgroup.lowerCentralSeries_succ, Subgroup.commutator_le]
    intro x hx y _
    have hx' := h1 hx
    change ⁅x, y⁆ ∈ L₂
    have hx_eq : x = SemidirectProduct.inl x.left := by
      ext <;> simp [hx'.1]
    have hconj : y * x⁻¹ * y⁻¹ =
        SemidirectProduct.inl (y.left * MGrp.actionHom M y.right x.left⁻¹ * y.left⁻¹) := by
      conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right y, hx_eq, ← map_inv]
      calc
        (SemidirectProduct.inl y.left * SemidirectProduct.inr y.right) *
            SemidirectProduct.inl x.left⁻¹ *
            (SemidirectProduct.inl y.left * SemidirectProduct.inr y.right)⁻¹
            = SemidirectProduct.inl y.left *
                (SemidirectProduct.inr y.right * SemidirectProduct.inl x.left⁻¹ *
                  SemidirectProduct.inr y.right⁻¹) * SemidirectProduct.inl y.left⁻¹ := by
                simp only [map_inv]
                group
        _ = SemidirectProduct.inl y.left *
              SemidirectProduct.inl (MGrp.actionHom M y.right x.left⁻¹) *
              SemidirectProduct.inl y.left⁻¹ := by
              rw [← SemidirectProduct.inl_aut]
        _ = SemidirectProduct.inl (y.left * MGrp.actionHom M y.right x.left⁻¹ * y.left⁻¹) := by
              simp only [← map_mul]
    have hcomm_eq : ⁅x, y⁆ =
        SemidirectProduct.inl (x.left * (y.left * MGrp.actionHom M y.right x.left⁻¹ * y.left⁻¹)) := by
      change x * y * x⁻¹ * y⁻¹ = _
      have h1' : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
      rw [h1', hconj]
      conv_lhs => rw [hx_eq]
      rw [← map_mul]
      simp only [SemidirectProduct.left_inl]
    rw [hcomm_eq]
    have hact_uv := MGrp.actionHom_eq_uv_of_u_eq_v (M := M) y.right x.left⁻¹ hx'.2
    refine ⟨SemidirectProduct.right_inl _, ?_, ?_⟩
    · simp only [SemidirectProduct.left_inl, MGrp.mul_u, MGrp.inv_u, hact_uv.1]
      have hre : x.left.u + (y.left.u + x.left.u + y.left.u) =
          (x.left.u + x.left.u) + (y.left.u + y.left.u) := by abel
      rw [hre, w_add_self, w_add_self, add_zero]
    · simp only [SemidirectProduct.left_inl, MGrp.mul_v, MGrp.inv_v, hact_uv.2]
      have hre : x.left.v + (y.left.v + x.left.v + y.left.v) =
          (x.left.v + x.left.v) + (y.left.v + y.left.v) := by abel
      rw [hre, w_add_self, w_add_self, add_zero]
  have hconj_central : ∀ (z : MGrp M) (g : G76 M), z.u = 0 → z.v = 0 →
      g * SemidirectProduct.inl z * g⁻¹ = SemidirectProduct.inl (MGrp.actionHom M g.right z) := by
    intro z g hzu hzv
    conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right g]
    have hact_uv : (MGrp.actionHom M g.right z).u = 0 ∧ (MGrp.actionHom M g.right z).v = 0 := by
      have huv := MGrp.actionHom_eq_uv_of_u_eq_v (M := M) g.right z (hzu.trans hzv.symm)
      exact ⟨huv.1.trans hzu, huv.2.trans hzv⟩
    calc
      (SemidirectProduct.inl g.left * SemidirectProduct.inr g.right) * SemidirectProduct.inl z *
          (SemidirectProduct.inl g.left * SemidirectProduct.inr g.right)⁻¹
          = SemidirectProduct.inl g.left *
              (SemidirectProduct.inr g.right * SemidirectProduct.inl z *
                SemidirectProduct.inr g.right⁻¹) * SemidirectProduct.inl g.left⁻¹ := by
              simp only [map_inv]
              group
      _ = SemidirectProduct.inl g.left * SemidirectProduct.inl (MGrp.actionHom M g.right z) *
            SemidirectProduct.inl g.left⁻¹ := by
            rw [← SemidirectProduct.inl_aut]
      _ = SemidirectProduct.inl (g.left * MGrp.actionHom M g.right z * g.left⁻¹) := by
            simp only [← map_mul]
      _ = SemidirectProduct.inl (MGrp.actionHom M g.right z * g.left * g.left⁻¹) := by
            rw [MGrp.mul_comm_of_uv_zero hact_uv]
      _ = SemidirectProduct.inl (MGrp.actionHom M g.right z) := by
            simp
  have h3 : Subgroup.lowerCentralSeries (⊤ : Subgroup (G76 M)) 3 ≤ L₃ := by
    rw [Subgroup.lowerCentralSeries_succ, Subgroup.commutator_le]
    intro x hx y _
    have hx' := h2 hx
    change ⁅x, y⁆ ∈ L₃
    have hx_eq : x = SemidirectProduct.inl x.left := by
      ext <;> simp [hx'.1]
    have hx_inv : x.left⁻¹ = x.left := by
      refine MGrp.ext rfl rfl ?_ ?_ <;> simp [hx'.2.1, hx'.2.2]
    have hcomm_eq : ⁅x, y⁆ = SemidirectProduct.inl (x.left * MGrp.actionHom M y.right x.left) := by
      change x * y * x⁻¹ * y⁻¹ = _
      have h1' : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
      rw [h1']
      conv_lhs => rw [hx_eq]
      rw [← map_inv, hx_inv, hconj_central x.left y hx'.2.1 hx'.2.2, ← map_mul]
    rw [hcomm_eq]
    have hprops := MGrp.actionHom_mul_self_of_uv_zero (M := M) y.right x.left hx'.2.1 hx'.2.2
    exact ⟨SemidirectProduct.right_inl _, hprops.1, hprops.2.1, hprops.2.2⟩
  rw [Subgroup.lowerCentralSeries_succ, eq_bot_iff, Subgroup.commutator_le]
  intro x hx y _
  have hx' := h3 hx
  change ⁅x, y⁆ = 1
  have hx_eq : x = SemidirectProduct.inl x.left := by ext <;> simp [hx'.1]
  have hx_inv : x.left⁻¹ = x.left := by
    refine MGrp.ext rfl rfl ?_ ?_ <;> simp [hx'.2.1, hx'.2.2.1]
  have hact_fix : MGrp.actionHom M y.right x.left = x.left :=
    MGrp.actionHom_fix_of_uv_zero_ab_eq (M := M) y.right x.left hx'.2.1 hx'.2.2.1 hx'.2.2.2
  have h1' : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
  change x * y * x⁻¹ * y⁻¹ = 1
  rw [h1']
  conv_lhs => rw [hx_eq]
  rw [← map_inv, hx_inv, hconj_central x.left y hx'.2.1 hx'.2.2.1, hact_fix, ← map_mul]
  have hxx : x.left * x.left = 1 := by
    refine MGrp.ext (w_add_self _) (w_add_self _) ?_ ?_ <;>
      simp [hx'.2.1, hx'.2.2.1, z0_add_self]
  rw [hxx, map_one]

/-- Whenever the alternating form `ω M` is not identically zero, `G76 M` has exact nilpotency
class `4`. -/
theorem nilpotencyClass_G76_eq_four (hω : ∃ u v : W n, ω M u v ≠ 0) :
    Group.nilpotencyClass (G76 M) = 4 := by
  obtain ⟨u, v, huv⟩ := hω
  obtain ⟨_, hle4⟩ := nilpotencyClass_G76_le_four M
  refine le_antisymm hle4 ?_
  by_contra hlt4
  have hle3 : Group.nilpotencyClass (G76 M) ≤ 3 := by omega
  have hbot : Subgroup.lowerCentralSeries (⊤ : Subgroup (G76 M)) 3 = ⊥ :=
    Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr hle3
  let gu : G76 M := SemidirectProduct.inl ⟨u, 0, 0, 0⟩
  let gv : G76 M := SemidirectProduct.inl ⟨v, 0, 0, 0⟩
  let s : G76 M := SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2))
  let z1 : G76 M := ⁅gu, s⁆
  let z2 : G76 M := ⁅z1, gv⁆
  let z3 : G76 M := ⁅z2, s⁆
  have hz1 : z1 ∈ Subgroup.lowerCentralSeries (⊤ : Subgroup (G76 M)) 1 := by
    rw [Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_zero]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hz2 : z2 ∈ Subgroup.lowerCentralSeries (⊤ : Subgroup (G76 M)) 2 := by
    rw [Subgroup.lowerCentralSeries_succ]
    exact Subgroup.commutator_mem_commutator hz1 (Subgroup.mem_top _)
  have hz3 : z3 ∈ Subgroup.lowerCentralSeries (⊤ : Subgroup (G76 M)) 3 := by
    rw [Subgroup.lowerCentralSeries_succ]
    exact Subgroup.commutator_mem_commutator hz2 (Subgroup.mem_top _)
  have hz3_one : z3 = 1 := Subgroup.mem_bot.mp (hbot ▸ hz3)
  have hact1 : ∀ m : MGrp M,
      MGrp.actionHom M (Multiplicative.ofAdd (1 : ZMod 2)) m = MGrp.swapAut M m := by
    intro m
    simp only [MGrp.actionHom, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
    have h10 : (1 : ZMod 2) ≠ 0 := by decide
    simp [h10]
  have hz1_eq : z1 = SemidirectProduct.inl ⟨u, u, fBil M u u, 0⟩ := by
    change gu * s * gu⁻¹ * s⁻¹ = _
    have hgrp : gu * s * gu⁻¹ * s⁻¹ = gu * (s * gu⁻¹ * s⁻¹) := by group
    rw [hgrp]
    dsimp [gu, s]
    rw [← map_inv, ← map_inv, ← SemidirectProduct.inl_aut, hact1, ← map_mul]
    congr 1
    refine MGrp.ext ?_ ?_ ?_ ?_ <;> simp
  have hz2_eq : z2 = SemidirectProduct.inl ⟨0, 0, fBil M v u, fBil M u v⟩ := by
    change z1 * gv * z1⁻¹ * gv⁻¹ = _
    rw [hz1_eq]
    dsimp [gv]
    simp only [← map_inv, ← map_mul]
    congr 1
    refine MGrp.ext ?_ ?_ ?_ ?_
    · have h : u + v + u + v = (u + u) + (v + v) := by abel
      simpa [w_add_self] using h
    · simp [w_add_self]
    · simp only [MGrp.mul_a, MGrp.inv_a, MGrp.mul_u, MGrp.inv_u, MGrp.inv_v,
        fBil_zero_right, fBil_add_left, add_zero]
      have h : fBil M u u + (fBil M u u + fBil M u u) + (fBil M u u + fBil M v u) =
          (fBil M u u + fBil M u u) + (fBil M u u + fBil M u u) + fBil M v u := by abel
      simpa [z0_add_self] using h
    · simp only [MGrp.mul_b, MGrp.inv_b, MGrp.mul_v, MGrp.inv_u, MGrp.inv_v,
        fBil_zero_left, add_zero, zero_add]
      have h : fBil M u v + fBil M u u + fBil M u u =
          fBil M u v + (fBil M u u + fBil M u u) := by abel
      simpa [z0_add_self] using h
  have hz3_eq : z3 = SemidirectProduct.inl ⟨0, 0, fBil M v u + fBil M u v,
      fBil M u v + fBil M v u⟩ := by
    change z2 * s * z2⁻¹ * s⁻¹ = _
    have hgrp : z2 * s * z2⁻¹ * s⁻¹ = z2 * (s * z2⁻¹ * s⁻¹) := by group
    rw [hgrp, hz2_eq]
    dsimp [s]
    rw [← map_inv, ← map_inv, ← SemidirectProduct.inl_aut, hact1, ← map_mul]
    congr 1
    refine MGrp.ext ?_ ?_ ?_ ?_ <;> simp
  have ha_zero : fBil M v u + fBil M u v = 0 := by
    have h := congrArg (fun g : G76 M => g.left.a) (hz3_eq.symm.trans hz3_one)
    simpa using h
  apply huv
  rw [ω_symm]
  exact ha_zero

/-- Elementary abelian subgroup B of order 2^(n + 2 z0) inside MGrp M. -/
def BSub : Subgroup (MGrp M) where
  carrier := { x | x.v = 0 }
  mul_mem' := by
    intro x y hx hy
    change x.v = 0 at hx
    change y.v = 0 at hy
    change x.v + y.v = 0
    rw [hx, hy, add_zero]
  one_mem' := rfl
  inv_mem' := by
    intro x hx
    exact hx

lemma BSub_comm : IsMulCommutative (BSub M) := by
  refine IsMulCommutative.of_setLike_mul_comm fun x hx y hy => ?_
  change x.v = 0 at hx
  change y.v = 0 at hy
  refine MGrp.ext ?_ ?_ ?_ ?_ <;> simp [hx, hy, add_comm]

lemma BSub_exp2 : ∀ x ∈ BSub M, x ^ 2 = 1 := by
  intro x hx
  change x.v = 0 at hx
  rw [sq]
  refine MGrp.ext ?_ ?_ ?_ ?_
  · exact w_add_self x.u
  · simp [hx]
  · simp [hx, z0_add_self]
  · simp [hx, z0_add_self]

def equivBSub : BSub M ≃ W n × Z0 z₀ × Z0 z₀ where
  toFun x := (x.1.u, x.1.a, x.1.b)
  invFun p := ⟨⟨p.1, 0, p.2.1, p.2.2⟩, rfl⟩
  left_inv x := Subtype.ext (MGrp.ext rfl x.2.symm rfl rfl)
  right_inv p := by rcases p with ⟨_, _, _⟩; rfl

lemma card_BSub : Nat.card (BSub M) = 2 ^ (n + 2 * z₀) := by
  rw [Nat.card_congr (equivBSub M), Nat.card_eq_fintype_card]
  simp only [Fintype.card_prod, card_w]
  ring

/-- Elementary abelian subgroup B inside G76 M. -/
def elemAbelianSubgroup : Subgroup (G76 M) :=
  (BSub M).map SemidirectProduct.inl

lemma elemAbelianSubgroup_props :
    IsMulCommutative (elemAbelianSubgroup M) ∧
    (∀ g ∈ elemAbelianSubgroup M, g ^ 2 = 1) ∧
    Nat.card (elemAbelianSubgroup M) = 2 ^ (n + 2 * z₀) := by
  have : IsMulCommutative (BSub M) := BSub_comm M
  refine ⟨Subgroup.map_isMulCommutative (BSub M) SemidirectProduct.inl, ?_, ?_⟩
  · intro g hg
    rcases Subgroup.mem_map.mp hg with ⟨x, hx, rfl⟩
    rw [← map_pow, BSub_exp2 M x hx, map_one]
  · have hinj : Function.Injective (fun x : BSub M =>
        (⟨SemidirectProduct.inl x.1, Subgroup.mem_map_of_mem _ x.2⟩ : elemAbelianSubgroup M)) := by
      intro x y h
      exact Subtype.ext (SemidirectProduct.inl_injective (congrArg Subtype.val h))
    have hbij : Function.Bijective (fun x : BSub M =>
        (⟨SemidirectProduct.inl x.1, Subgroup.mem_map_of_mem _ x.2⟩ : elemAbelianSubgroup M)) := by
      refine ⟨hinj, ?_⟩
      rintro ⟨g, hg⟩
      rcases Subgroup.mem_map.mp hg with ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    rw [← Nat.card_congr (Equiv.ofBijective _ hbij), card_BSub M]

/-- Upper bound on the order of any normal abelian subgroup of G76 M. -/
lemma normal_abelian_card_le {d : ℕ} (hd : 1 ≤ d) (hnd : d ≤ n)
    (hiso : ∀ S : Submodule (ZMod 2) (W n),
      (∀ x ∈ S, ∀ y ∈ S, ω M x y = 0) → Module.finrank (ZMod 2) S ≤ d - 1)
    (H : Subgroup (G76 M)) (hNorm : H.Normal) (hComm : IsMulCommutative H) :
    Nat.card H ≤ 2 ^ (2 * (d - 1) + 2 * z₀) := by
  have := hComm
  have hright_one : ∀ h ∈ H, h.right = 1 := by
    intro h hh
    by_contra hne
    have htoAdd_ne : Multiplicative.toAdd h.right ≠ 0 := by
      intro hz
      exact hne (Multiplicative.toAdd.injective hz)
    have hact_eq : MGrp.actionHom M h.right = MGrp.swapAut M := by
      simp only [MGrp.actionHom, MonoidHom.coe_mk, OneHom.coe_mk, htoAdd_ne, ↓reduceIte]
    let g : W n → MGrp M := fun u => ⟨u, 0, 0, 0⟩
    let k : W n → G76 M := fun u =>
      h * SemidirectProduct.inl (g u) * h⁻¹ * (SemidirectProduct.inl (g u))⁻¹
    have hk_mem : ∀ u, k u ∈ H := by
      intro u
      have h1 : SemidirectProduct.inl (g u) * h⁻¹ * (SemidirectProduct.inl (g u))⁻¹ ∈ H :=
        hNorm.conj_mem _ (H.inv_mem hh) (SemidirectProduct.inl (g u))
      simpa only [k, mul_assoc] using H.mul_mem hh h1
    let m : W n → MGrp M := fun u =>
      h.left * MGrp.swapAut M (g u) * h.left⁻¹ * (g u)⁻¹
    have hk_eq : ∀ u, k u = SemidirectProduct.inl (m u) := by
      intro u
      have hconj : h * SemidirectProduct.inl (g u) * h⁻¹ =
          SemidirectProduct.inl (h.left * MGrp.swapAut M (g u) * h.left⁻¹) := by
        conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right h]
        calc
          (SemidirectProduct.inl h.left * SemidirectProduct.inr h.right) *
              SemidirectProduct.inl (g u) *
              (SemidirectProduct.inl h.left * SemidirectProduct.inr h.right)⁻¹
              = SemidirectProduct.inl h.left *
                  (SemidirectProduct.inr h.right * SemidirectProduct.inl (g u) *
                    SemidirectProduct.inr h.right⁻¹) *
                  SemidirectProduct.inl h.left⁻¹ := by
                  simp only [map_inv]
                  group
          _ = SemidirectProduct.inl h.left *
                SemidirectProduct.inl (MGrp.actionHom M h.right (g u)) *
                SemidirectProduct.inl h.left⁻¹ := by
                rw [← SemidirectProduct.inl_aut]
          _ = SemidirectProduct.inl (h.left * MGrp.swapAut M (g u) * h.left⁻¹) := by
                rw [hact_eq, ← map_mul, ← map_mul]
      rw [show k u = (h * SemidirectProduct.inl (g u) * h⁻¹) * (SemidirectProduct.inl (g u))⁻¹ from rfl]
      rw [hconj, ← map_inv, ← map_mul]
    have hmu : ∀ u, (m u).u = u := by
      intro u
      simp only [m, g, MGrp.mul_u, MGrp.inv_u, MGrp.swapAut_u, add_zero]
      rw [w_add_self, zero_add]
    have hmv : ∀ u, (m u).v = u := by
      intro u
      simp only [m, g, MGrp.mul_v, MGrp.inv_v, MGrp.swapAut_v, add_zero]
      have : h.left.v + u + h.left.v = (h.left.v + h.left.v) + u := by abel
      rw [this, w_add_self, zero_add]
    have hω_zero : ∀ u w : W n, ω M u w = 0 := by
      intro u w
      have hcomm_k : k u * k w = k w * k u :=
        setLike_mul_comm (hk_mem u) (hk_mem w)
      rw [hk_eq u, hk_eq w, ← map_mul, ← map_mul] at hcomm_k
      have hcomm_m := SemidirectProduct.inl_injective hcomm_k
      have ha := congrArg MGrp.a hcomm_m
      simp only [MGrp.mul_a, hmu, hmv] at ha
      have ha' : fBil M u w = fBil M w u := by
        have hsub := congrArg (fun z => z + ((m u).a + (m w).a)) ha
        have hL : (m u).a + (m w).a + fBil M u w + ((m u).a + (m w).a) = fBil M u w := by
          have : (m u).a + (m w).a + fBil M u w + ((m u).a + (m w).a) =
              ((m u).a + (m u).a) + ((m w).a + (m w).a) + fBil M u w := by abel
          rw [this, z0_add_self, z0_add_self, zero_add, zero_add]
        have hR : (m w).a + (m u).a + fBil M w u + ((m u).a + (m w).a) = fBil M w u := by
          have : (m w).a + (m u).a + fBil M w u + ((m u).a + (m w).a) =
              ((m u).a + (m u).a) + ((m w).a + (m w).a) + fBil M w u := by abel
          rw [this, z0_add_self, z0_add_self, zero_add, zero_add]
        rwa [hL, hR] at hsub
      rw [ω, ha', z0_add_self]
    obtain ⟨u, w, huw⟩ := exists_ne_zero_ω M hd hnd hiso
    exact huw (hω_zero u w)
  let H₀ : Subgroup (MGrp M) := H.comap SemidirectProduct.inl
  have hH_card : Nat.card H = Nat.card H₀ := by
    have hinj : Function.Injective (fun x : H₀ =>
        (⟨SemidirectProduct.inl x.1, x.2⟩ : H)) := by
      intro x y h
      exact Subtype.ext (SemidirectProduct.inl_injective (congrArg Subtype.val h))
    have hbij : Function.Bijective (fun x : H₀ =>
        (⟨SemidirectProduct.inl x.1, x.2⟩ : H)) := by
      refine ⟨hinj, ?_⟩
      rintro ⟨h, hh⟩
      have heq : SemidirectProduct.inl h.left = h := by
        ext <;> simp [hright_one h hh]
      have hmem : h.left ∈ H₀ := by
        change SemidirectProduct.inl h.left ∈ H
        rwa [heq]
      exact ⟨⟨h.left, hmem⟩, Subtype.ext heq⟩
    exact (Nat.card_congr (Equiv.ofBijective _ hbij)).symm
  have hComm₀ : IsMulCommutative H₀ :=
    Subgroup.comap_injective_isMulCommutative (H := H) SemidirectProduct.inl_injective
  have hswap_mem : ∀ x ∈ H₀, MGrp.swapAut M x ∈ H₀ := by
    intro x hx
    change SemidirectProduct.inl (MGrp.swapAut M x) ∈ H
    let σ : Multiplicative (ZMod 2) := Multiplicative.ofAdd (1 : ZMod 2)
    have hact_σ : MGrp.actionHom M σ = MGrp.swapAut M := by
      simp [MGrp.actionHom, σ]
    have hconj := hNorm.conj_mem _ hx (SemidirectProduct.inr σ)
    rwa [← map_inv SemidirectProduct.inr, ← SemidirectProduct.inl_aut, hact_σ] at hconj
  let projUV : MGrp M →* Multiplicative (W n × W n) :=
    { toFun := fun x => Multiplicative.ofAdd (x.u, x.v)
      map_one' := rfl
      map_mul' := fun x y => by simp; rfl }
  let f : H₀ →* Multiplicative (W n × W n) := projUV.comp H₀.subtype
  have hcard_f : Nat.card H₀ = Nat.card f.ker * Nat.card f.range := by
    have hlag := f.ker.card_mul_index
    rw [Subgroup.index_ker] at hlag
    exact hlag.symm
  have hker_le : Nat.card f.ker ≤ 2 ^ (2 * z₀) := by
    have hinj : Function.Injective (fun x : f.ker => (x.1.1.a, x.1.1.b)) := by
      intro x y h
      have hx0 : x.1.1.u = 0 ∧ x.1.1.v = 0 := by
        have hfx := MonoidHom.mem_ker.mp x.2
        change Multiplicative.ofAdd (x.1.1.u, x.1.1.v) = 1 at hfx
        have hpair : (x.1.1.u, x.1.1.v) = (0, 0) := Multiplicative.ofAdd.injective hfx
        exact Prod.ext_iff.mp hpair
      have hy0 : y.1.1.u = 0 ∧ y.1.1.v = 0 := by
        have hfy := MonoidHom.mem_ker.mp y.2
        change Multiplicative.ofAdd (y.1.1.u, y.1.1.v) = 1 at hfy
        have hpair : (y.1.1.u, y.1.1.v) = (0, 0) := Multiplicative.ofAdd.injective hfy
        exact Prod.ext_iff.mp hpair
      have hab := Prod.ext_iff.mp h
      ext1; ext1
      refine MGrp.ext ?_ ?_ ?_ ?_
      · exact hx0.1.trans hy0.1.symm
      · exact hx0.2.trans hy0.2.symm
      · exact hab.1
      · exact hab.2
    have : Finite f.ker := inferInstance
    calc
      Nat.card f.ker ≤ Nat.card (Z0 z₀ × Z0 z₀) := Nat.card_le_card_of_injective _ hinj
      _ = 2 ^ (2 * z₀) := by
          rw [Nat.card_eq_fintype_card, Fintype.card_prod, card_z0]
          ring
  let P : Submodule (ZMod 2) (W n × W n) :=
    { carrier := { p | Multiplicative.ofAdd p ∈ f.range }
      zero_mem' := by
        change Multiplicative.ofAdd (0 : W n × W n) ∈ f.range
        rw [ofAdd_zero]
        exact f.range.one_mem
      add_mem' := fun hp hq => f.range.mul_mem hp hq
      smul_mem' := fun c p hp => by
        rcases zmod2_cases c with rfl | rfl
        · change Multiplicative.ofAdd ((0 : ZMod 2) • p) ∈ f.range
          rw [zero_smul, ofAdd_zero]
          exact f.range.one_mem
        · change Multiplicative.ofAdd ((1 : ZMod 2) • p) ∈ f.range
          rw [one_smul]
          exact hp }
  have hP_card : Nat.card f.range = Nat.card P := by
    have hbij : Function.Bijective (fun p : P =>
        (⟨Multiplicative.ofAdd p.1, p.2⟩ : f.range)) := by
      refine ⟨fun p₁ p₂ h => Subtype.ext (Multiplicative.ofAdd.injective (congrArg Subtype.val h)),
        ?_⟩
      rintro ⟨y, hy⟩
      exact ⟨⟨Multiplicative.toAdd y, hy⟩, rfl⟩
    exact (Nat.card_congr (Equiv.ofBijective _ hbij)).symm
  let sumLin : (W n × W n) →ₗ[ZMod 2] W n :=
    { toFun := fun p => p.1 + p.2
      map_add' := fun p q => by simp; abel
      map_smul' := fun c p => by simp [smul_add] }
  let S₁ : Submodule (ZMod 2) (W n) := P.map sumLin
  let S₂ : Submodule (ZMod 2) (W n) := (P ⊓ LinearMap.ker sumLin).map (LinearMap.fst (ZMod 2) (W n) (W n))
  have hS₁_iso : ∀ w₁ ∈ S₁, ∀ w₂ ∈ S₁, ω M w₁ w₂ = 0 := by
    intro w₁ hw₁ w₂ hw₂
    rcases Submodule.mem_map.mp hw₁ with ⟨p₁, hp₁, rfl⟩
    rcases Submodule.mem_map.mp hw₂ with ⟨p₂, hp₂, rfl⟩
    rcases hp₁ with ⟨⟨x, hx⟩, hxp⟩
    rcases hp₂ with ⟨⟨y, hy⟩, hyp⟩
    have hpx : x.u = p₁.1 ∧ x.v = p₁.2 :=
      Prod.ext_iff.mp (Multiplicative.ofAdd.injective hxp)
    have hpy : y.u = p₂.1 ∧ y.v = p₂.2 :=
      Prod.ext_iff.mp (Multiplicative.ofAdd.injective hyp)
    have hxy := setLike_mul_comm hx hy
    have hxsy := setLike_mul_comm hx (hswap_mem y hy)
    have ha1 : fBil M x.u y.v + fBil M y.u x.v = 0 := by
      have ha := congrArg MGrp.a hxy
      simp only [MGrp.mul_a] at ha
      have hsub := congrArg (· + (x.a + y.a)) ha
      have hL : x.a + y.a + fBil M x.u y.v + (x.a + y.a) = fBil M x.u y.v := by
        have : x.a + y.a + fBil M x.u y.v + (x.a + y.a) =
            (x.a + x.a) + (y.a + y.a) + fBil M x.u y.v := by abel
        rw [this, z0_add_self, z0_add_self, zero_add, zero_add]
      have hR : y.a + x.a + fBil M y.u x.v + (x.a + y.a) = fBil M y.u x.v := by
        have : y.a + x.a + fBil M y.u x.v + (x.a + y.a) =
            (x.a + x.a) + (y.a + y.a) + fBil M y.u x.v := by abel
        rw [this, z0_add_self, z0_add_self, zero_add, zero_add]
      rw [hL, hR] at hsub
      rw [hsub, z0_add_self]
    have hb1 : fBil M x.v y.u + fBil M y.v x.u = 0 := by
      have hb := congrArg MGrp.b hxy
      simp only [MGrp.mul_b] at hb
      have hsub := congrArg (· + (x.b + y.b)) hb
      have hL : x.b + y.b + fBil M x.v y.u + (x.b + y.b) = fBil M x.v y.u := by
        have : x.b + y.b + fBil M x.v y.u + (x.b + y.b) =
            (x.b + x.b) + (y.b + y.b) + fBil M x.v y.u := by abel
        rw [this, z0_add_self, z0_add_self, zero_add, zero_add]
      have hR : y.b + x.b + fBil M y.v x.u + (x.b + y.b) = fBil M y.v x.u := by
        have : y.b + x.b + fBil M y.v x.u + (x.b + y.b) =
            (x.b + x.b) + (y.b + y.b) + fBil M y.v x.u := by abel
        rw [this, z0_add_self, z0_add_self, zero_add, zero_add]
      rw [hL, hR] at hsub
      rw [hsub, z0_add_self]
    have ha2 : fBil M x.u y.u + fBil M y.v x.v = 0 := by
      have ha := congrArg MGrp.a hxsy
      simp only [MGrp.mul_a, MGrp.swapAut_u, MGrp.swapAut_v, MGrp.swapAut_a] at ha
      have hsub := congrArg (· + (x.a + y.b)) ha
      have hL : x.a + y.b + fBil M x.u y.u + (x.a + y.b) = fBil M x.u y.u := by
        have : x.a + y.b + fBil M x.u y.u + (x.a + y.b) =
            (x.a + x.a) + (y.b + y.b) + fBil M x.u y.u := by abel
        rw [this, z0_add_self, z0_add_self, zero_add, zero_add]
      have hR : y.b + x.a + fBil M y.v x.v + (x.a + y.b) = fBil M y.v x.v := by
        have : y.b + x.a + fBil M y.v x.v + (x.a + y.b) =
            (x.a + x.a) + (y.b + y.b) + fBil M y.v x.v := by abel
        rw [this, z0_add_self, z0_add_self, zero_add, zero_add]
      rw [hL, hR] at hsub
      rw [hsub, z0_add_self]
    have hb2 : fBil M x.v y.v + fBil M y.u x.u = 0 := by
      have hb := congrArg MGrp.b hxsy
      simp only [MGrp.mul_b, MGrp.swapAut_u, MGrp.swapAut_v, MGrp.swapAut_b] at hb
      have hsub := congrArg (· + (x.b + y.a)) hb
      have hL : x.b + y.a + fBil M x.v y.v + (x.b + y.a) = fBil M x.v y.v := by
        have : x.b + y.a + fBil M x.v y.v + (x.b + y.a) =
            (x.b + x.b) + (y.a + y.a) + fBil M x.v y.v := by abel
        rw [this, z0_add_self, z0_add_self, zero_add, zero_add]
      have hR : y.a + x.b + fBil M y.u x.u + (x.b + y.a) = fBil M y.u x.u := by
        have : y.a + x.b + fBil M y.u x.u + (x.b + y.a) =
            (x.b + x.b) + (y.a + y.a) + fBil M y.u x.u := by abel
        rw [this, z0_add_self, z0_add_self, zero_add, zero_add]
      rw [hL, hR] at hsub
      rw [hsub, z0_add_self]
    change ω M (p₁.1 + p₁.2) (p₂.1 + p₂.2) = 0
    rw [← hpx.1, ← hpx.2, ← hpy.1, ← hpy.2]
    rw [ω_add_left, ω_add_right, ω_add_right]
    simp only [ω]
    have htot : (fBil M x.u y.u + fBil M y.u x.u) + (fBil M x.u y.v + fBil M y.v x.u) +
        ((fBil M x.v y.u + fBil M y.u x.v) + (fBil M x.v y.v + fBil M y.v x.v)) =
        (fBil M x.u y.v + fBil M y.u x.v) + (fBil M x.v y.u + fBil M y.v x.u) +
        (fBil M x.u y.u + fBil M y.v x.v) + (fBil M x.v y.v + fBil M y.u x.u) := by abel
    rw [htot, ha1, hb1, ha2, hb2, add_zero, add_zero, add_zero]
  have hS₂_iso : ∀ u₁ ∈ S₂, ∀ u₂ ∈ S₂, ω M u₁ u₂ = 0 := by
    intro u₁ hu₁ u₂ hu₂
    rcases Submodule.mem_map.mp hu₁ with ⟨p₁, ⟨hp₁P, hp₁K⟩, rfl⟩
    rcases Submodule.mem_map.mp hu₂ with ⟨p₂, ⟨hp₂P, hp₂K⟩, rfl⟩
    have hv₁ : p₁.1 = p₁.2 := w_eq_of_add_eq_zero (LinearMap.mem_ker.mp hp₁K)
    have hv₂ : p₂.1 = p₂.2 := w_eq_of_add_eq_zero (LinearMap.mem_ker.mp hp₂K)
    rcases hp₁P with ⟨⟨x, hx⟩, hxp⟩
    rcases hp₂P with ⟨⟨y, hy⟩, hyp⟩
    have hpx : x.u = p₁.1 ∧ x.v = p₁.2 :=
      Prod.ext_iff.mp (Multiplicative.ofAdd.injective hxp)
    have hpy : y.u = p₂.1 ∧ y.v = p₂.2 :=
      Prod.ext_iff.mp (Multiplicative.ofAdd.injective hyp)
    have hxy := setLike_mul_comm hx hy
    have ha := congrArg MGrp.a hxy
    simp only [MGrp.mul_a, hpx.1, hpx.2, hpy.1, hpy.2, ← hv₁, ← hv₂] at ha
    have hsub := congrArg (· + (x.a + y.a)) ha
    have hL : x.a + y.a + fBil M p₁.1 p₂.1 + (x.a + y.a) = fBil M p₁.1 p₂.1 := by
      have : x.a + y.a + fBil M p₁.1 p₂.1 + (x.a + y.a) =
          (x.a + x.a) + (y.a + y.a) + fBil M p₁.1 p₂.1 := by abel
      rw [this, z0_add_self, z0_add_self, zero_add, zero_add]
    have hR : y.a + x.a + fBil M p₂.1 p₁.1 + (x.a + y.a) = fBil M p₂.1 p₁.1 := by
      have : y.a + x.a + fBil M p₂.1 p₁.1 + (x.a + y.a) =
          (x.a + x.a) + (y.a + y.a) + fBil M p₂.1 p₁.1 := by abel
      rw [this, z0_add_self, z0_add_self, zero_add, zero_add]
    rw [hL, hR] at hsub
    change ω M p₁.1 p₂.1 = 0
    rw [ω, hsub, z0_add_self]
  have hcard_S₁ : Nat.card S₁ ≤ 2 ^ (d - 1) := by
    classical
    let : Fintype S₁ := Fintype.ofFinite S₁
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
    exact Nat.pow_le_pow_right (by decide) (hiso S₁ hS₁_iso)
  have hcard_S₂ : Nat.card S₂ ≤ 2 ^ (d - 1) := by
    classical
    let : Fintype S₂ := Fintype.ofFinite S₂
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
    exact Nat.pow_le_pow_right (by decide) (hiso S₂ hS₂_iso)
  let sumP : P →ₗ[ZMod 2] S₁ :=
    { toFun := fun p => ⟨sumLin p.1, Submodule.mem_map_of_mem p.2⟩
      map_add' := fun p q => Subtype.ext (sumLin.map_add p.1 q.1)
      map_smul' := fun c p => Subtype.ext (sumLin.map_smul c p.1) }
  have hsumP_surj : Function.Surjective sumP := by
    rintro ⟨w, hw⟩
    rcases Submodule.mem_map.mp hw with ⟨p, hp, rfl⟩
    exact ⟨⟨p, hp⟩, rfl⟩
  have hP_mul : Nat.card P = Nat.card S₁ * Nat.card (LinearMap.ker sumP) := by
    have hlag := (LinearMap.ker sumP).toAddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
    have heq : Nat.card (P ⧸ LinearMap.ker sumP) = Nat.card S₁ :=
      Nat.card_congr (sumP.quotKerEquivOfSurjective hsumP_surj).toEquiv
    have hq : Nat.card (P ⧸ (LinearMap.ker sumP).toAddSubgroup) =
        Nat.card (P ⧸ LinearMap.ker sumP) := rfl
    have hk : Nat.card (LinearMap.ker sumP).toAddSubgroup = Nat.card (LinearMap.ker sumP) := rfl
    rw [hq, heq, hk] at hlag
    exact hlag
  have hkerP_le : Nat.card (LinearMap.ker sumP) ≤ Nat.card S₂ := by
    have hinj : Function.Injective (fun p : LinearMap.ker sumP =>
        (⟨p.1.1.1, Submodule.mem_map.mpr
          ⟨p.1.1, ⟨p.1.2, LinearMap.mem_ker.mpr (congrArg Subtype.val (LinearMap.mem_ker.mp p.2))⟩,
            rfl⟩⟩ : S₂)) := by
      intro p₁ p₂ h
      have h1 : p₁.1.1.1 = p₂.1.1.1 := congrArg Subtype.val h
      have hp₁ : p₁.1.1.1 = p₁.1.1.2 :=
        w_eq_of_add_eq_zero (congrArg Subtype.val (LinearMap.mem_ker.mp p₁.2))
      have hp₂ : p₂.1.1.1 = p₂.1.1.2 :=
        w_eq_of_add_eq_zero (congrArg Subtype.val (LinearMap.mem_ker.mp p₂.2))
      ext1; ext1
      exact Prod.ext h1 (hp₁.symm.trans (h1.trans hp₂))
    have : Finite S₂ := inferInstance
    exact Nat.card_le_card_of_injective _ hinj
  have hP_le : Nat.card P ≤ 2 ^ (2 * (d - 1)) := by
    calc
      Nat.card P = Nat.card S₁ * Nat.card (LinearMap.ker sumP) := hP_mul
      _ ≤ 2 ^ (d - 1) * 2 ^ (d - 1) := Nat.mul_le_mul hcard_S₁ (hkerP_le.trans hcard_S₂)
      _ = 2 ^ (2 * (d - 1)) := by rw [← pow_add, two_mul]
  calc
    Nat.card H = Nat.card H₀ := hH_card
    _ = Nat.card f.ker * Nat.card f.range := hcard_f
    _ = Nat.card f.ker * Nat.card P := by rw [hP_card]
    _ ≤ 2 ^ (2 * z₀) * 2 ^ (2 * (d - 1)) := Nat.mul_le_mul hker_le hP_le
    _ = 2 ^ (2 * (d - 1) + 2 * z₀) := by rw [← pow_add, add_comm]

end G76Properties

end SemidirectTwoGroup

section MainTheorems

/-- Parametric counterexample engine for Kourovka 20.75 & 20.76. -/
theorem exists_counterexample_family
    (n z₀ d : ℕ) (hd : 1 ≤ d) (hnd : d ≤ n)
    (hprob : (∏ i ∈ Finset.range d, (2 ^ n - 2 ^ i)) <
      (∏ i ∈ Finset.range d, (2 ^ d - 2 ^ i)) * 2 ^ (z₀ * (d * (d - 1) / 2))) :
    ∃ (G : Type) (_ : Group G) (_ : Fintype G),
      IsPGroup 2 G ∧
      Nat.card G = 2 ^ (2 * n + 2 * z₀ + 1) ∧
      (∀ H : Subgroup G, H.Normal ∧ IsMulCommutative H →
        Nat.card H ≤ 2 ^ (2 * (d - 1) + 2 * z₀)) ∧
      (∃ B : Subgroup G, IsMulCommutative B ∧
        (∀ x ∈ B, x ^ 2 = 1) ∧
        Nat.card B = 2 ^ (n + 2 * z₀)) := by
  obtain ⟨M, hiso⟩ := exists_good_M n z₀ d hd hnd hprob
  refine ⟨G76 M, inferInstance, inferInstance, isPGroup_G76 M, card_G76 M, ?_, ?_⟩
  · intro H ⟨hNorm, hComm⟩
    exact normal_abelian_card_le M hd hnd hiso H hNorm hComm
  · exact ⟨elemAbelianSubgroup M, elemAbelianSubgroup_props M⟩

private lemma hprob_of_bound (n z₀ d a : ℕ)
    (ha : 2 ^ a ≤ ∏ i ∈ Finset.range d, (2 ^ d - 2 ^ i))
    (hlt : d * n < a + z₀ * (d * (d - 1) / 2)) :
    (∏ i ∈ Finset.range d, (2 ^ n - 2 ^ i)) <
      (∏ i ∈ Finset.range d, (2 ^ d - 2 ^ i)) * 2 ^ (z₀ * (d * (d - 1) / 2)) := by
  have hLHS : ∏ i ∈ Finset.range d, (2 ^ n - 2 ^ i) ≤ 2 ^ (d * n) := by
    calc
      ∏ i ∈ Finset.range d, (2 ^ n - 2 ^ i)
          ≤ ∏ _i ∈ Finset.range d, 2 ^ n := Finset.prod_le_prod' fun i _ => Nat.sub_le _ _
      _ = (2 ^ n) ^ d := by rw [Finset.prod_const, Finset.card_range]
      _ = 2 ^ (d * n) := by rw [← pow_mul, mul_comm]
  have hpow : 2 ^ (d * n) < 2 ^ a * 2 ^ (z₀ * (d * (d - 1) / 2)) := by
    rw [← pow_add]
    exact Nat.pow_lt_pow_right (by decide) hlt
  exact Nat.lt_of_le_of_lt hLHS (Nat.lt_of_lt_of_le hpow (Nat.mul_le_mul_right _ ha))

/-- Sharpened counterexample of order 2^141 (normal abelian <= 2^40, elem. abelian = 2^81). -/
theorem exists_counterexample_two_pow_141 :
    ∃ (G : Type) (_ : Group G) (_ : Fintype G),
      IsPGroup 2 G ∧
      Nat.card G = 2 ^ 141 ∧
      (∀ H : Subgroup G, H.Normal ∧ IsMulCommutative H → Nat.card H ≤ 2 ^ 40) ∧
      (∃ B : Subgroup G, IsMulCommutative B ∧
        (∀ x ∈ B, x ^ 2 = 1) ∧
        Nat.card B = 2 ^ 81) := by
  have hprob := hprob_of_bound 59 11 10 98 (by norm_num [Finset.prod_range_succ]) (by decide)
  obtain ⟨G, _, _, hg, hcard, hnorm, ⟨B, hBcomm, hBexp, hBcard⟩⟩ :=
    exists_counterexample_family 59 11 10 (by omega) (by omega) hprob
  exact ⟨G, inferInstance, inferInstance, hg, hcard, hnorm, ⟨B, hBcomm, hBexp, hBcard⟩⟩

/-- Muliarchyk's exact counterexample of order 2^145 (normal abelian <= 2^42, elem. abelian = 2^85). -/
theorem exists_counterexample_two_pow_145 :
    ∃ (G : Type) (_ : Group G) (_ : Fintype G),
      IsPGroup 2 G ∧
      Nat.card G = 2 ^ 145 ∧
      (∀ H : Subgroup G, H.Normal ∧ IsMulCommutative H → Nat.card H ≤ 2 ^ 42) ∧
      (∃ B : Subgroup G, IsMulCommutative B ∧
        (∀ x ∈ B, x ^ 2 = 1) ∧
        Nat.card B = 2 ^ 85) := by
  have hprob := hprob_of_bound 59 13 9 79 (by norm_num [Finset.prod_range_succ]) (by decide)
  obtain ⟨G, _, _, hg, hcard, hnorm, ⟨B, hBcomm, hBexp, hBcard⟩⟩ :=
    exists_counterexample_family 59 13 9 (by omega) (by omega) hprob
  exact ⟨G, inferInstance, inferInstance, hg, hcard, hnorm, ⟨B, hBcomm, hBexp, hBcard⟩⟩

set_option linter.unusedVariables false in
/-- Refutation of Kourovka Problem 20.76 (Pyber). -/
theorem kourovka_20_76 :
    ¬ (∀ᵉ (p : ℕ) (hp : p.Prime) (G : Type) (_ : Group G) (hg : IsPGroup p G) (_ : Finite G) (k : ℕ)
    (h : ∀ H : Subgroup G, H.Normal ∧ IsMulCommutative H → Nat.card H ≤ p ^ k),
    (∀ H : Subgroup G, IsMulCommutative H → Nat.card H ≤ p ^ (2 * k))) := by
  intro hall
  obtain ⟨G, _, _, hg, _, hnorm, ⟨B, hBcomm, _, hBcard⟩⟩ := exists_counterexample_two_pow_141
  have hle := hall 2 Nat.prime_two G inferInstance hg inferInstance 40 hnorm B hBcomm
  rw [hBcard] at hle
  have hlt : 2 ^ (2 * 40) < 2 ^ 81 := Nat.pow_lt_pow_right (by decide) (by omega)
  omega

private lemma exists_finset_closure_of_card_le_two_pow_aux {G : Type} [Group G] [DecidableEq G]
    (H : Subgroup G) [Finite H] (k : ℕ) (hk : Nat.card H ≤ 2 ^ k) :
    ∀ (m : ℕ) (S : Finset G),
      (S : Set G) ⊆ H →
      2 ^ S.card ≤ Nat.card (Subgroup.closure (S : Set G)) →
      Nat.card H - Nat.card (Subgroup.closure (S : Set G)) ≤ m →
      ∃ T : Finset G, T.card ≤ k ∧ Subgroup.closure (T : Set G) = H := by
  intro m
  induction m with
  | zero =>
    intro S hSH hpow hm
    have hK_le : Subgroup.closure (S : Set G) ≤ H := (Subgroup.closure_le H).mpr hSH
    have : Finite (Subgroup.closure (S : Set G)) :=
      Finite.Set.subset H (SetLike.coe_subset_coe.mpr hK_le)
    have hcard_le : Nat.card (Subgroup.closure (S : Set G)) ≤ Nat.card H :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hK_le)
    have hcard_eq : Nat.card (Subgroup.closure (S : Set G)) = Nat.card H := by omega
    have hK_eq : Subgroup.closure (S : Set G) = H :=
      Subgroup.eq_of_le_of_card_ge hK_le hcard_eq.ge
    refine ⟨S, ?_, hK_eq⟩
    have h2 : 2 ^ S.card ≤ 2 ^ k := hpow.trans (hcard_eq ▸ hk)
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp h2
  | succ m ih =>
    intro S hSH hpow hm
    have hK_le : Subgroup.closure (S : Set G) ≤ H := (Subgroup.closure_le H).mpr hSH
    have : Finite (Subgroup.closure (S : Set G)) :=
      Finite.Set.subset H (SetLike.coe_subset_coe.mpr hK_le)
    by_cases hK_eq : Subgroup.closure (S : Set G) = H
    · refine ⟨S, ?_, hK_eq⟩
      have h2 : 2 ^ S.card ≤ 2 ^ k := hpow.trans (hK_eq ▸ hk)
      exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp h2
    · have hlt : Subgroup.closure (S : Set G) < H := lt_of_le_of_ne hK_le hK_eq
      obtain ⟨x, hxH, hxK⟩ := SetLike.exists_of_lt hlt
      let S' : Finset G := insert x S
      have hS'H : (S' : Set G) ⊆ H := by
        intro y hy
        change y ∈ (insert x S : Finset G) at hy
        rcases Finset.mem_insert.mp hy with rfl | hyS
        · exact hxH
        · exact hSH hyS
      have hK_lt_K' : Subgroup.closure (S : Set G) < Subgroup.closure (S' : Set G) := by
        refine lt_of_le_of_ne (Subgroup.closure_mono (Finset.subset_insert x S)) ?_
        intro heq
        apply hxK
        rw [heq]
        exact Subgroup.subset_closure (Finset.mem_insert_self x S)
      have hK'_le : Subgroup.closure (S' : Set G) ≤ H := (Subgroup.closure_le H).mpr hS'H
      have : Finite (Subgroup.closure (S' : Set G)) :=
        Finite.Set.subset H (SetLike.coe_subset_coe.mpr hK'_le)
      have hdvd : Nat.card (Subgroup.closure (S : Set G)) ∣
          Nat.card (Subgroup.closure (S' : Set G)) :=
        Subgroup.card_dvd_of_le hK_lt_K'.le
      have hcard_lt : Nat.card (Subgroup.closure (S : Set G)) <
          Nat.card (Subgroup.closure (S' : Set G)) := by
        classical
        let : Fintype (Subgroup.closure (S : Set G)) := Fintype.ofFinite _
        let : Fintype (Subgroup.closure (S' : Set G)) := Fintype.ofFinite _
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
        let ι : Subgroup.closure (S : Set G) → Subgroup.closure (S' : Set G) :=
          fun z => ⟨z.1, hK_lt_K'.le z.2⟩
        have hι_inj : Function.Injective ι := fun z₁ z₂ h =>
          Subtype.ext (congrArg (Subtype.val : Subgroup.closure (S' : Set G) → G) h)
        let x' : Subgroup.closure (S' : Set G) :=
          ⟨x, Subgroup.subset_closure (Finset.mem_insert_self x S)⟩
        refine Fintype.card_lt_of_injective_of_notMem (b := x') ι hι_inj ?_
        rintro ⟨z, hz⟩
        apply hxK
        have hzx : z.1 = x := congrArg Subtype.val hz
        rw [← hzx]
        exact z.2
      rcases hdvd with ⟨q, hq⟩
      have hq_ge : 2 ≤ q := by
        rcases q with _ | _ | q
        · simp only [mul_zero] at hq
          have hpos : 0 < Nat.card (Subgroup.closure (S' : Set G)) := Nat.card_pos
          omega
        · rw [Nat.zero_add, mul_one] at hq
          omega
        · omega
      have hpow' : 2 ^ S'.card ≤ Nat.card (Subgroup.closure (S' : Set G)) := by
        calc
          2 ^ S'.card ≤ 2 ^ (S.card + 1) :=
            Nat.pow_le_pow_right (by decide) (Finset.card_insert_le x S)
          _ = 2 * 2 ^ S.card := by rw [pow_succ, mul_comm]
          _ ≤ 2 * Nat.card (Subgroup.closure (S : Set G)) := Nat.mul_le_mul_left 2 hpow
          _ ≤ Nat.card (Subgroup.closure (S : Set G)) * q := by
              rw [mul_comm 2]
              exact Nat.mul_le_mul_left _ hq_ge
          _ = Nat.card (Subgroup.closure (S' : Set G)) := hq.symm
      have hm' : Nat.card H - Nat.card (Subgroup.closure (S' : Set G)) ≤ m := by
        have hpos_K : 0 < Nat.card (Subgroup.closure (S : Set G)) := Nat.card_pos
        omega
      exact ih S' hS'H hpow' hm'

lemma exists_finset_closure_of_card_le_two_pow {G : Type} [Group G]
    (H : Subgroup G) [Finite H] (k : ℕ) (hk : Nat.card H ≤ 2 ^ k) :
    ∃ S : Finset G, S.card ≤ k ∧ Subgroup.closure (S : Set G) = H := by
  classical
  refine exists_finset_closure_of_card_le_two_pow_aux H k hk (Nat.card H) ∅ ?_ ?_ ?_
  · simp
  · simp
  · omega

lemma card_closure_le_two_pow_of_elem_abelian {G : Type} [Group G] [Finite G]
    (B : Subgroup G) (hBcomm : IsMulCommutative B) (hBexp : ∀ x ∈ B, x ^ 2 = 1)
    (S : Finset G) (hSB : (S : Set G) ⊆ B) :
    Nat.card (Subgroup.closure (S : Set G)) ≤ 2 ^ S.card := by
  classical
  have := hBcomm
  induction S using Finset.induction_on with
  | empty =>
    simp
  | @insert a S haS ih =>
    have haB : a ∈ B := hSB (Finset.mem_insert_self a S)
    have hSB' : (S : Set G) ⊆ B := fun x hx => hSB (Finset.mem_insert_of_mem hx)
    have ih' := ih hSB'
    have ha_sq : a * a = 1 := by
      rw [← sq]
      exact hBexp a haB
    have ha_inv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha_sq
    let K := Subgroup.closure (S : Set G)
    have hKB : K ≤ B := (Subgroup.closure_le B).mpr hSB'
    have hcomm_a : ∀ x ∈ K, x * a = a * x := fun x hx =>
      setLike_mul_comm (hKB hx) haB
    let M : Subgroup G :=
      { carrier := { y | ∃ x ∈ K, ∃ b : Bool, y = if b then x * a else x }
        one_mem' := ⟨1, K.one_mem, false, rfl⟩
        mul_mem' := by
          rintro _ _ ⟨x₁, hx₁, b₁, rfl⟩ ⟨x₂, hx₂, b₂, rfl⟩
          cases b₁ <;> cases b₂
          · exact ⟨x₁ * x₂, K.mul_mem hx₁ hx₂, false, rfl⟩
          · exact ⟨x₁ * x₂, K.mul_mem hx₁ hx₂, true, by simp [mul_assoc]⟩
          · refine ⟨x₁ * x₂, K.mul_mem hx₁ hx₂, true, ?_⟩
            dsimp
            rw [mul_assoc, ← hcomm_a x₂ hx₂, ← mul_assoc]
          · refine ⟨x₁ * x₂, K.mul_mem hx₁ hx₂, false, ?_⟩
            dsimp
            calc
              (x₁ * a) * (x₂ * a) = x₁ * (a * x₂) * a := by group
              _ = x₁ * (x₂ * a) * a := by rw [hcomm_a x₂ hx₂]
              _ = x₁ * x₂ * (a * a) := by group
              _ = x₁ * x₂ := by rw [ha_sq, mul_one]
        inv_mem' := by
          rintro _ ⟨x, hx, b, rfl⟩
          cases b
          · exact ⟨x⁻¹, K.inv_mem hx, false, rfl⟩
          · refine ⟨x⁻¹, K.inv_mem hx, true, ?_⟩
            dsimp
            rw [mul_inv_rev, ha_inv]
            exact (hcomm_a x⁻¹ (K.inv_mem hx)).symm }
    have hsubM : Subgroup.closure ((insert a S : Finset G) : Set G) ≤ M := by
      rw [Subgroup.closure_le]
      intro y hy
      rcases Finset.mem_insert.mp (Finset.mem_coe.mp hy) with rfl | hyS
      · exact ⟨1, K.one_mem, true, by simp⟩
      · exact ⟨y, Subgroup.subset_closure hyS, false, rfl⟩
    let f : K × Bool → G := fun p => if p.2 then p.1.1 * a else p.1.1
    have hmem : ∀ y : Subgroup.closure ((insert a S : Finset G) : Set G),
        ∃ p : K × Bool, f p = y.1 := by
      intro y
      rcases hsubM y.2 with ⟨x, hx, b, hy⟩
      exact ⟨(⟨x, hx⟩, b), hy.symm⟩
    let g : Subgroup.closure ((insert a S : Finset G) : Set G) → K × Bool :=
      fun y => (hmem y).choose
    have hg : Function.Injective g := by
      intro y₁ y₂ h
      have hy₁ : f (g y₁) = y₁.1 := (hmem y₁).choose_spec
      have hy₂ : f (g y₂) = y₂.1 := (hmem y₂).choose_spec
      have hf : f (g y₁) = f (g y₂) := congrArg f h
      exact Subtype.ext (hy₁.symm.trans (hf.trans hy₂))
    calc
      Nat.card (Subgroup.closure ((insert a S : Finset G) : Set G))
          ≤ Nat.card (K × Bool) := Nat.card_le_card_of_injective g hg
      _ = Nat.card K * 2 := by
          rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]
      _ ≤ 2 ^ S.card * 2 := Nat.mul_le_mul_right 2 ih'
      _ = 2 ^ (insert a S).card := by
          rw [Finset.card_insert_of_notMem haS, pow_succ]

set_option linter.unusedVariables false in
/-- Refutation of Kourovka Problem 20.75 (generator-count version). -/
theorem kourovka_20_75 :
    ¬ (∀ᵉ (p : ℕ) (hp : p.Prime) (G : Type) (_ : Group G) (hg : IsPGroup p G) (_ : Finite G) (k : ℕ)
    (h : ∀ H : Subgroup G, H.Normal ∧ IsMulCommutative H →
      ∃ S : Finset G, S.card ≤ k ∧ Subgroup.closure (S : Set G) = H),
    (∀ H : Subgroup G, IsMulCommutative H →
      ∃ S : Finset G, S.card ≤ 2 * k ∧ Subgroup.closure (S : Set G) = H)) := by
  intro hall
  obtain ⟨G, _, _, hg, _, hnorm, ⟨B, hBcomm, hBexp, hBcard⟩⟩ := exists_counterexample_two_pow_141
  have hgen : ∀ H : Subgroup G, H.Normal ∧ IsMulCommutative H →
      ∃ S : Finset G, S.card ≤ 40 ∧ Subgroup.closure (S : Set G) = H := by
    intro H hH
    exact exists_finset_closure_of_card_le_two_pow H 40 (hnorm H hH)
  obtain ⟨S, hScard, hSclos⟩ := hall 2 Nat.prime_two G inferInstance hg inferInstance 40 hgen B hBcomm
  have hSB : (S : Set G) ⊆ B := by
    rw [← hSclos]
    exact Subgroup.subset_closure
  have hle := card_closure_le_two_pow_of_elem_abelian B hBcomm hBexp S hSB
  rw [hSclos, hBcard] at hle
  have hpow : 2 ^ S.card ≤ 2 ^ 80 := Nat.pow_le_pow_right (by decide) hScard
  have h81 : 2 ^ 81 ≤ 2 ^ 80 := hle.trans hpow
  have hlt : 2 ^ 80 < 2 ^ 81 := Nat.pow_lt_pow_right (by decide) (by omega)
  omega

/-- Superlinear / quadratic Omega(k^2) separation refuting any linear exponent bound p^(C*k). -/
theorem no_linear_exponent_bound (C : ℕ) :
    ∃ (G : Type) (_ : Group G) (_ : Finite G) (k : ℕ),
      IsPGroup 2 G ∧ 1 ≤ k ∧
      (∀ H : Subgroup G, H.Normal ∧ IsMulCommutative H → Nat.card H ≤ 2 ^ k) ∧
      (∃ B : Subgroup G, IsMulCommutative B ∧ 2 ^ (C * k) < Nat.card B) := by
  let m : ℕ := 4 * C + 2
  let d : ℕ := 2 * m + 1
  let z₀ : ℕ := 2 * m
  let n : ℕ := 2 * m ^ 2 - 1
  have hm2 : 2 ≤ m := by omega
  have hd : 1 ≤ d := by omega
  have hnd : d ≤ n := by
    have hm_sq : 4 * m ≤ 2 * m ^ 2 := by nlinarith
    omega
  have hexp_lt : d * n < z₀ * (d * (d - 1) / 2) := by
    have hdiv : d * (d - 1) / 2 = (2 * m + 1) * m := by
      have h1 : d - 1 = 2 * m := by omega
      rw [h1]
      have h2 : d * (2 * m) = 2 * (d * m) := by ring
      rw [h2, Nat.mul_div_right _ (by decide)]
    rw [hdiv]
    have hmul_rhs : z₀ * ((2 * m + 1) * m) = (2 * m + 1) * (2 * m ^ 2) := by
      dsimp [z₀]
      ring
    have hm_pos : 1 ≤ 2 * m ^ 2 := by nlinarith
    have hn_lt : n < 2 * m ^ 2 := by omega
    rw [hmul_rhs]
    exact Nat.mul_lt_mul_of_pos_left hn_lt (by omega)
  have hprob : (∏ i ∈ Finset.range d, (2 ^ n - 2 ^ i)) <
      (∏ i ∈ Finset.range d, (2 ^ d - 2 ^ i)) * 2 ^ (z₀ * (d * (d - 1) / 2)) := by
    have hLHS : ∏ i ∈ Finset.range d, (2 ^ n - 2 ^ i) ≤ 2 ^ (d * n) := by
      calc
        ∏ i ∈ Finset.range d, (2 ^ n - 2 ^ i)
            ≤ ∏ _i ∈ Finset.range d, 2 ^ n :=
              Finset.prod_le_prod' fun i _ => Nat.sub_le _ _
        _ = (2 ^ n) ^ d := by rw [Finset.prod_const, Finset.card_range]
        _ = 2 ^ (d * n) := by rw [← pow_mul, mul_comm]
    have hRHS_prod : 1 ≤ ∏ i ∈ Finset.range d, (2 ^ d - 2 ^ i) := by
      refine Finset.one_le_prod' fun i hi => ?_
      have hid : i < d := Finset.mem_range.mp hi
      have hlt : 2 ^ i < 2 ^ d := Nat.pow_lt_pow_right (by decide) hid
      omega
    have hpow_lt : 2 ^ (d * n) < 2 ^ (z₀ * (d * (d - 1) / 2)) :=
      Nat.pow_lt_pow_right (by decide) hexp_lt
    calc
      ∏ i ∈ Finset.range d, (2 ^ n - 2 ^ i) ≤ 2 ^ (d * n) := hLHS
      _ < 2 ^ (z₀ * (d * (d - 1) / 2)) := hpow_lt
      _ ≤ (∏ i ∈ Finset.range d, (2 ^ d - 2 ^ i)) * 2 ^ (z₀ * (d * (d - 1) / 2)) :=
            Nat.le_mul_of_pos_left _ (by positivity)
  obtain ⟨G, _, _, hg, _, hnorm, ⟨B, hBcomm, _, hBcard⟩⟩ :=
    exists_counterexample_family n z₀ d hd hnd hprob
  let k : ℕ := 2 * (d - 1) + 2 * z₀
  refine ⟨G, inferInstance, inferInstance, k, hg, by omega, hnorm, ⟨B, hBcomm, ?_⟩⟩
  rw [hBcard]
  have hCk : C * k < n + 2 * z₀ := by
    have hk_eq : k = 8 * m := by dsimp [k, d, z₀]; omega
    have hm_sq : 2 * m ^ 2 = 8 * C * m + 4 * m := by
      dsimp [m]
      ring
    have hm_pos : 1 ≤ 2 * m ^ 2 := by nlinarith
    have hk_val : C * k = 8 * C * m := by rw [hk_eq]; ring
    have hrhs_val : n + 2 * z₀ = 8 * C * m + 8 * m - 1 := by
      dsimp [n, z₀]
      omega
    omega
  exact Nat.pow_lt_pow_right (by decide) hCk

end MainTheorems

end Kourovka20_76

/-! ## Bridge to the formal-conjectures statement (appended by the audit) -/
set_option pp.numericTypes true
set_option pp.fieldNotation false

/-- The upstream statement is proved by the standalone theorem, which has exactly the upstream type. -/
theorem upstream_type_match : type_of% @Kourovka.«20.76».kourovka_20_76 :=
  @Kourovka20_76.kourovka_20_76

/-- Definitional equality of the two types, checked separately. -/
example : (type_of% @Kourovka20_76.kourovka_20_76) = (type_of% @Kourovka.«20.76».kourovka_20_76) := rfl

#check @Kourovka.«20.76».kourovka_20_76
#check @Kourovka20_76.kourovka_20_76
#check @Kourovka20_76.kourovka_20_75
#check @Kourovka20_76.exists_counterexample_two_pow_141
#check @Kourovka20_76.exists_counterexample_two_pow_145
#check @Kourovka20_76.exists_counterexample_family
#check @Kourovka20_76.no_linear_exponent_bound
#check @Kourovka20_76.pyber_bound_of_nilpotencyClass_le_two
#check @Kourovka20_76.abelian_card_le_of_commutator_le_center
#check @Kourovka20_76.card_group_le_pow_quadratic
#check @Kourovka20_76.abelian_card_le_pow_quadratic
#check @Kourovka20_76.centralizer_eq_self_of_max_normal_abelian
#check @Kourovka20_76.exists_good_M
#check @Kourovka20_76.nilpotencyClass_G76_le_four
#check @Kourovka20_76.nilpotencyClass_G76_eq_four
#print Kourovka20_76.kourovka_20_76
#print Kourovka20_76.kourovka_20_75

#print axioms Kourovka.«20.76».kourovka_20_76
#print axioms upstream_type_match
#print axioms Kourovka20_76.kourovka_20_76
#print axioms Kourovka20_76.kourovka_20_75
#print axioms Kourovka20_76.exists_counterexample_two_pow_141
#print axioms Kourovka20_76.exists_counterexample_two_pow_145
#print axioms Kourovka20_76.exists_counterexample_family
#print axioms Kourovka20_76.no_linear_exponent_bound
#print axioms Kourovka20_76.pyber_bound_of_nilpotencyClass_le_two
#print axioms Kourovka20_76.abelian_card_le_of_commutator_le_center
#print axioms Kourovka20_76.card_group_le_pow_quadratic
#print axioms Kourovka20_76.abelian_card_le_pow_quadratic
#print axioms Kourovka20_76.centralizer_eq_self_of_max_normal_abelian
#print axioms Kourovka20_76.exists_good_M
#print axioms Kourovka20_76.nilpotencyClass_G76_le_four
#print axioms Kourovka20_76.nilpotencyClass_G76_eq_four
