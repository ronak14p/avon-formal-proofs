/-
Copyright (c) 2026 Ronak Patel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ronak Patel
-/
import Mathlib

/-!
# Certified Sum-of-Squares Bounds on Tao's Sidon Autocorrelation Constant `C1a`

This file develops a self-contained Real-Symmetric Direct-`T_g` Sum-of-Squares (SOS)
duality theory for Tao's first autoconvolution (Sidon autocorrelation) constant `C1a`,
proves the single-SDP certified lower bound

  `4055172655215574821001279 / 3125000000000000000000000 ≤ C1a` (`> 12976 / 10000 = 1.2976`),

establishes an explicit 50-bin step-function upper bound

  `C1a ≤ 3801261850 / 2500100001 ≤ 1521 / 1000 < π / 2`

disproving the Schinzel–Schmidt conjecture, and proves the discrete-to-continuous
`B_2[g]`-Sidon set inequality `C1a * |A|^2 ≤ 2 * g * N` together with the unconditional
classical Sidon bound `|A|^2 ≤ (2500 / 811) * N`.

## Main Definitions and Results

* `Constant1aProof.C1a`: Tao's first autoconvolution constant on `[-1/4, 1/4]`.
* `Constant1aProof.mem_Ioc_c1a_answer`: Certified witness `12976 / 10000 = 1.2976`.
* `Constant1aProof.one_le_c1a`, `Constant1aProof.c1a_le_two`: Basic bracket `1 ≤ C1a ≤ 2`.
* `Constant1aProof.autoconv_fourier_cos`, `Constant1aProof.autoconv_fourier_sin`:
  Exact real cosine and sine Fourier identities for autoconvolutions on `[-1/2, 1/2]`.
* `Constant1aProof.finite_bessel_autoconv`: Elementary finite trigonometric Bessel inequality
  for autoconvolutions, avoiding infinite Fourier series and `AddCircle` machinery.
* `Constant1aProof.c1a_ge_of_sos_certificate`: General Real-Symmetric Direct-`T_g` SOS
  duality master theorem over `N` folded cells on `[0, 1/4]`.
* `Constant1aProof.cos_taylor_deg6_le`, `Constant1aProof.cos_le_taylor_deg8`,
  `Constant1aProof.sin_taylor_deg7_le`, `Constant1aProof.sin_le_taylor_deg9`:
  Alternating polynomial Taylor brackets on `[0, ∞)`.
* `Constant1aProof.c1a_ge_cert80_exact`, `Constant1aProof.c1a_ge_12976`,
  `Constant1aProof.c1a_lower_bound`, `Constant1aProof.mem_Ioc_c1a`:
  Pure-`decide` `(N = 80, K = 65, D = 10^5)` SOS lower bounds on `C1a`.
* `Constant1aProof.c1a_le_step50`, `Constant1aProof.c1a_le_1521`,
  `Constant1aProof.c1a_lt_pi_div_two`: Explicit 50-bin step-function upper bounds.
* `Constant1aProof.IsGSidon`, `Constant1aProof.IsSidonFinset`,
  `Constant1aProof.IsSidonFinset.isGSidon_two`,
  `Constant1aProof.c1a_mul_card_sq_le_two_mul_g_sidon`,
  `Constant1aProof.isSidonFinset_card_sq_le`: Discrete `B_2[g]`-Sidon bridge.
-/

set_option maxRecDepth 4096

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Constant1aProof

noncomputable def C1a : ℝ :=
  sSup {C : ℝ | ∀ ⦃f : ℝ → ℝ⦄, 0 ≤ f → MemLp f 2 →
    C * (∫ x in (- 1 / 4)..(1 / 4), f x) ^ 2
      ≤ sSup {∫ x, f (t - x) * f x | t ∈ Icc (- 1 / 2 : ℝ) (1 / 2)}}

noncomputable def mem_Ioc_c1a_answer : ℝ := 12976 / 10000

def dropNat : ℕ → List ℤ → List ℤ
  | 0, xs => xs
  | _, [] => []
  | n + 1, _ :: xs => dropNat n xs

def dotList : List ℤ → List ℤ → ℤ
  | [], _ => 0
  | x :: xs, ys =>
    match ys with
    | [] => 0
    | y :: ys' => x * y + dotList xs ys'

def sumDots (k : ℕ) : List (List ℤ) → ℤ
  | [] => 0
  | row :: rows => dotList row (dropNat k row) + sumDots k rows

def bandSumRows (k : ℕ) (rows : List (List ℤ)) : ℤ :=
  let s := sumDots k rows
  if Nat.beq k 0 then s else 2 * s

/- ### Section 1: Boundedness and Basic `[1, 2]` Bounds on `C1a` -/

theorem autoconvValues_bddAbove {f : ℝ → ℝ} (hf : MeasureTheory.MemLp f 2) :
    BddAbove {∫ x, f (t - x) * f x | t ∈ Set.Icc (- 1 / 2 : ℝ) (1 / 2)} := by
  refine ⟨(∫ x, f x ^ 2) + ∫ x, f x ^ 2, ?_⟩
  rintro _ ⟨t, _, rfl⟩
  have ht : MeasureTheory.MemLp (fun x => f (t - x)) 2 :=
    hf.comp_measurePreserving (MeasureTheory.volume.measurePreserving_sub_left t)
  calc
    ∫ x, f (t - x) * f x ≤ ∫ x, (f (t - x) ^ 2 + f x ^ 2) := by
      apply integral_mono (ht.integrable_mul hf) (ht.integrable_sq.add hf.integrable_sq)
      intro x
      change f (t - x) * f x ≤ f (t - x) ^ 2 + f x ^ 2
      nlinarith [sq_nonneg (f (t - x) - f x), sq_nonneg (f x), sq_nonneg (f (t - x))]
    _ = (∫ x, f x ^ 2) + ∫ x, f x ^ 2 := by
      rw [integral_add ht.integrable_sq hf.integrable_sq,
        integral_sub_left_eq_self (fun x => f x ^ 2) volume t]

private lemma autoconvValues_nonneg_sSup {f : ℝ → ℝ} (hf0 : 0 ≤ f)
    (_hf : MeasureTheory.MemLp f 2) :
    0 ≤ sSup {∫ x, f (t - x) * f x | t ∈ Set.Icc (- 1 / 2 : ℝ) (1 / 2)} := by
  apply Real.sSup_nonneg
  rintro _ ⟨t, _, rfl⟩
  exact integral_nonneg fun x => mul_nonneg (hf0 _) (hf0 _)

private def shearSubLeft : ℝ × ℝ ≃ᵐ ℝ × ℝ where
  toFun z := (z.1 - z.2, z.2)
  invFun z := (z.1 + z.2, z.2)
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  measurable_toFun := (measurable_fst.sub measurable_snd).prodMk measurable_snd
  measurable_invFun := (measurable_fst.add measurable_snd).prodMk measurable_snd

private lemma integrable_of_memLp_Icc {f₁ : ℝ → ℝ} (hf : MeasureTheory.MemLp f₁ 2)
    (hsupp : ∀ x ∉ Set.Icc (-1 / 4 : ℝ) (1 / 4), f₁ x = 0) :
    Integrable f₁ := by
  let I : Set ℝ := Set.Icc (-1 / 4 : ℝ) (1 / 4)
  have hIfin : IsFiniteMeasure (volume.restrict I) := ⟨by simp [I, Real.volume_Icc]⟩
  have hIint : IntegrableOn f₁ I := (hf.restrict I).integrable (by norm_num)
  have hind : I.indicator f₁ = f₁ := by
    ext x
    by_cases hx : x ∈ I
    · simp [hx]
    · simp [hx, hsupp x hx]
  rw [← hind]
  exact (integrable_indicator_iff measurableSet_Icc).mpr hIint

private lemma integral_Icc_eq_integral_of_supp {a b : ℝ} (_hab : a ≤ b) {h : ℝ → ℝ}
    (hsupp : ∀ x ∉ Set.Icc a b, h x = 0) :
    ∫ x in Set.Icc a b, h x = ∫ x, h x :=
  setIntegral_eq_integral_of_forall_compl_eq_zero hsupp

private lemma intervalIntegral_eq_integral_of_supp {a b : ℝ} (hab : a ≤ b) {h : ℝ → ℝ}
    (hsupp : ∀ x ∉ Set.Icc a b, h x = 0) :
    ∫ x in a..b, h x = ∫ x, h x := by
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  exact integral_Icc_eq_integral_of_supp hab hsupp

private lemma autoconv_eq_zero_of_notMem {f₁ : ℝ → ℝ}
    (hsupp : ∀ x ∉ Set.Icc (-1 / 4 : ℝ) (1 / 4), f₁ x = 0)
    {t : ℝ} (ht : t ∉ Set.Icc (-1 / 2 : ℝ) (1 / 2)) :
    ∫ x, f₁ (t - x) * f₁ x = 0 := by
  have hzero : ∀ x, f₁ (t - x) * f₁ x = 0 := by
    intro x
    by_cases hx : x ∈ Set.Icc (-1 / 4 : ℝ) (1 / 4)
    · have htx : t - x ∉ Set.Icc (-1 / 4 : ℝ) (1 / 4) := by
        intro hmem
        apply ht
        simp only [Set.mem_Icc] at hx hmem ⊢
        constructor <;> linarith
      simp [hsupp (t - x) htx]
    · simp [hsupp x hx]
  simp [hzero]

private lemma integrable_autoconv_prod {f₁ : ℝ → ℝ} (hf : MeasureTheory.MemLp f₁ 2)
    (hsupp : ∀ x ∉ Set.Icc (-1 / 4 : ℝ) (1 / 4), f₁ x = 0) :
    Integrable (fun z : ℝ × ℝ => f₁ (z.1 - z.2) * f₁ z.2) (volume.prod volume) := by
  have hfint := integrable_of_memLp_Icc hf hsupp
  have hprod : Integrable (fun z : ℝ × ℝ => f₁ z.1 * f₁ z.2) (volume.prod volume) :=
    hfint.mul_prod hfint
  have hmp := measurePreserving_sub_prod (volume : Measure ℝ) (volume : Measure ℝ)
  exact (hmp.integrable_comp_emb shearSubLeft.measurableEmbedding).mpr hprod

private lemma integrable_autoconv {f₁ : ℝ → ℝ} (hf : MeasureTheory.MemLp f₁ 2)
    (hsupp : ∀ x ∉ Set.Icc (-1 / 4 : ℝ) (1 / 4), f₁ x = 0) :
    Integrable (fun t => ∫ x, f₁ (t - x) * f₁ x) :=
  (integrable_autoconv_prod hf hsupp).integral_prod_left

private lemma integral_autoconv_eq_sq {f₁ : ℝ → ℝ} (hf : MeasureTheory.MemLp f₁ 2)
    (hsupp : ∀ x ∉ Set.Icc (-1 / 4 : ℝ) (1 / 4), f₁ x = 0) :
    ∫ t, (∫ x, f₁ (t - x) * f₁ x) = (∫ x, f₁ x) ^ 2 := by
  have hprod := integrable_autoconv_prod hf hsupp
  rw [← integral_prod (fun z : ℝ × ℝ => f₁ (z.1 - z.2) * f₁ z.2) hprod]
  have hmp := measurePreserving_sub_prod (volume : Measure ℝ) (volume : Measure ℝ)
  have hcomp :
      ∫ z : ℝ × ℝ, f₁ (z.1 - z.2) * f₁ z.2 ∂(volume.prod volume) =
        ∫ z : ℝ × ℝ, f₁ z.1 * f₁ z.2 ∂(volume.prod volume) :=
    hmp.integral_comp shearSubLeft.measurableEmbedding (fun z : ℝ × ℝ => f₁ z.1 * f₁ z.2)
  rw [hcomp, integral_prod_mul, sq]

private lemma c1a_set_upper_bound :
    ∀ C ∈ {C : ℝ | ∀ ⦃f : ℝ → ℝ⦄, 0 ≤ f → MeasureTheory.MemLp f 2 →
      C * (∫ x in (- 1 / 4)..(1 / 4), f x) ^ 2
        ≤ sSup {∫ x, f (t - x) * f x | t ∈ Set.Icc (- 1 / 2 : ℝ) (1 / 2)}},
      C ≤ 2 := by
  let I : Set ℝ := Set.Icc (-1 / 4 : ℝ) (1 / 4)
  let f : ℝ → ℝ := I.indicator (fun _ => (1 : ℝ))
  have hf0 : 0 ≤ f := fun x => indicator_nonneg (fun _ _ => zero_le_one) x
  have hfm : MeasureTheory.MemLp f 2 :=
    memLp_indicator_const _ measurableSet_Icc _ (Or.inr (by simp [Real.volume_Icc]))
  have hfint : Integrable f :=
    integrable_of_memLp_Icc hfm (fun x hx => indicator_of_notMem hx _)
  have hmass_int : (∫ x, f x) = 1 / 2 := by
    change (∫ x, I.indicator (fun _ : ℝ => (1 : ℝ)) x) = 1 / 2
    rw [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul, mul_one]
    simp [Measure.real, Real.volume_Icc]
    norm_num
  have hmass_iv : (∫ x in (-1 / 4 : ℝ)..(1 / 4), f x) = 1 / 2 := by
    rw [intervalIntegral_eq_integral_of_supp (by norm_num) (fun x hx => indicator_of_notMem hx _)]
    exact hmass_int
  have hconv_le : ∀ t : ℝ, ∫ x, f (t - x) * f x ≤ 1 / 2 := by
    intro t
    have htm : MeasureTheory.MemLp (fun x => f (t - x)) 2 :=
      hfm.comp_measurePreserving (volume.measurePreserving_sub_left t)
    calc
      ∫ x, f (t - x) * f x ≤ ∫ x, f x := by
        apply integral_mono (htm.integrable_mul hfm) hfint
        intro x
        have hle1 : f (t - x) ≤ 1 := indicator_le' (fun _ _ => le_rfl) (fun _ _ => zero_le_one) _
        exact mul_le_of_le_one_left (hf0 x) hle1
      _ = 1 / 2 := hmass_int
  have hsSup_le : sSup {∫ x, f (t - x) * f x | t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2)} ≤ 1 / 2 := by
    apply csSup_le
    · refine ⟨∫ x, f (0 - x) * f x, 0, by norm_num, rfl⟩
    · rintro _ ⟨t, _, rfl⟩
      exact hconv_le t
  intro C hC
  have h := hC hf0 hfm
  rw [hmass_iv] at h
  linarith

theorem c1a_set_bddAbove :
    BddAbove {C : ℝ | ∀ ⦃f : ℝ → ℝ⦄, 0 ≤ f → MeasureTheory.MemLp f 2 →
      C * (∫ x in (- 1 / 4)..(1 / 4), f x) ^ 2
        ≤ sSup {∫ x, f (t - x) * f x | t ∈ Set.Icc (- 1 / 2 : ℝ) (1 / 2)}} :=
  ⟨2, c1a_set_upper_bound⟩

private lemma one_mem_c1a_set :
    (1 : ℝ) ∈ {C : ℝ | ∀ ⦃f : ℝ → ℝ⦄, 0 ≤ f → MeasureTheory.MemLp f 2 →
      C * (∫ x in (- 1 / 4)..(1 / 4), f x) ^ 2
        ≤ sSup {∫ x, f (t - x) * f x | t ∈ Set.Icc (- 1 / 2 : ℝ) (1 / 2)}} := by
  intro f hf0 hf
  let I : Set ℝ := Set.Icc (-1 / 4 : ℝ) (1 / 4)
  let f₁ : ℝ → ℝ := I.indicator f
  have hf₁0 : 0 ≤ f₁ := fun x => indicator_nonneg (fun y _ => hf0 y) x
  have hf₁m : MeasureTheory.MemLp f₁ 2 := hf.indicator measurableSet_Icc
  have hf₁supp : ∀ x ∉ I, f₁ x = 0 := fun x hx => indicator_of_notMem hx f
  have hf₁_le : ∀ x, f₁ x ≤ f x := fun x =>
    if hx : x ∈ I then by simp [f₁, hx] else by simp [f₁, hx]; exact hf0 x
  have hmass : (∫ x in (-1 / 4 : ℝ)..(1 / 4), f x) = ∫ x, f₁ x := by
    rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc]
    exact (integral_indicator measurableSet_Icc).symm
  let M : ℝ := sSup {∫ x, f (t - x) * f x | t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2)}
  have hg_int : Integrable (fun t => ∫ x, f₁ (t - x) * f₁ x) := integrable_autoconv hf₁m hf₁supp
  have hg_le_M : ∀ t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2), ∫ x, f₁ (t - x) * f₁ x ≤ M := by
    intro t ht
    have htm1 : MeasureTheory.MemLp (fun x => f₁ (t - x)) 2 :=
      hf₁m.comp_measurePreserving (volume.measurePreserving_sub_left t)
    have htm : MeasureTheory.MemLp (fun x => f (t - x)) 2 :=
      hf.comp_measurePreserving (volume.measurePreserving_sub_left t)
    calc
      ∫ x, f₁ (t - x) * f₁ x ≤ ∫ x, f (t - x) * f x := by
        apply integral_mono (htm1.integrable_mul hf₁m) (htm.integrable_mul hf)
        intro x
        exact mul_le_mul (hf₁_le (t - x)) (hf₁_le x) (hf₁0 x) (hf0 (t - x))
      _ ≤ M := le_csSup (autoconvValues_bddAbove hf) ⟨t, ht, rfl⟩
  have hvol_J : volume.real (Set.Icc (-1 / 2 : ℝ) (1 / 2)) = 1 := by
    simp [Measure.real, Real.volume_Icc]
    norm_num
  calc
    1 * (∫ x in (-1 / 4 : ℝ)..(1 / 4), f x) ^ 2
        = (∫ x, f₁ x) ^ 2 := by rw [one_mul, hmass]
    _ = ∫ t, (∫ x, f₁ (t - x) * f₁ x) := (integral_autoconv_eq_sq hf₁m hf₁supp).symm
    _ = ∫ t in Set.Icc (-1 / 2 : ℝ) (1 / 2), (∫ x, f₁ (t - x) * f₁ x) :=
        (integral_Icc_eq_integral_of_supp (by norm_num)
          (fun t ht => autoconv_eq_zero_of_notMem hf₁supp ht)).symm
    _ ≤ ∫ _ in Set.Icc (-1 / 2 : ℝ) (1 / 2), M := by
        apply setIntegral_mono_on hg_int.integrableOn
          (integrableOn_const (by simp [Real.volume_Icc])) measurableSet_Icc
        exact hg_le_M
    _ = M := by
        rw [setIntegral_const, smul_eq_mul, hvol_J, one_mul]

theorem one_le_c1a : 1 ≤ C1a :=
  le_csSup c1a_set_bddAbove one_mem_c1a_set

theorem c1a_le_two : C1a ≤ 2 :=
  csSup_le ⟨1, one_mem_c1a_set⟩ c1a_set_upper_bound

/- ### Section 2: Fourier Identities and Finite Bessel Inequality for Autoconvolution -/

private lemma intervalIntegral_cos_two_pi_int {k : ℤ} (hk : k ≠ 0) :
    ∫ t in (-1 / 2 : ℝ)..(1 / 2), Real.cos (2 * Real.pi * (k : ℝ) * t) = 0 := by
  have hc : 2 * Real.pi * (k : ℝ) ≠ 0 := by
    have hk' : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
    exact mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hk'
  have hfn : (fun t : ℝ => Real.cos (2 * Real.pi * (k : ℝ) * t)) =
      fun t => Real.cos ((2 * Real.pi * (k : ℝ)) * t) := by
    rfl
  rw [hfn, intervalIntegral.integral_comp_mul_left (f := Real.cos) hc]
  have hlo : (2 * Real.pi * (k : ℝ)) * (-1 / 2 : ℝ) = -((k : ℝ) * Real.pi) := by ring
  have hhi : (2 * Real.pi * (k : ℝ)) * (1 / 2 : ℝ) = (k : ℝ) * Real.pi := by ring
  rw [hlo, hhi, integral_cos, Real.sin_neg, Real.sin_int_mul_pi]
  simp

private lemma intervalIntegral_sin_two_pi_int (k : ℤ) :
    ∫ t in (-1 / 2 : ℝ)..(1 / 2), Real.sin (2 * Real.pi * (k : ℝ) * t) = 0 := by
  by_cases hk : k = 0
  · subst hk; simp
  have hc : 2 * Real.pi * (k : ℝ) ≠ 0 := by
    have hk' : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
    exact mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hk'
  have hfn : (fun t : ℝ => Real.sin (2 * Real.pi * (k : ℝ) * t)) =
      fun t => Real.sin ((2 * Real.pi * (k : ℝ)) * t) := by
    rfl
  rw [hfn, intervalIntegral.integral_comp_mul_left (f := Real.sin) hc]
  have hlo : (2 * Real.pi * (k : ℝ)) * (-1 / 2 : ℝ) = -((k : ℝ) * Real.pi) := by ring
  have hhi : (2 * Real.pi * (k : ℝ)) * (1 / 2 : ℝ) = (k : ℝ) * Real.pi := by ring
  rw [hlo, hhi, integral_sin, Real.cos_neg, sub_self, smul_zero]

private lemma intervalIntegral_cos_mul_cos {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ∫ t in (-1 / 2 : ℝ)..(1 / 2),
      Real.cos (2 * Real.pi * (m : ℝ) * t) * Real.cos (2 * Real.pi * (n : ℝ) * t) =
        if m = n then 1 / 2 else 0 := by
  have hrew : (fun t : ℝ =>
      Real.cos (2 * Real.pi * (m : ℝ) * t) * Real.cos (2 * Real.pi * (n : ℝ) * t)) =
      fun t => (Real.cos (2 * Real.pi * (((m : ℤ) + n : ℤ) : ℝ) * t) +
        Real.cos (2 * Real.pi * (((m : ℤ) - n : ℤ) : ℝ) * t)) / 2 := by
    ext t
    have hadd : 2 * Real.pi * (((m : ℤ) + n : ℤ) : ℝ) * t =
        2 * Real.pi * (m : ℝ) * t + 2 * Real.pi * (n : ℝ) * t := by push_cast; ring
    have hsub : 2 * Real.pi * (((m : ℤ) - n : ℤ) : ℝ) * t =
        2 * Real.pi * (m : ℝ) * t - 2 * Real.pi * (n : ℝ) * t := by push_cast; ring
    rw [hadd, hsub]
    linarith [Real.cos_add (2 * Real.pi * (m : ℝ) * t) (2 * Real.pi * (n : ℝ) * t),
      Real.cos_sub (2 * Real.pi * (m : ℝ) * t) (2 * Real.pi * (n : ℝ) * t)]
  rw [hrew, intervalIntegral.integral_div]
  have hc1 : IntervalIntegrable (fun t => Real.cos (2 * Real.pi * (((m : ℤ) + n : ℤ) : ℝ) * t))
      volume (-1 / 2) (1 / 2) :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have hc2 : IntervalIntegrable (fun t => Real.cos (2 * Real.pi * (((m : ℤ) - n : ℤ) : ℝ) * t))
      volume (-1 / 2) (1 / 2) :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hc1 hc2]
  have hsum_ne : (m : ℤ) + n ≠ 0 := by omega
  rw [intervalIntegral_cos_two_pi_int hsum_ne, zero_add]
  by_cases hmn : m = n
  · subst hmn
    simp
    norm_num
  · have hdiff_ne : (m : ℤ) - n ≠ 0 := by omega
    rw [intervalIntegral_cos_two_pi_int hdiff_ne, zero_div, if_neg hmn]

private lemma intervalIntegral_sin_mul_sin {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ∫ t in (-1 / 2 : ℝ)..(1 / 2),
      Real.sin (2 * Real.pi * (m : ℝ) * t) * Real.sin (2 * Real.pi * (n : ℝ) * t) =
        if m = n then 1 / 2 else 0 := by
  have hrew : (fun t : ℝ =>
      Real.sin (2 * Real.pi * (m : ℝ) * t) * Real.sin (2 * Real.pi * (n : ℝ) * t)) =
      fun t => (Real.cos (2 * Real.pi * (((m : ℤ) - n : ℤ) : ℝ) * t) -
        Real.cos (2 * Real.pi * (((m : ℤ) + n : ℤ) : ℝ) * t)) / 2 := by
    ext t
    have hadd : 2 * Real.pi * (((m : ℤ) + n : ℤ) : ℝ) * t =
        2 * Real.pi * (m : ℝ) * t + 2 * Real.pi * (n : ℝ) * t := by push_cast; ring
    have hsub : 2 * Real.pi * (((m : ℤ) - n : ℤ) : ℝ) * t =
        2 * Real.pi * (m : ℝ) * t - 2 * Real.pi * (n : ℝ) * t := by push_cast; ring
    rw [hadd, hsub]
    linarith [Real.cos_add (2 * Real.pi * (m : ℝ) * t) (2 * Real.pi * (n : ℝ) * t),
      Real.cos_sub (2 * Real.pi * (m : ℝ) * t) (2 * Real.pi * (n : ℝ) * t)]
  rw [hrew, intervalIntegral.integral_div]
  have hc1 : IntervalIntegrable (fun t => Real.cos (2 * Real.pi * (((m : ℤ) - n : ℤ) : ℝ) * t))
      volume (-1 / 2) (1 / 2) :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have hc2 : IntervalIntegrable (fun t => Real.cos (2 * Real.pi * (((m : ℤ) + n : ℤ) : ℝ) * t))
      volume (-1 / 2) (1 / 2) :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hc1 hc2]
  have hsum_ne : (m : ℤ) + n ≠ 0 := by omega
  rw [intervalIntegral_cos_two_pi_int hsum_ne, sub_zero]
  by_cases hmn : m = n
  · subst hmn
    simp
    norm_num
  · have hdiff_ne : (m : ℤ) - n ≠ 0 := by omega
    rw [intervalIntegral_cos_two_pi_int hdiff_ne, zero_div, if_neg hmn]

private lemma intervalIntegral_cos_mul_sin (m n : ℕ) :
    ∫ t in (-1 / 2 : ℝ)..(1 / 2),
      Real.cos (2 * Real.pi * (m : ℝ) * t) * Real.sin (2 * Real.pi * (n : ℝ) * t) = 0 := by
  have hrew : (fun t : ℝ =>
      Real.cos (2 * Real.pi * (m : ℝ) * t) * Real.sin (2 * Real.pi * (n : ℝ) * t)) =
      fun t => (Real.sin (2 * Real.pi * (((m : ℤ) + n : ℤ) : ℝ) * t) -
        Real.sin (2 * Real.pi * (((m : ℤ) - n : ℤ) : ℝ) * t)) / 2 := by
    ext t
    have hadd : 2 * Real.pi * (((m : ℤ) + n : ℤ) : ℝ) * t =
        2 * Real.pi * (m : ℝ) * t + 2 * Real.pi * (n : ℝ) * t := by push_cast; ring
    have hsub : 2 * Real.pi * (((m : ℤ) - n : ℤ) : ℝ) * t =
        2 * Real.pi * (m : ℝ) * t - 2 * Real.pi * (n : ℝ) * t := by push_cast; ring
    rw [hadd, hsub]
    linarith [Real.sin_add (2 * Real.pi * (m : ℝ) * t) (2 * Real.pi * (n : ℝ) * t),
      Real.sin_sub (2 * Real.pi * (m : ℝ) * t) (2 * Real.pi * (n : ℝ) * t)]
  rw [hrew, intervalIntegral.integral_div]
  have hs1 : IntervalIntegrable (fun t => Real.sin (2 * Real.pi * (((m : ℤ) + n : ℤ) : ℝ) * t))
      volume (-1 / 2) (1 / 2) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have hs2 : IntervalIntegrable (fun t => Real.sin (2 * Real.pi * (((m : ℤ) - n : ℤ) : ℝ) * t))
      volume (-1 / 2) (1 / 2) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hs1 hs2, intervalIntegral_sin_two_pi_int,
    intervalIntegral_sin_two_pi_int]
  ring

private lemma integrable_mul_bounded_cont {h φ : ℝ → ℝ} (hh : Integrable h) (hφc : Continuous φ)
    (hφb : ∃ C : ℝ, ∀ t, |φ t| ≤ C) :
    Integrable (fun t => h t * φ t) := by
  rcases hφb with ⟨C, hC⟩
  have h' : Integrable (fun t => φ t * h t) := by
    refine hh.bdd_mul (c := C) hφc.aestronglyMeasurable ?_
    filter_upwards with t
    simpa [Real.norm_eq_abs] using hC t
  simpa [mul_comm] using h'

private lemma integral_autoconv_mul_eq {f₁ φ : ℝ → ℝ} (hf : MeasureTheory.MemLp f₁ 2)
    (hsupp : ∀ x ∉ Set.Icc (-1 / 4 : ℝ) (1 / 4), f₁ x = 0)
    (hφc : Continuous φ) (hφb : ∀ t, |φ t| ≤ 1) :
    ∫ t in (-1 / 2 : ℝ)..(1 / 2), (∫ x, f₁ (t - x) * f₁ x) * φ t =
      ∫ z : ℝ × ℝ, f₁ z.1 * f₁ z.2 * φ (z.1 + z.2) ∂(volume.prod volume) := by
  have hsupp_gφ : ∀ t ∉ Set.Icc (-1 / 2 : ℝ) (1 / 2), (∫ x, f₁ (t - x) * f₁ x) * φ t = 0 := by
    intro t ht
    rw [autoconv_eq_zero_of_notMem hsupp ht, zero_mul]
  rw [intervalIntegral_eq_integral_of_supp (by norm_num) hsupp_gφ]
  have hprod : Integrable (fun z : ℝ × ℝ => f₁ (z.1 - z.2) * f₁ z.2 * φ z.1) (volume.prod volume) := by
    have h' : Integrable (fun z : ℝ × ℝ => φ z.1 * (f₁ (z.1 - z.2) * f₁ z.2)) (volume.prod volume) := by
      refine (integrable_autoconv_prod hf hsupp).bdd_mul (c := 1)
        (hφc.comp continuous_fst).aestronglyMeasurable ?_
      filter_upwards with z
      simpa [Real.norm_eq_abs] using hφb z.1
    simpa [mul_comm, mul_assoc] using h'
  have hsplit : (∫ t, (∫ x, f₁ (t - x) * f₁ x) * φ t) =
      ∫ z : ℝ × ℝ, f₁ (z.1 - z.2) * f₁ z.2 * φ z.1 ∂(volume.prod volume) := by
    rw [integral_prod _ hprod]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    exact (integral_mul_const (φ t) (fun x => f₁ (t - x) * f₁ x)).symm
  rw [hsplit]
  have hmp := measurePreserving_add_prod (volume : Measure ℝ) (volume : Measure ℝ)
  have hcomp :
      ∫ z : ℝ × ℝ, f₁ z.1 * f₁ z.2 * φ (z.1 + z.2) ∂(volume.prod volume) =
        ∫ z : ℝ × ℝ, f₁ (z.1 - z.2) * f₁ z.2 * φ z.1 ∂(volume.prod volume) := by
    simpa [shearSubLeft] using
      hmp.integral_comp shearSubLeft.symm.measurableEmbedding
        (fun z : ℝ × ℝ => f₁ (z.1 - z.2) * f₁ z.2 * φ z.1)
  exact hcomp.symm

theorem autoconv_integral_Icc_eq_one
    (f₁ : ℝ → ℝ) (hf : MeasureTheory.MemLp f₁ 2)
    (hsupp : ∀ x ∉ Set.Icc (-1 / 4 : ℝ) (1 / 4), f₁ x = 0)
    (hmass : ∫ x in Set.Icc (-1 / 4 : ℝ) (1 / 4), f₁ x = 1) :
    ∫ t in (-1 / 2 : ℝ)..(1 / 2), (∫ x, f₁ (t - x) * f₁ x) = 1 := by
  rw [intervalIntegral_eq_integral_of_supp (by norm_num)
    (fun t ht => autoconv_eq_zero_of_notMem hsupp ht)]
  rw [integral_autoconv_eq_sq hf hsupp, ← integral_Icc_eq_integral_of_supp (by norm_num) hsupp, hmass]
  norm_num

theorem autoconv_fourier_cos
    (f₁ : ℝ → ℝ) (hf : MeasureTheory.MemLp f₁ 2)
    (hsupp : ∀ x ∉ Set.Icc (-1 / 4 : ℝ) (1 / 4), f₁ x = 0)
    (k : ℕ) :
    ∫ t in (-1 / 2 : ℝ)..(1 / 2),
      (∫ x, f₁ (t - x) * f₁ x) * Real.cos (2 * Real.pi * (k : ℝ) * t) =
        (∫ x, f₁ x * Real.cos (2 * Real.pi * (k : ℝ) * x)) ^ 2 -
          (∫ x, f₁ x * Real.sin (2 * Real.pi * (k : ℝ) * x)) ^ 2 := by
  have hφc : Continuous (fun t : ℝ => Real.cos (2 * Real.pi * (k : ℝ) * t)) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  rw [integral_autoconv_mul_eq hf hsupp hφc (fun t => Real.abs_cos_le_one _)]
  have hfint := integrable_of_memLp_Icc hf hsupp
  have hcos_int : Integrable (fun x => f₁ x * Real.cos (2 * Real.pi * (k : ℝ) * x)) :=
    integrable_mul_bounded_cont hfint hφc ⟨1, fun t => Real.abs_cos_le_one _⟩
  have hsin_int : Integrable (fun x => f₁ x * Real.sin (2 * Real.pi * (k : ℝ) * x)) :=
    integrable_mul_bounded_cont hfint
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))
      ⟨1, fun t => Real.abs_sin_le_one _⟩
  have hprod_cos : Integrable (fun z : ℝ × ℝ =>
      (f₁ z.1 * Real.cos (2 * Real.pi * (k : ℝ) * z.1)) *
        (f₁ z.2 * Real.cos (2 * Real.pi * (k : ℝ) * z.2))) (volume.prod volume) :=
    hcos_int.mul_prod hcos_int
  have hprod_sin : Integrable (fun z : ℝ × ℝ =>
      (f₁ z.1 * Real.sin (2 * Real.pi * (k : ℝ) * z.1)) *
        (f₁ z.2 * Real.sin (2 * Real.pi * (k : ℝ) * z.2))) (volume.prod volume) :=
    hsin_int.mul_prod hsin_int
  have hrew : (fun z : ℝ × ℝ => f₁ z.1 * f₁ z.2 * Real.cos (2 * Real.pi * (k : ℝ) * (z.1 + z.2))) =
      fun z =>
        (f₁ z.1 * Real.cos (2 * Real.pi * (k : ℝ) * z.1)) *
          (f₁ z.2 * Real.cos (2 * Real.pi * (k : ℝ) * z.2)) -
        (f₁ z.1 * Real.sin (2 * Real.pi * (k : ℝ) * z.1)) *
          (f₁ z.2 * Real.sin (2 * Real.pi * (k : ℝ) * z.2)) := by
    ext z
    have hadd : 2 * Real.pi * (k : ℝ) * (z.1 + z.2) =
        2 * Real.pi * (k : ℝ) * z.1 + 2 * Real.pi * (k : ℝ) * z.2 := by ring
    rw [hadd, Real.cos_add]
    ring
  rw [hrew, integral_sub hprod_cos hprod_sin,
    integral_prod_mul (fun x => f₁ x * Real.cos (2 * Real.pi * (k : ℝ) * x))
      (fun x => f₁ x * Real.cos (2 * Real.pi * (k : ℝ) * x)),
    integral_prod_mul (fun x => f₁ x * Real.sin (2 * Real.pi * (k : ℝ) * x))
      (fun x => f₁ x * Real.sin (2 * Real.pi * (k : ℝ) * x)),
    sq, sq]

theorem autoconv_fourier_sin
    (f₁ : ℝ → ℝ) (hf : MeasureTheory.MemLp f₁ 2)
    (hsupp : ∀ x ∉ Set.Icc (-1 / 4 : ℝ) (1 / 4), f₁ x = 0)
    (k : ℕ) :
    ∫ t in (-1 / 2 : ℝ)..(1 / 2),
      (∫ x, f₁ (t - x) * f₁ x) * Real.sin (2 * Real.pi * (k : ℝ) * t) =
        2 * (∫ x, f₁ x * Real.cos (2 * Real.pi * (k : ℝ) * x)) *
          (∫ x, f₁ x * Real.sin (2 * Real.pi * (k : ℝ) * x)) := by
  have hφc : Continuous (fun t : ℝ => Real.sin (2 * Real.pi * (k : ℝ) * t)) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_id)
  rw [integral_autoconv_mul_eq hf hsupp hφc (fun t => Real.abs_sin_le_one _)]
  have hfint := integrable_of_memLp_Icc hf hsupp
  have hcos_int : Integrable (fun x => f₁ x * Real.cos (2 * Real.pi * (k : ℝ) * x)) :=
    integrable_mul_bounded_cont hfint
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))
      ⟨1, fun t => Real.abs_cos_le_one _⟩
  have hsin_int : Integrable (fun x => f₁ x * Real.sin (2 * Real.pi * (k : ℝ) * x)) :=
    integrable_mul_bounded_cont hfint hφc ⟨1, fun t => Real.abs_sin_le_one _⟩
  have hprod_sc : Integrable (fun z : ℝ × ℝ =>
      (f₁ z.1 * Real.sin (2 * Real.pi * (k : ℝ) * z.1)) *
        (f₁ z.2 * Real.cos (2 * Real.pi * (k : ℝ) * z.2))) (volume.prod volume) :=
    hsin_int.mul_prod hcos_int
  have hprod_cs : Integrable (fun z : ℝ × ℝ =>
      (f₁ z.1 * Real.cos (2 * Real.pi * (k : ℝ) * z.1)) *
        (f₁ z.2 * Real.sin (2 * Real.pi * (k : ℝ) * z.2))) (volume.prod volume) :=
    hcos_int.mul_prod hsin_int
  have hrew : (fun z : ℝ × ℝ => f₁ z.1 * f₁ z.2 * Real.sin (2 * Real.pi * (k : ℝ) * (z.1 + z.2))) =
      fun z =>
        (f₁ z.1 * Real.sin (2 * Real.pi * (k : ℝ) * z.1)) *
          (f₁ z.2 * Real.cos (2 * Real.pi * (k : ℝ) * z.2)) +
        (f₁ z.1 * Real.cos (2 * Real.pi * (k : ℝ) * z.1)) *
          (f₁ z.2 * Real.sin (2 * Real.pi * (k : ℝ) * z.2)) := by
    ext z
    have hadd : 2 * Real.pi * (k : ℝ) * (z.1 + z.2) =
        2 * Real.pi * (k : ℝ) * z.1 + 2 * Real.pi * (k : ℝ) * z.2 := by ring
    rw [hadd, Real.sin_add]
    ring
  rw [hrew, integral_add hprod_sc hprod_cs,
    integral_prod_mul (fun x => f₁ x * Real.sin (2 * Real.pi * (k : ℝ) * x))
      (fun x => f₁ x * Real.cos (2 * Real.pi * (k : ℝ) * x)),
    integral_prod_mul (fun x => f₁ x * Real.cos (2 * Real.pi * (k : ℝ) * x))
      (fun x => f₁ x * Real.sin (2 * Real.pi * (k : ℝ) * x))]
  ring

theorem finite_bessel_autoconv
    (f₁ : ℝ → ℝ) (hf0 : 0 ≤ f₁) (hf : MeasureTheory.MemLp f₁ 2)
    (hsupp : ∀ x ∉ Set.Icc (-1 / 4 : ℝ) (1 / 4), f₁ x = 0)
    (hmass : ∫ x in Set.Icc (-1 / 4 : ℝ) (1 / 4), f₁ x = 1)
    (K : ℕ) {Ω : ℝ}
    (hΩ : ∀ t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2), (∫ x, f₁ (t - x) * f₁ x) ≤ Ω) :
    2 * ∑ k ∈ Finset.Icc 1 K,
      ((∫ x, f₁ x * Real.cos (2 * Real.pi * (k : ℝ) * x)) ^ 2 +
        (∫ x, f₁ x * Real.sin (2 * Real.pi * (k : ℝ) * x)) ^ 2) ^ 2 ≤ Ω - 1 := by
  let g : ℝ → ℝ := fun t => ∫ x, f₁ (t - x) * f₁ x
  let a : ℕ → ℝ := fun k => ∫ x, f₁ x * Real.cos (2 * Real.pi * (k : ℝ) * x)
  let b : ℕ → ℝ := fun k => ∫ x, f₁ x * Real.sin (2 * Real.pi * (k : ℝ) * x)
  let c : ℕ → ℝ := fun k => a k ^ 2 - b k ^ 2
  let s : ℕ → ℝ := fun k => 2 * a k * b k
  let term : ℕ → ℝ → ℝ := fun k t =>
    2 * (c k * Real.cos (2 * Real.pi * (k : ℝ) * t) +
      s k * Real.sin (2 * Real.pi * (k : ℝ) * t))
  let S : ℝ → ℝ := fun t => ∑ k ∈ Finset.Icc 1 K, term k t
  let gK : ℝ → ℝ := fun t => 1 + S t
  have hg_nonneg : ∀ t, 0 ≤ g t := fun t => integral_nonneg fun x => mul_nonneg (hf0 _) (hf0 _)
  have hg_int : Integrable g := integrable_autoconv hf hsupp
  have hg_one : ∫ t in (-1 / 2 : ℝ)..(1 / 2), g t = 1 :=
    autoconv_integral_Icc_eq_one f₁ hf hsupp hmass
  have hg_sq_int : IntegrableOn (fun t => g t ^ 2) (Set.Icc (-1 / 2 : ℝ) (1 / 2)) := by
    refine (hg_int.integrableOn.const_mul Ω).mono' (hg_int.aestronglyMeasurable.pow 2).restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hgt : 0 ≤ g t := hg_nonneg t
    have hle : g t ^ 2 ≤ Ω * g t := by
      rw [sq]
      exact mul_le_mul_of_nonneg_right (hΩ t ht) hgt
    simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (g t)),
      abs_of_nonneg (le_trans (sq_nonneg (g t)) hle)] using hle
  have hg_sq_iv : IntervalIntegrable (fun t => g t ^ 2) volume (-1 / 2) (1 / 2) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mpr hg_sq_int
  have hg_sq_le : ∫ t in (-1 / 2 : ℝ)..(1 / 2), g t ^ 2 ≤ Ω := by
    rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc]
    calc
      ∫ t in Set.Icc (-1 / 2 : ℝ) (1 / 2), g t ^ 2
          ≤ ∫ t in Set.Icc (-1 / 2 : ℝ) (1 / 2), Ω * g t := by
        apply setIntegral_mono_on hg_sq_int (hg_int.integrableOn.const_mul Ω) measurableSet_Icc
        intro t ht
        rw [sq]
        exact mul_le_mul_of_nonneg_right (hΩ t ht) (hg_nonneg t)
      _ = Ω * ∫ t in Set.Icc (-1 / 2 : ℝ) (1 / 2), g t := integral_const_mul _ _
      _ = Ω * ∫ t in (-1 / 2 : ℝ)..(1 / 2), g t := by
        rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc]
      _ = Ω := by rw [hg_one, mul_one]
  have hterm_cont : ∀ k, Continuous (term k) := fun k =>
    continuous_const.mul
      ((continuous_const.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))).add
        (continuous_const.mul (Real.continuous_sin.comp (continuous_const.mul continuous_id))))
  have hS_cont : Continuous S := continuous_finsetSum _ (fun k _ => hterm_cont k)
  have hgK_cont : Continuous gK := continuous_const.add hS_cont
  have hgK_sq_iv : IntervalIntegrable (fun t => gK t ^ 2) volume (-1 / 2) (1 / 2) :=
    (hgK_cont.pow 2).intervalIntegrable _ _
  have hS_bound : ∃ C : ℝ, ∀ t, |S t| ≤ C := by
    refine ⟨∑ k ∈ Finset.Icc 1 K, 2 * (|c k| + |s k|), fun t => ?_⟩
    calc
      |S t| ≤ ∑ k ∈ Finset.Icc 1 K, |term k t| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.Icc 1 K, 2 * (|c k| + |s k|) := by
        apply Finset.sum_le_sum
        intro k _
        have hc_b : |c k * Real.cos (2 * Real.pi * (k : ℝ) * t)| ≤ |c k| := by
          rw [abs_mul]
          exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
        have hs_b : |s k * Real.sin (2 * Real.pi * (k : ℝ) * t)| ≤ |s k| := by
          rw [abs_mul]
          exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
        dsimp [term]
        rw [abs_mul, abs_of_nonneg (by norm_num)]
        linarith [abs_add_le (c k * Real.cos (2 * Real.pi * (k : ℝ) * t))
          (s k * Real.sin (2 * Real.pi * (k : ℝ) * t))]
  have hgK_bound : ∃ C : ℝ, ∀ t, |gK t| ≤ C := by
    rcases hS_bound with ⟨C, hC⟩
    refine ⟨1 + C, fun t => ?_⟩
    have h1 : |(1 : ℝ)| = 1 := abs_one
    linarith [abs_add_le (1 : ℝ) (S t), h1, hC t]
  have hggK_int : Integrable (fun t => g t * gK t) :=
    integrable_mul_bounded_cont hg_int hgK_cont hgK_bound
  have hggK_iv : IntervalIntegrable (fun t => g t * gK t) volume (-1 / 2) (1 / 2) :=
    hggK_int.intervalIntegrable
  have h_ggK_eq : ∫ t in (-1 / 2 : ℝ)..(1 / 2), g t * gK t =
      1 + 2 * ∑ k ∈ Finset.Icc 1 K, (c k ^ 2 + s k ^ 2) := by
    have hmul_sum : (fun t => g t * gK t) =
        fun t => g t + ∑ k ∈ Finset.Icc 1 K,
          (2 * c k * (g t * Real.cos (2 * Real.pi * (k : ℝ) * t)) +
           2 * s k * (g t * Real.sin (2 * Real.pi * (k : ℝ) * t))) := by
      ext t
      dsimp [gK, S, term]
      rw [mul_add, mul_one, Finset.mul_sum]
      refine congr_arg (g t + ·) (Finset.sum_congr rfl fun k _ => ?_)
      ring
    rw [hmul_sum]
    have hg_iv : IntervalIntegrable g volume (-1 / 2) (1 / 2) := hg_int.intervalIntegrable
    have hcos_iv : ∀ k : ℕ, IntervalIntegrable
        (fun t => g t * Real.cos (2 * Real.pi * (k : ℝ) * t)) volume (-1 / 2) (1 / 2) :=
      fun k => (integrable_mul_bounded_cont hg_int
        (Real.continuous_cos.comp (continuous_const.mul continuous_id))
        ⟨1, fun t => Real.abs_cos_le_one _⟩).intervalIntegrable
    have hsin_iv : ∀ k : ℕ, IntervalIntegrable
        (fun t => g t * Real.sin (2 * Real.pi * (k : ℝ) * t)) volume (-1 / 2) (1 / 2) :=
      fun k => (integrable_mul_bounded_cont hg_int
        (Real.continuous_sin.comp (continuous_const.mul continuous_id))
        ⟨1, fun t => Real.abs_sin_le_one _⟩).intervalIntegrable
    have hterm_iv : ∀ k ∈ Finset.Icc 1 K, IntervalIntegrable
        (fun t => 2 * c k * (g t * Real.cos (2 * Real.pi * (k : ℝ) * t)) +
          2 * s k * (g t * Real.sin (2 * Real.pi * (k : ℝ) * t))) volume (-1 / 2) (1 / 2) :=
      fun k _ => ((hcos_iv k).const_mul _).add ((hsin_iv k).const_mul _)
    have hsum_iv : IntervalIntegrable (fun t => ∑ k ∈ Finset.Icc 1 K,
        (2 * c k * (g t * Real.cos (2 * Real.pi * (k : ℝ) * t)) +
          2 * s k * (g t * Real.sin (2 * Real.pi * (k : ℝ) * t)))) volume (-1 / 2) (1 / 2) := by
      have hfun : (fun t => ∑ k ∈ Finset.Icc 1 K,
          (2 * c k * (g t * Real.cos (2 * Real.pi * (k : ℝ) * t)) +
            2 * s k * (g t * Real.sin (2 * Real.pi * (k : ℝ) * t)))) =
          ∑ k ∈ Finset.Icc 1 K, fun t =>
            2 * c k * (g t * Real.cos (2 * Real.pi * (k : ℝ) * t)) +
              2 * s k * (g t * Real.sin (2 * Real.pi * (k : ℝ) * t)) := by
        ext t; simp only [Finset.sum_apply]
      rw [hfun]
      exact IntervalIntegrable.sum (Finset.Icc 1 K) hterm_iv
    rw [intervalIntegral.integral_add hg_iv hsum_iv]
    rw [hg_one, intervalIntegral.integral_finsetSum hterm_iv]
    have hsum_val : ∑ k ∈ Finset.Icc 1 K, ∫ t in (-1 / 2 : ℝ)..(1 / 2),
        (2 * c k * (g t * Real.cos (2 * Real.pi * (k : ℝ) * t)) +
          2 * s k * (g t * Real.sin (2 * Real.pi * (k : ℝ) * t))) =
        2 * ∑ k ∈ Finset.Icc 1 K, (c k ^ 2 + s k ^ 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [intervalIntegral.integral_add ((hcos_iv k).const_mul _) ((hsin_iv k).const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      have hfc : ∫ t in (-1 / 2 : ℝ)..(1 / 2), g t * Real.cos (2 * Real.pi * (k : ℝ) * t) = c k :=
        autoconv_fourier_cos f₁ hf hsupp k
      have hfs : ∫ t in (-1 / 2 : ℝ)..(1 / 2), g t * Real.sin (2 * Real.pi * (k : ℝ) * t) = s k :=
        autoconv_fourier_sin f₁ hf hsupp k
      rw [hfc, hfs]
      ring
    rw [hsum_val]
  have h_S_int : ∫ t in (-1 / 2 : ℝ)..(1 / 2), S t = 0 := by
    change ∫ t in (-1 / 2 : ℝ)..(1 / 2), ∑ k ∈ Finset.Icc 1 K, term k t = 0
    rw [intervalIntegral.integral_finsetSum (fun k _ => (hterm_cont k).intervalIntegrable _ _)]
    apply Finset.sum_eq_zero
    intro k hk
    have hk1 : (k : ℤ) ≠ 0 := by
      have := (Finset.mem_Icc.mp hk).1
      omega
    have hc_iv : IntervalIntegrable (fun t => Real.cos (2 * Real.pi * (k : ℝ) * t))
        volume (-1 / 2) (1 / 2) :=
      (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
    have hs_iv : IntervalIntegrable (fun t => Real.sin (2 * Real.pi * (k : ℝ) * t))
        volume (-1 / 2) (1 / 2) :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
    dsimp [term]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (hc_iv.const_mul _) (hs_iv.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have hcos0 := intervalIntegral_cos_two_pi_int hk1
    have hsin0 := intervalIntegral_sin_two_pi_int (k : ℤ)
    simp only [Int.cast_natCast] at hcos0 hsin0
    rw [hcos0, hsin0]
    ring
  have h_S_sq_int : ∫ t in (-1 / 2 : ℝ)..(1 / 2), S t ^ 2 =
      2 * ∑ k ∈ Finset.Icc 1 K, (c k ^ 2 + s k ^ 2) := by
    have hrew : (fun t => S t ^ 2) =
        fun t => ∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 K, term k t * term l t := by
      ext t
      dsimp [S]
      rw [sq, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
    rw [hrew, intervalIntegral.integral_finsetSum]
    · have hinner : ∀ k ∈ Finset.Icc 1 K,
          ∫ t in (-1 / 2 : ℝ)..(1 / 2), ∑ l ∈ Finset.Icc 1 K, term k t * term l t =
            2 * (c k ^ 2 + s k ^ 2) := by
        intro k hk
        have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
        rw [intervalIntegral.integral_finsetSum]
        · have hpair : ∀ l ∈ Finset.Icc 1 K,
              ∫ t in (-1 / 2 : ℝ)..(1 / 2), term k t * term l t =
                if l = k then 2 * (c k ^ 2 + s k ^ 2) else 0 := by
            intro l hl
            have hl1 : 1 ≤ l := (Finset.mem_Icc.mp hl).1
            have hexp : (fun t => term k t * term l t) = fun t =>
                (4 * c k * c l) * (Real.cos (2 * Real.pi * (k : ℝ) * t) * Real.cos (2 * Real.pi * (l : ℝ) * t)) +
                (4 * c k * s l) * (Real.cos (2 * Real.pi * (k : ℝ) * t) * Real.sin (2 * Real.pi * (l : ℝ) * t)) +
                (4 * s k * c l) * (Real.cos (2 * Real.pi * (l : ℝ) * t) * Real.sin (2 * Real.pi * (k : ℝ) * t)) +
                (4 * s k * s l) * (Real.sin (2 * Real.pi * (k : ℝ) * t) * Real.sin (2 * Real.pi * (l : ℝ) * t)) := by
              ext t; dsimp [term]; ring
            have iv1 : IntervalIntegrable (fun t =>
                Real.cos (2 * Real.pi * (k : ℝ) * t) * Real.cos (2 * Real.pi * (l : ℝ) * t))
                volume (-1 / 2) (1 / 2) :=
              ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).mul
                (Real.continuous_cos.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
            have iv2 : IntervalIntegrable (fun t =>
                Real.cos (2 * Real.pi * (k : ℝ) * t) * Real.sin (2 * Real.pi * (l : ℝ) * t))
                volume (-1 / 2) (1 / 2) :=
              ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).mul
                (Real.continuous_sin.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
            have iv3 : IntervalIntegrable (fun t =>
                Real.cos (2 * Real.pi * (l : ℝ) * t) * Real.sin (2 * Real.pi * (k : ℝ) * t))
                volume (-1 / 2) (1 / 2) :=
              ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).mul
                (Real.continuous_sin.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
            have iv4 : IntervalIntegrable (fun t =>
                Real.sin (2 * Real.pi * (k : ℝ) * t) * Real.sin (2 * Real.pi * (l : ℝ) * t))
                volume (-1 / 2) (1 / 2) :=
              ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).mul
                (Real.continuous_sin.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
            rw [hexp,
              intervalIntegral.integral_add (((iv1.const_mul _).add (iv2.const_mul _)).add (iv3.const_mul _)) (iv4.const_mul _),
              intervalIntegral.integral_add ((iv1.const_mul _).add (iv2.const_mul _)) (iv3.const_mul _),
              intervalIntegral.integral_add (iv1.const_mul _) (iv2.const_mul _),
              intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
              intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
            rw [intervalIntegral_cos_mul_cos hk1 hl1, intervalIntegral_cos_mul_sin k l,
              intervalIntegral_cos_mul_sin l k, intervalIntegral_sin_mul_sin hk1 hl1]
            by_cases hlk : l = k
            · subst hlk; simp; ring
            · have hkl : k ≠ l := Ne.symm hlk
              simp [hlk, hkl]
          rw [Finset.sum_congr rfl hpair, Finset.sum_ite_eq', if_pos hk]
        · intro l _; exact ((hterm_cont k).mul (hterm_cont l)).intervalIntegrable _ _
      rw [Finset.sum_congr rfl hinner, Finset.mul_sum]
    · intro k _; exact (continuous_finsetSum _ fun l _ => (hterm_cont k).mul (hterm_cont l)).intervalIntegrable _ _
  have h_gK_sq_eq : ∫ t in (-1 / 2 : ℝ)..(1 / 2), gK t ^ 2 =
      1 + 2 * ∑ k ∈ Finset.Icc 1 K, (c k ^ 2 + s k ^ 2) := by
    have hrew : (fun t => gK t ^ 2) = fun t => (1 : ℝ) + 2 * S t + S t ^ 2 := by
      ext t; dsimp [gK]; ring
    have iv1 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume (-1 / 2) (1 / 2) :=
      intervalIntegrable_const
    have iv2 : IntervalIntegrable (fun t => 2 * S t) volume (-1 / 2) (1 / 2) :=
      (hS_cont.intervalIntegrable _ _).const_mul 2
    have iv3 : IntervalIntegrable (fun t => S t ^ 2) volume (-1 / 2) (1 / 2) :=
      (hS_cont.pow 2).intervalIntegrable _ _
    rw [hrew, intervalIntegral.integral_add (iv1.add iv2) iv3,
      intervalIntegral.integral_add iv1 iv2,
      intervalIntegral.integral_const, smul_eq_mul,
      intervalIntegral.integral_const_mul, h_S_int, h_S_sq_int]
    norm_num
  have h_diff_sq_nonneg : 0 ≤ ∫ t in (-1 / 2 : ℝ)..(1 / 2), (g t - gK t) ^ 2 := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro t _; exact sq_nonneg _
  have h_expand_eq : (fun t => (g t - gK t) ^ 2) =
      fun t => g t ^ 2 - 2 * (g t * gK t) + gK t ^ 2 := by
    ext t; ring
  rw [h_expand_eq,
    intervalIntegral.integral_add (hg_sq_iv.sub (hggK_iv.const_mul 2)) hgK_sq_iv,
    intervalIntegral.integral_sub hg_sq_iv (hggK_iv.const_mul 2),
    intervalIntegral.integral_const_mul, h_ggK_eq, h_gK_sq_eq] at h_diff_sq_nonneg
  have hcs_sq : ∑ k ∈ Finset.Icc 1 K, (a k ^ 2 + b k ^ 2) ^ 2 =
      ∑ k ∈ Finset.Icc 1 K, (c k ^ 2 + s k ^ 2) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    dsimp [c, s]; ring
  rw [hcs_sq]
  linarith

/- ### Section 3: Real-Symmetric Gram Identities and Nonnegativity Lemmas -/

private lemma dropNat_length (k : ℕ) (row : List ℤ) :
    (dropNat k row).length = row.length - k := by
  induction k generalizing row with
  | zero => simp [dropNat]
  | succ k ih =>
    cases row with
    | nil => simp [dropNat]
    | cons x xs => simp [dropNat, ih]

private lemma dropNat_getD (k i : ℕ) (row : List ℤ) :
    (dropNat k row).getD i 0 = row.getD (i + k) 0 := by
  induction k generalizing row with
  | zero => simp [dropNat]
  | succ k ih =>
    cases row with
    | nil => simp [dropNat]
    | cons x xs =>
      have hidx : i + (k + 1) = (i + k) + 1 := by omega
      change (dropNat k xs).getD i 0 = (x :: xs).getD (i + (k + 1)) 0
      rw [ih xs, hidx]
      rfl

private lemma dotList_eq_sum (xs ys : List ℤ) :
    dotList xs ys =
      ∑ i ∈ Finset.range (min xs.length ys.length), xs.getD i 0 * ys.getD i 0 := by
  induction xs generalizing ys with
  | nil => simp [dotList]
  | cons x xs ih =>
    cases ys with
    | nil => simp [dotList]
    | cons y ys =>
      have hmin : min (x :: xs).length (y :: ys).length = min xs.length ys.length + 1 := by
        simp only [List.length_cons]; omega
      change x * y + dotList xs ys =
        ∑ i ∈ Finset.range (min (x :: xs).length (y :: ys).length),
          (x :: xs).getD i 0 * (y :: ys).getD i 0
      rw [hmin, Finset.sum_range_succ', ih ys]
      have hx0 : (x :: xs).getD 0 0 = x := rfl
      have hy0 : (y :: ys).getD 0 0 = y := rfl
      have hxs : ∀ i, (x :: xs).getD (i + 1) 0 = xs.getD i 0 := fun _ => rfl
      have hys : ∀ i, (y :: ys).getD (i + 1) 0 = ys.getD i 0 := fun _ => rfl
      simp_rw [hxs, hys]
      rw [hx0, hy0]
      ring

private lemma dotList_dropNat_eq_sum (k : ℕ) (row : List ℤ) :
    dotList row (dropNat k row) =
      ∑ i ∈ Finset.range (row.length - k), row.getD i 0 * row.getD (i + k) 0 := by
  rw [dotList_eq_sum, dropNat_length, min_eq_right (Nat.sub_le _ _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dropNat_getD]

theorem trigSqSum_row_eq (K : ℕ) (row : List ℤ) (hlen : row.length = K + 1) (θ : ℝ) :
    (∑ i ∈ Finset.range (K + 1), ((row.getD i 0 : ℤ) : ℝ) * Real.cos (2 * Real.pi * (i : ℝ) * θ)) ^ 2 +
    (∑ i ∈ Finset.range (K + 1), ((row.getD i 0 : ℤ) : ℝ) * Real.sin (2 * Real.pi * (i : ℝ) * θ)) ^ 2 =
      (dotList row row : ℝ) +
        ∑ k ∈ Finset.Icc 1 K, (2 * dotList row (dropNat k row) : ℝ) * Real.cos (2 * Real.pi * (k : ℝ) * θ) := by
  let u : ℕ → ℝ := fun i => ((row.getD i 0 : ℤ) : ℝ)
  let α : ℝ := 2 * Real.pi * θ
  let S : Finset ℕ := Finset.range (K + 1)
  let F : ℕ → ℕ → ℝ := fun i j => u i * u j * Real.cos ((i : ℝ) * α - (j : ℝ) * α)
  have hcos_pair : ∀ i j : ℕ,
      (u i * Real.cos (2 * Real.pi * (i : ℝ) * θ)) * (u j * Real.cos (2 * Real.pi * (j : ℝ) * θ)) +
      (u i * Real.sin (2 * Real.pi * (i : ℝ) * θ)) * (u j * Real.sin (2 * Real.pi * (j : ℝ) * θ)) = F i j := by
    intro i j
    have hi : 2 * Real.pi * (i : ℝ) * θ = (i : ℝ) * α := by dsimp [α]; ring
    have hj : 2 * Real.pi * (j : ℝ) * θ = (j : ℝ) * α := by dsimp [α]; ring
    dsimp [F]
    rw [hi, hj, Real.cos_sub]
    ring
  have hexpand :
      (∑ i ∈ S, u i * Real.cos (2 * Real.pi * (i : ℝ) * θ)) ^ 2 +
      (∑ i ∈ S, u i * Real.sin (2 * Real.pi * (i : ℝ) * θ)) ^ 2 =
        ∑ p ∈ S ×ˢ S, F p.1 p.2 := by
    rw [sq, sq, Finset.sum_mul, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    have hcongr : ∑ i ∈ S, (∑ j ∈ S,
        (u i * Real.cos (2 * Real.pi * (i : ℝ) * θ)) * (u j * Real.cos (2 * Real.pi * (j : ℝ) * θ)) +
        ∑ j ∈ S, (u i * Real.sin (2 * Real.pi * (i : ℝ) * θ)) * (u j * Real.sin (2 * Real.pi * (j : ℝ) * θ))) =
        ∑ i ∈ S, ∑ j ∈ S, F i j := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => hcos_pair i j
    rw [hcongr, Finset.sum_product']
  have hsplit_eq : ∑ p ∈ S ×ˢ S, F p.1 p.2 =
      (∑ p ∈ (S ×ˢ S).filter (fun p => p.1 = p.2), F p.1 p.2) +
      ∑ p ∈ (S ×ˢ S).filter (fun p => ¬ p.1 = p.2), F p.1 p.2 :=
    (Finset.sum_filter_add_sum_filter_not (S ×ˢ S) (fun p => p.1 = p.2) (fun p => F p.1 p.2)).symm
  have hsplit_lt : ∑ p ∈ (S ×ˢ S).filter (fun p => ¬ p.1 = p.2), F p.1 p.2 =
      (∑ p ∈ (S ×ˢ S).filter (fun p => p.1 < p.2), F p.1 p.2) +
      ∑ p ∈ (S ×ˢ S).filter (fun p => p.2 < p.1), F p.1 p.2 := by
    have h1 := (Finset.sum_filter_add_sum_filter_not
      ((S ×ˢ S).filter (fun p => ¬ p.1 = p.2)) (fun p => p.1 < p.2) (fun p => F p.1 p.2)).symm
    have hA : ((S ×ˢ S).filter (fun p => ¬ p.1 = p.2)).filter (fun p => p.1 < p.2) =
        (S ×ˢ S).filter (fun p => p.1 < p.2) := by
      ext p; simp only [Finset.mem_filter]; constructor <;> rintro h
      · exact ⟨h.1.1, h.2⟩
      · exact ⟨⟨h.1, Nat.ne_of_lt h.2⟩, h.2⟩
    have hB : ((S ×ˢ S).filter (fun p => ¬ p.1 = p.2)).filter (fun p => ¬ p.1 < p.2) =
        (S ×ˢ S).filter (fun p => p.2 < p.1) := by
      ext p; simp only [Finset.mem_filter]; constructor <;> rintro h
      · exact ⟨h.1.1, by omega⟩
      · exact ⟨⟨h.1, by omega⟩, by omega⟩
    rw [hA, hB] at h1
    exact h1
  have hlower_eq_upper : ∑ p ∈ (S ×ˢ S).filter (fun p => p.2 < p.1), F p.1 p.2 =
      ∑ p ∈ (S ×ˢ S).filter (fun p => p.1 < p.2), F p.1 p.2 := by
    refine Finset.sum_bij (fun p _ => p.swap) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product] at hp ⊢
      exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
    · intro p _ q _ hpq
      exact Prod.ext (congrArg Prod.snd hpq) (congrArg Prod.fst hpq)
    · intro q hq
      refine ⟨q.swap, ?_, by ext <;> rfl⟩
      simp only [Finset.mem_filter, Finset.mem_product] at hq ⊢
      exact ⟨⟨hq.1.2, hq.1.1⟩, hq.2⟩
    · intro p _
      dsimp [F]
      have hneg : (p.1 : ℝ) * α - (p.2 : ℝ) * α = -((p.2 : ℝ) * α - (p.1 : ℝ) * α) := by ring
      rw [hneg, Real.cos_neg]
      ring
  have hdiag : ∑ p ∈ (S ×ˢ S).filter (fun p => p.1 = p.2), F p.1 p.2 = (dotList row row : ℝ) := by
    have hbij : ∑ p ∈ (S ×ˢ S).filter (fun p => p.1 = p.2), F p.1 p.2 =
        ∑ i ∈ S, u i * u i := by
      refine Finset.sum_bij (fun p _ => p.1) ?_ ?_ ?_ ?_
      · intro p hp
        exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
      · intro p hp q hq hpq
        have hp' := (Finset.mem_filter.mp hp).2
        have hq' := (Finset.mem_filter.mp hq).2
        exact Prod.ext hpq (by omega)
      · intro i hi
        refine ⟨(i, i), ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨hi, hi⟩, trivial⟩
      · intro p hp
        have hp' := (Finset.mem_filter.mp hp).2
        dsimp [F]
        rw [hp', sub_self, Real.cos_zero, mul_one]
    rw [hbij]
    have hdot := dotList_dropNat_eq_sum 0 row
    rw [dropNat, hlen, Nat.sub_zero] at hdot
    have hcast : (dotList row row : ℝ) = ∑ i ∈ S, u i * u i := by
      rw [hdot]
      push_cast
      rfl
    exact hcast.symm
  have hupper : ∑ p ∈ (S ×ˢ S).filter (fun p => p.1 < p.2), F p.1 p.2 =
      ∑ k ∈ Finset.Icc 1 K, (dotList row (dropNat k row) : ℝ) * Real.cos (2 * Real.pi * (k : ℝ) * θ) := by
    have hsig :
        ∑ x ∈ (Finset.Icc 1 K).sigma (fun k => Finset.range (K + 1 - k)), F x.2 (x.2 + x.1) =
          ∑ p ∈ (S ×ˢ S).filter (fun p => p.1 < p.2), F p.1 p.2 := by
      refine Finset.sum_bij (fun x _ => (x.2, x.2 + x.1)) ?_ ?_ ?_ ?_
      · intro x hx
        simp only [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_range] at hx
        simp only [Finset.mem_filter, Finset.mem_product, S, Finset.mem_range]
        exact ⟨⟨by omega, by omega⟩, by omega⟩
      · intro x _ y _ hxy
        rcases x with ⟨k₁, i₁⟩
        rcases y with ⟨k₂, i₂⟩
        have h2 : i₁ = i₂ := congrArg Prod.fst hxy
        have h12 : i₁ + k₁ = i₂ + k₂ := congrArg Prod.snd hxy
        have h1 : k₁ = k₂ := by omega
        exact Sigma.ext h1 (by subst h1; exact heq_of_eq h2)
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_product, S, Finset.mem_range] at hp
        refine ⟨⟨p.2 - p.1, p.1⟩, ?_, ?_⟩
        · simp only [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_range]
          exact ⟨⟨by omega, by omega⟩, by omega⟩
        · exact Prod.ext rfl (by dsimp; omega)
      · intro _ _; rfl
    rw [← hsig, Finset.sum_sigma]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hF : ∀ i ∈ Finset.range (K + 1 - k),
        F i (i + k) = (u i * u (i + k)) * Real.cos (2 * Real.pi * (k : ℝ) * θ) := by
      intro i _
      dsimp [F]
      have harg : (i : ℝ) * α - ((i + k : ℕ) : ℝ) * α = -(2 * Real.pi * (k : ℝ) * θ) := by
        dsimp [α]; push_cast; ring
      rw [harg, Real.cos_neg]
    rw [Finset.sum_congr rfl hF, ← Finset.sum_mul]
    congr 1
    have hdot := dotList_dropNat_eq_sum k row
    rw [hlen] at hdot
    rw [hdot]
    push_cast
    rfl
  rw [hexpand, hsplit_eq, hsplit_lt, hlower_eq_upper, hdiag, hupper, ← two_mul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

noncomputable def trigSqSum (K : ℕ) (rows : List (List ℤ)) (θ : ℝ) : ℝ :=
  match rows with
  | [] => 0
  | row :: rest =>
    ((∑ i ∈ Finset.range (K + 1), ((row.getD i 0 : ℤ) : ℝ) * Real.cos (2 * Real.pi * (i : ℝ) * θ)) ^ 2 +
     (∑ i ∈ Finset.range (K + 1), ((row.getD i 0 : ℤ) : ℝ) * Real.sin (2 * Real.pi * (i : ℝ) * θ)) ^ 2) +
    trigSqSum K rest θ

lemma trigSqSum_nonneg (K : ℕ) (rows : List (List ℤ)) (θ : ℝ) :
    0 ≤ trigSqSum K rows θ := by
  induction rows with
  | nil => simp [trigSqSum]
  | cons row rest ih =>
    simp only [trigSqSum]
    exact add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) ih

lemma trigSqSum_eq_bandSum (K : ℕ) (rows : List (List ℤ))
    (hlen : ∀ row ∈ rows, row.length = K + 1) (θ : ℝ) :
    trigSqSum K rows θ =
      (bandSumRows 0 rows : ℝ) +
        ∑ k ∈ Finset.Icc 1 K, (bandSumRows k rows : ℝ) * Real.cos (2 * Real.pi * (k : ℝ) * θ) := by
  induction rows with
  | nil =>
    simp [trigSqSum, bandSumRows, sumDots]
  | cons row rest ih =>
    have hrow : row.length = K + 1 := hlen row (by simp)
    have hrest : ∀ r ∈ rest, r.length = K + 1 := fun r hr => hlen r (by simp [hr])
    simp only [trigSqSum]
    rw [trigSqSum_row_eq K row hrow θ, ih hrest]
    have hband0 : (bandSumRows 0 (row :: rest) : ℝ) =
        (dotList row row : ℝ) + (bandSumRows 0 rest : ℝ) := by
      simp [bandSumRows, sumDots, dropNat]
    have hbandk : ∀ k ∈ Finset.Icc 1 K, (bandSumRows k (row :: rest) : ℝ) =
        (2 * dotList row (dropNat k row) : ℝ) + (bandSumRows k rest : ℝ) := by
      intro k hk
      have hk0 : Nat.beq k 0 = false := by
        have := (Finset.mem_Icc.mp hk).1
        cases k with
        | zero => omega
        | succ _ => rfl
      simp [bandSumRows, sumDots, hk0]
      ring
    rw [hband0]
    have hsum_split :
        ∑ k ∈ Finset.Icc 1 K, (bandSumRows k (row :: rest) : ℝ) * Real.cos (2 * Real.pi * (k : ℝ) * θ) =
          (∑ k ∈ Finset.Icc 1 K, (2 * dotList row (dropNat k row) : ℝ) * Real.cos (2 * Real.pi * (k : ℝ) * θ)) +
          (∑ k ∈ Finset.Icc 1 K, (bandSumRows k rest : ℝ) * Real.cos (2 * Real.pi * (k : ℝ) * θ)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [hbandk k hk, add_mul]
    rw [hsum_split]
    ring

theorem gram_f_nonneg
    (f₁ : ℝ → ℝ) (hf0 : 0 ≤ f₁) (hf : MeasureTheory.MemLp f₁ 2)
    (hsupp : ∀ x ∉ Set.Icc (-1 / 4 : ℝ) (1 / 4), f₁ x = 0)
    (hmass : ∫ x in Set.Icc (-1 / 4 : ℝ) (1 / 4), f₁ x = 1)
    (K : ℕ) (Vf : List (List ℤ)) (hVf_len : ∀ row ∈ Vf, row.length = K + 1) :
    0 ≤ (bandSumRows 0 Vf : ℝ) +
      ∑ k ∈ Finset.Icc 1 K,
        (bandSumRows k Vf : ℝ) * (∫ x, f₁ x * Real.cos (2 * Real.pi * (k : ℝ) * x)) := by
  have hfint := integrable_of_memLp_Icc hf hsupp
  have hf_one : ∫ x, f₁ x = 1 := by
    rw [← integral_Icc_eq_integral_of_supp (by norm_num) hsupp, hmass]
  have hcos_int : ∀ k : ℕ, Integrable (fun x => f₁ x * Real.cos (2 * Real.pi * (k : ℝ) * x)) :=
    fun k => integrable_mul_bounded_cont hfint
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))
      ⟨1, fun x => Real.abs_cos_le_one _⟩
  have hrew : (fun x => f₁ x * trigSqSum K Vf x) =
      fun x => (bandSumRows 0 Vf : ℝ) * f₁ x +
        ∑ k ∈ Finset.Icc 1 K, (bandSumRows k Vf : ℝ) * (f₁ x * Real.cos (2 * Real.pi * (k : ℝ) * x)) := by
    ext x
    rw [trigSqSum_eq_bandSum K Vf hVf_len x, mul_add, Finset.mul_sum]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun k _ => by ring
  have h_nonneg : 0 ≤ ∫ x, f₁ x * trigSqSum K Vf x :=
    integral_nonneg fun x => mul_nonneg (hf0 x) (trigSqSum_nonneg K Vf x)
  rw [hrew] at h_nonneg
  have hsum_int : Integrable (fun x => ∑ k ∈ Finset.Icc 1 K,
      (bandSumRows k Vf : ℝ) * (f₁ x * Real.cos (2 * Real.pi * (k : ℝ) * x))) :=
    integrable_finsetSum _ fun k _ => (hcos_int k).const_mul _
  rw [integral_add (hfint.const_mul _) hsum_int, integral_const_mul, hf_one, mul_one,
    integral_finsetSum _ (fun k _ => (hcos_int k).const_mul _)] at h_nonneg
  simpa [integral_const_mul] using h_nonneg

private lemma sum_Icc_shift_sub {K : ℕ} (hK : 1 ≤ K) (φ : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 1 K, φ (k - 1) = ∑ j ∈ Finset.Icc 0 (K - 1), φ j := by
  refine Finset.sum_bij (fun k _ => k - 1) ?_ ?_ ?_ ?_
  · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
  · intro k₁ hk₁ k₂ hk₂ h; simp only [Finset.mem_Icc] at hk₁ hk₂; omega
  · intro j hj; simp only [Finset.mem_Icc] at hj; refine ⟨j + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
  · intro _ _; rfl

private lemma sum_Icc_shift_add (K : ℕ) (φ : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 1 K, φ (k + 1) = ∑ j ∈ Finset.Icc 2 (K + 1), φ j := by
  refine Finset.sum_bij (fun k _ => k + 1) ?_ ?_ ?_ ?_
  · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
  · intro k₁ _ k₂ _ h; omega
  · intro j hj; simp only [Finset.mem_Icc] at hj; refine ⟨j - 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
  · intro _ _; rfl

private lemma Icc_zero_split {K : ℕ} (hK : 2 ≤ K) :
    Finset.Icc 0 (K - 1) = insert 0 (insert 1 (Finset.Icc 2 (K - 1))) := by
  ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega

private lemma Icc_two_split {K : ℕ} (hK : 2 ≤ K) :
    Finset.Icc 2 (K + 1) = insert (K + 1) (insert K (Finset.Icc 2 (K - 1))) := by
  ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega

theorem gram_nu_nonneg
    (f₁ : ℝ → ℝ) (hf0 : 0 ≤ f₁) (hf : MeasureTheory.MemLp f₁ 2)
    (hsupp : ∀ x ∉ Set.Icc (-1 / 4 : ℝ) (1 / 4), f₁ x = 0)
    (hmass : ∫ x in Set.Icc (-1 / 4 : ℝ) (1 / 4), f₁ x = 1)
    (K : ℕ) (hK : 2 ≤ K) (Vnu : List (List ℤ)) (hVnu_len : ∀ row ∈ Vnu, row.length = K + 1) :
    0 ≤ ((bandSumRows 1 Vnu : ℝ) / 2) +
      ((bandSumRows 0 Vnu : ℝ) + (bandSumRows 2 Vnu : ℝ) / 2) *
        (∫ x, f₁ x * Real.cos (2 * Real.pi * ((1 : ℕ) : ℝ) * x)) +
      (∑ k ∈ Finset.Icc 2 (K - 1),
        (((bandSumRows (k - 1) Vnu : ℝ) + (bandSumRows (k + 1) Vnu : ℝ)) / 2) *
          (∫ x, f₁ x * Real.cos (2 * Real.pi * (k : ℝ) * x))) +
      ((bandSumRows (K - 1) Vnu : ℝ) / 2) *
        (∫ x, f₁ x * Real.cos (2 * Real.pi * (K : ℝ) * x)) +
      ((bandSumRows K Vnu : ℝ) / 2) *
        (∫ x, f₁ x * Real.cos (2 * Real.pi * ((K + 1 : ℕ) : ℝ) * x)) := by
  let a : ℕ → ℝ := fun k => ∫ x, f₁ x * Real.cos (2 * Real.pi * (k : ℝ) * x)
  let snu : ℕ → ℝ := fun k => (bandSumRows k Vnu : ℝ)
  have hfint := integrable_of_memLp_Icc hf hsupp
  have ha0 : a 0 = 1 := by
    dsimp [a]
    simp only [Nat.cast_zero, mul_zero, zero_mul, Real.cos_zero, mul_one]
    rw [← integral_Icc_eq_integral_of_supp (by norm_num) hsupp, hmass]
  have hcos_int : ∀ k : ℕ, Integrable (fun x => f₁ x * Real.cos (2 * Real.pi * (k : ℝ) * x)) :=
    fun k => integrable_mul_bounded_cont hfint
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))
      ⟨1, fun x => Real.abs_cos_le_one _⟩
  have h_pt_nonneg : ∀ x, 0 ≤ f₁ x * Real.cos (2 * Real.pi * x) * trigSqSum K Vnu x := by
    intro x
    by_cases hx : x ∈ Set.Icc (-1 / 4 : ℝ) (1 / 4)
    · have hcos_nn : 0 ≤ Real.cos (2 * Real.pi * x) := by
        apply Real.cos_nonneg_of_mem_Icc
        simp only [Set.mem_Icc] at hx ⊢
        constructor <;> nlinarith [Real.pi_pos]
      exact mul_nonneg (mul_nonneg (hf0 x) hcos_nn) (trigSqSum_nonneg K Vnu x)
    · rw [hsupp x hx]
      simp
  have h_int_nonneg : 0 ≤ ∫ x, f₁ x * Real.cos (2 * Real.pi * x) * trigSqSum K Vnu x :=
    integral_nonneg h_pt_nonneg
  have hprod_cos : ∀ k ∈ Finset.Icc 1 K, ∀ x : ℝ,
      Real.cos (2 * Real.pi * (k : ℝ) * x) * Real.cos (2 * Real.pi * x) =
        (Real.cos (2 * Real.pi * ((k - 1 : ℕ) : ℝ) * x) +
          Real.cos (2 * Real.pi * ((k + 1 : ℕ) : ℝ) * x)) / 2 := by
    intro k hk x
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hsub : 2 * Real.pi * ((k - 1 : ℕ) : ℝ) * x =
        2 * Real.pi * (k : ℝ) * x - 2 * Real.pi * x := by
      rw [Nat.cast_sub hk1]; push_cast; ring
    have hadd : 2 * Real.pi * ((k + 1 : ℕ) : ℝ) * x =
        2 * Real.pi * (k : ℝ) * x + 2 * Real.pi * x := by
      push_cast; ring
    rw [hsub, hadd]
    linarith [Real.cos_add (2 * Real.pi * (k : ℝ) * x) (2 * Real.pi * x),
      Real.cos_sub (2 * Real.pi * (k : ℝ) * x) (2 * Real.pi * x)]
  have hrew : (fun x => f₁ x * Real.cos (2 * Real.pi * x) * trigSqSum K Vnu x) =
      fun x => snu 0 * (f₁ x * Real.cos (2 * Real.pi * ((1 : ℕ) : ℝ) * x)) +
        ∑ k ∈ Finset.Icc 1 K,
          ((snu k / 2) * (f₁ x * Real.cos (2 * Real.pi * ((k - 1 : ℕ) : ℝ) * x)) +
           (snu k / 2) * (f₁ x * Real.cos (2 * Real.pi * ((k + 1 : ℕ) : ℝ) * x))) := by
    ext x
    rw [trigSqSum_eq_bandSum K Vnu hVnu_len x]
    have h1 : Real.cos (2 * Real.pi * ((1 : ℕ) : ℝ) * x) = Real.cos (2 * Real.pi * x) := by
      simp
    rw [mul_add, Finset.mul_sum]
    congr 1
    · dsimp [snu]; rw [h1]; ring
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hmul : f₁ x * Real.cos (2 * Real.pi * x) *
          ((bandSumRows k Vnu : ℝ) * Real.cos (2 * Real.pi * (k : ℝ) * x)) =
          (snu k) * (f₁ x * (Real.cos (2 * Real.pi * (k : ℝ) * x) * Real.cos (2 * Real.pi * x))) := by
        dsimp [snu]; ring
      rw [hmul, hprod_cos k hk x]
      ring
  have hterm_iv : ∀ k ∈ Finset.Icc 1 K, Integrable (fun x =>
      (snu k / 2) * (f₁ x * Real.cos (2 * Real.pi * ((k - 1 : ℕ) : ℝ) * x)) +
      (snu k / 2) * (f₁ x * Real.cos (2 * Real.pi * ((k + 1 : ℕ) : ℝ) * x))) :=
    fun k _ => ((hcos_int (k - 1)).const_mul _).add ((hcos_int (k + 1)).const_mul _)
  rw [hrew, integral_add ((hcos_int 1).const_mul _) (integrable_finsetSum _ hterm_iv),
    integral_const_mul, integral_finsetSum _ hterm_iv] at h_int_nonneg
  have hsum_eval : ∑ k ∈ Finset.Icc 1 K, ∫ x,
      ((snu k / 2) * (f₁ x * Real.cos (2 * Real.pi * ((k - 1 : ℕ) : ℝ) * x)) +
       (snu k / 2) * (f₁ x * Real.cos (2 * Real.pi * ((k + 1 : ℕ) : ℝ) * x))) =
      (∑ k ∈ Finset.Icc 1 K, (snu k / 2) * a (k - 1)) +
      (∑ k ∈ Finset.Icc 1 K, (snu k / 2) * a (k + 1)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_add ((hcos_int (k - 1)).const_mul _) ((hcos_int (k + 1)).const_mul _),
      integral_const_mul, integral_const_mul]
  rw [hsum_eval] at h_int_nonneg
  have hshift1 : ∑ k ∈ Finset.Icc 1 K, (snu k / 2) * a (k - 1) =
      (snu 1 / 2) * a 0 + (snu 2 / 2) * a 1 +
        ∑ j ∈ Finset.Icc 2 (K - 1), (snu (j + 1) / 2) * a j := by
    have hs := sum_Icc_shift_sub (by omega : 1 ≤ K) (fun j => (snu (j + 1) / 2) * a j)
    have heq : ∑ k ∈ Finset.Icc 1 K, (snu k / 2) * a (k - 1) =
        ∑ k ∈ Finset.Icc 1 K, (snu (k - 1 + 1) / 2) * a (k - 1) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk1 := (Finset.mem_Icc.mp hk).1
      rw [Nat.sub_add_cancel hk1]
    rw [heq, hs, Icc_zero_split hK,
      Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
    ring
  have hshift2 : ∑ k ∈ Finset.Icc 1 K, (snu k / 2) * a (k + 1) =
      (∑ j ∈ Finset.Icc 2 (K - 1), (snu (j - 1) / 2) * a j) +
        (snu (K - 1) / 2) * a K + (snu K / 2) * a (K + 1) := by
    have hs := sum_Icc_shift_add K (fun j => (snu (j - 1) / 2) * a j)
    have heq : ∑ k ∈ Finset.Icc 1 K, (snu k / 2) * a (k + 1) =
        ∑ k ∈ Finset.Icc 1 K, (snu (k + 1 - 1) / 2) * a (k + 1) := by
      refine Finset.sum_congr rfl fun k _ => by simp
    rw [heq, hs, Icc_two_split hK,
      Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_Icc]; omega),
      Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
    have hKsub : K + 1 - 1 = K := by omega
    rw [hKsub]
    ring
  rw [hshift1, hshift2, ha0] at h_int_nonneg
  have hmid : (∑ j ∈ Finset.Icc 2 (K - 1), (snu (j + 1) / 2) * a j) +
      (∑ j ∈ Finset.Icc 2 (K - 1), (snu (j - 1) / 2) * a j) =
      ∑ k ∈ Finset.Icc 2 (K - 1), ((snu (k - 1) + snu (k + 1)) / 2) * a k := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => by ring
  dsimp [snu, a] at h_int_nonneg hmid ⊢
  linarith

theorem gram_g_le
    (f₁ : ℝ → ℝ) (hf : MeasureTheory.MemLp f₁ 2)
    (hsupp : ∀ x ∉ Set.Icc (-1 / 4 : ℝ) (1 / 4), f₁ x = 0)
    (hmass : ∫ x in Set.Icc (-1 / 4 : ℝ) (1 / 4), f₁ x = 1)
    (K : ℕ) {Ω : ℝ}
    (hΩ : ∀ t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2), (∫ x, f₁ (t - x) * f₁ x) ≤ Ω)
    (Vg : List (List ℤ)) (hVg_len : ∀ row ∈ Vg, row.length = K + 1) :
    ∑ k ∈ Finset.Icc 1 K, (bandSumRows k Vg : ℝ) *
      ((∫ x, f₁ x * Real.cos (2 * Real.pi * (k : ℝ) * x)) ^ 2 -
       (∫ x, f₁ x * Real.sin (2 * Real.pi * (k : ℝ) * x)) ^ 2) ≤
      (bandSumRows 0 Vg : ℝ) * (Ω - 1) := by
  let g : ℝ → ℝ := fun t => ∫ x, f₁ (t - x) * f₁ x
  let a : ℕ → ℝ := fun k => ∫ x, f₁ x * Real.cos (2 * Real.pi * (k : ℝ) * x)
  let b : ℕ → ℝ := fun k => ∫ x, f₁ x * Real.sin (2 * Real.pi * (k : ℝ) * x)
  have hg_int : Integrable g := integrable_autoconv hf hsupp
  have hg_iv : IntervalIntegrable g volume (-1 / 2) (1 / 2) := hg_int.intervalIntegrable
  have hg_one : ∫ t in (-1 / 2 : ℝ)..(1 / 2), g t = 1 :=
    autoconv_integral_Icc_eq_one f₁ hf hsupp hmass
  have hΩg_iv : IntervalIntegrable (fun t => Ω - g t) volume (-1 / 2) (1 / 2) :=
    intervalIntegrable_const.sub hg_iv
  have htrig_cont : Continuous (trigSqSum K Vg) := by
    rw [funext (trigSqSum_eq_bandSum K Vg hVg_len)]
    refine continuous_const.add (continuous_finsetSum _ fun k _ => ?_)
    exact continuous_const.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))
  have hprod_iv : IntervalIntegrable (fun t => (Ω - g t) * trigSqSum K Vg t) volume (-1 / 2) (1 / 2) := by
    have hΩg_int : IntegrableOn (fun t => Ω - g t) (Set.Icc (-1 / 2 : ℝ) (1 / 2)) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mp hΩg_iv
    have hcont_on : ContinuousOn (trigSqSum K Vg) (Set.Icc (-1 / 2 : ℝ) (1 / 2)) :=
      htrig_cont.continuousOn
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mpr
      (hΩg_int.mul_continuousOn hcont_on isCompact_Icc)
  have h_nonneg : 0 ≤ ∫ t in (-1 / 2 : ℝ)..(1 / 2), (Ω - g t) * trigSqSum K Vg t := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro t ht
    exact mul_nonneg (sub_nonneg.mpr (hΩ t ht)) (trigSqSum_nonneg K Vg t)
  have hrew : (fun t => (Ω - g t) * trigSqSum K Vg t) =
      fun t => (bandSumRows 0 Vg : ℝ) * (Ω - g t) +
        ∑ k ∈ Finset.Icc 1 K, (bandSumRows k Vg : ℝ) *
          ((Ω - g t) * Real.cos (2 * Real.pi * (k : ℝ) * t)) := by
    ext t
    rw [trigSqSum_eq_bandSum K Vg hVg_len t, mul_add, Finset.mul_sum]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun k _ => by ring
  have hcos_iv : ∀ k : ℕ, IntervalIntegrable
      (fun t => (Ω - g t) * Real.cos (2 * Real.pi * (k : ℝ) * t)) volume (-1 / 2) (1 / 2) := by
    intro k
    have hcos_c : Continuous (fun t => Real.cos (2 * Real.pi * (k : ℝ) * t)) :=
      Real.continuous_cos.comp (continuous_const.mul continuous_id)
    have hΩg_on : IntegrableOn (fun t => Ω - g t) (Set.Icc (-1 / 2 : ℝ) (1 / 2)) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mp hΩg_iv
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mpr
      (hΩg_on.mul_continuousOn hcos_c.continuousOn isCompact_Icc)
  have hsum_iv : IntervalIntegrable (fun t => ∑ k ∈ Finset.Icc 1 K,
      (bandSumRows k Vg : ℝ) * ((Ω - g t) * Real.cos (2 * Real.pi * (k : ℝ) * t)))
      volume (-1 / 2) (1 / 2) := by
    have hfun : (fun t => ∑ k ∈ Finset.Icc 1 K,
        (bandSumRows k Vg : ℝ) * ((Ω - g t) * Real.cos (2 * Real.pi * (k : ℝ) * t))) =
        ∑ k ∈ Finset.Icc 1 K, fun t =>
          (bandSumRows k Vg : ℝ) * ((Ω - g t) * Real.cos (2 * Real.pi * (k : ℝ) * t)) := by
      ext t; simp only [Finset.sum_apply]
    rw [hfun]
    exact IntervalIntegrable.sum (Finset.Icc 1 K) (fun k _ => (hcos_iv k).const_mul _)
  rw [hrew, intervalIntegral.integral_add (hΩg_iv.const_mul _) hsum_iv,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub intervalIntegrable_const hg_iv,
    intervalIntegral.integral_const, hg_one,
    intervalIntegral.integral_finsetSum (fun k _ => (hcos_iv k).const_mul _)] at h_nonneg
  have hconst_int : (1 / 2 - -1 / 2 : ℝ) • Ω = Ω := by simp [smul_eq_mul]; norm_num
  rw [hconst_int] at h_nonneg
  have hsum_eval : ∑ k ∈ Finset.Icc 1 K, ∫ t in (-1 / 2 : ℝ)..(1 / 2),
      (bandSumRows k Vg : ℝ) * ((Ω - g t) * Real.cos (2 * Real.pi * (k : ℝ) * t)) =
      - ∑ k ∈ Finset.Icc 1 K, (bandSumRows k Vg : ℝ) * (a k ^ 2 - b k ^ 2) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk1 : (k : ℤ) ≠ 0 := by
      have := (Finset.mem_Icc.mp hk).1; omega
    have hcos_c_iv : IntervalIntegrable (fun t => Real.cos (2 * Real.pi * (k : ℝ) * t))
        volume (-1 / 2) (1 / 2) :=
      (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
    have hgcos_iv : IntervalIntegrable (fun t => g t * Real.cos (2 * Real.pi * (k : ℝ) * t))
        volume (-1 / 2) (1 / 2) :=
      (integrable_mul_bounded_cont hg_int
        (Real.continuous_cos.comp (continuous_const.mul continuous_id))
        ⟨1, fun t => Real.abs_cos_le_one _⟩).intervalIntegrable
    have hsub_fn : (fun t => (Ω - g t) * Real.cos (2 * Real.pi * (k : ℝ) * t)) =
        fun t => Ω * Real.cos (2 * Real.pi * (k : ℝ) * t) -
          g t * Real.cos (2 * Real.pi * (k : ℝ) * t) := by
      ext t; ring
    rw [intervalIntegral.integral_const_mul, hsub_fn,
      intervalIntegral.integral_sub (hcos_c_iv.const_mul _) hgcos_iv,
      intervalIntegral.integral_const_mul]
    have hcos0 := intervalIntegral_cos_two_pi_int hk1
    simp only [Int.cast_natCast] at hcos0
    rw [hcos0, autoconv_fourier_cos f₁ hf hsupp k]
    ring
  rw [hsum_eval] at h_nonneg
  dsimp [a, b] at h_nonneg ⊢
  linarith

/- ### Section 4: Master Certificate Theorem -/

private lemma sum_Icc_one_K_split {K : ℕ} (hK : 2 ≤ K) (φ : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 1 K, φ k = φ 1 + (∑ k ∈ Finset.Icc 2 (K - 1), φ k) + φ K := by
  have hset : Finset.Icc 1 K = insert 1 (insert K (Finset.Icc 2 (K - 1))) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [hset,
    Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_Icc]; omega),
    Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
  ring

private lemma sum_Icc_one_K_succ {K : ℕ} (hK : 2 ≤ K) (φ : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 1 (K + 1), φ k = (∑ k ∈ Finset.Icc 1 K, φ k) + φ (K + 1) := by
  have hset : Finset.Icc 1 (K + 1) = insert (K + 1) (Finset.Icc 1 K) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [hset, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
  ring

theorem c1a_ge_of_sos_certificate
    (K N : ℕ) (hK : 2 ≤ K) (hN : 1 ≤ N)
    (D C_num C_den numConst : ℤ) (hD : 0 < D) (hCden : 0 < C_den) (hCnum : 0 ≤ C_num)
    (Vf Vnu Vg : List (List ℤ))
    (sfFn snuFn sgFn rFn mFn alphaFn : ℕ → ℤ)
    (hVf_len : ∀ row ∈ Vf, row.length = K + 1)
    (hVnu_len : ∀ row ∈ Vnu, row.length = K + 1)
    (hVg_len : ∀ row ∈ Vg, row.length = K + 1)
    (hsf : ∀ k ≤ K, bandSumRows k Vf = sfFn k)
    (hsnu : ∀ k ≤ K, bandSumRows k Vnu = snuFn k)
    (hsg : ∀ k ≤ K, bandSumRows k Vg = sgFn k)
    (hmu : 0 ≤ D ^ 2 - sgFn 0)
    (hA_nonneg : ∀ k, 1 ≤ k → k ≤ K → 0 ≤ 4 * (D ^ 2 - sgFn 0) * rFn k + D * sgFn k)
    (halpha_le : ∀ k, 1 ≤ k → k ≤ K →
      alphaFn k = 4 * (4 * (D ^ 2 - sgFn 0) * rFn k + D * sgFn k) * mFn k -
        2 * D ^ 2 * sfFn k -
        (if k = 1 then 2 * D ^ 2 * snuFn 0 + D ^ 2 * snuFn 2
         else if k ≤ K - 1 then D ^ 2 * (snuFn (k - 1) + snuFn (k + 1))
         else D ^ 2 * snuFn (K - 1)))
    (halpha_top : alphaFn (K + 1) = -(D ^ 2 * snuFn K))
    (hconst : numConst = 2 * D ^ 5 -
      4 * D * (D ^ 2 - sgFn 0) * (∑ k ∈ Finset.Icc 1 K, (rFn k) ^ 2) -
      2 * (∑ k ∈ Finset.Icc 1 K, (4 * (D ^ 2 - sgFn 0) * rFn k + D * sgFn k) * (mFn k) ^ 2) +
      2 * D ^ 2 * (∑ k ∈ Finset.Icc 1 K, min (4 * (D ^ 2 - sgFn 0) * rFn k - D * sgFn k) 0) -
      2 * D ^ 3 * sfFn 0 - D ^ 3 * snuFn 1)
    (hcell : ∀ j < N, ∀ x ∈ Set.Icc ((j : ℝ) / (4 * N)) (((j : ℝ) + 1) / (4 * N)),
      (C_num : ℝ) / (C_den : ℝ) ≤
        (numConst : ℝ) / (2 * (D : ℝ) ^ 5) +
          (∑ k ∈ Finset.Icc 1 (K + 1), (alphaFn k : ℝ) * Real.cos (2 * Real.pi * (k : ℝ) * x)) /
            (2 * (D : ℝ) ^ 4)) :
    (C_num : ℝ) / (C_den : ℝ) ≤ C1a := by
  have _ := And.intro hCden hCnum
  apply le_csSup c1a_set_bddAbove
  intro f hf0 hf
  let I : Set ℝ := Set.Icc (-1 / 4 : ℝ) (1 / 4)
  let M : ℝ := ∫ x in (-1 / 4 : ℝ)..(1 / 4), f x
  let S_sup : ℝ := sSup {∫ x, f (t - x) * f x | t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2)}
  have hS_nn : 0 ≤ S_sup := autoconvValues_nonneg_sSup hf0 hf
  have hM_eq_Icc : M = ∫ x in I, f x := by
    dsimp [M, I]
    rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc]
  have hM_nn : 0 ≤ M := by
    rw [hM_eq_Icc]
    exact setIntegral_nonneg measurableSet_Icc fun x _ => hf0 x
  rcases hM_nn.eq_or_lt with hM0 | hMpos
  · change ((C_num : ℝ) / (C_den : ℝ)) * M ^ 2 ≤ S_sup
    rw [← hM0]
    simpa using hS_nn
  -- Normalized compactly-supported test function `f₁`
  let f₁ : ℝ → ℝ := fun x => (1 / M) * I.indicator f x
  have hf₁0 : 0 ≤ f₁ := fun x =>
    mul_nonneg (div_nonneg zero_le_one hMpos.le) (indicator_nonneg (fun y _ => hf0 y) x)
  have hf₁m : MeasureTheory.MemLp f₁ 2 := (hf.indicator measurableSet_Icc).const_mul (1 / M)
  have hf₁supp : ∀ x ∉ I, f₁ x = 0 := fun x hx => by
    dsimp [f₁]; rw [indicator_of_notMem hx, mul_zero]
  have hf₁mass : ∫ x in I, f₁ x = 1 := by
    dsimp [f₁]
    rw [integral_const_mul, setIntegral_indicator measurableSet_Icc, Set.inter_self, ← hM_eq_Icc]
    field_simp [hMpos.ne']
  have hf₁mass_all : ∫ x, f₁ x = 1 := by
    rw [← integral_Icc_eq_integral_of_supp (by norm_num) hf₁supp, hf₁mass]
  let Ω : ℝ := (1 / M ^ 2) * S_sup
  have hΩ : ∀ t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2), (∫ x, f₁ (t - x) * f₁ x) ≤ Ω := by
    intro t ht
    have htm1 : MeasureTheory.MemLp (fun x => f₁ (t - x)) 2 :=
      hf₁m.comp_measurePreserving (volume.measurePreserving_sub_left t)
    have htm : MeasureTheory.MemLp (fun x => f (t - x)) 2 :=
      hf.comp_measurePreserving (volume.measurePreserving_sub_left t)
    have hpt : ∀ x, f₁ (t - x) * f₁ x ≤ (1 / M ^ 2) * (f (t - x) * f x) := by
      intro x
      have h1 : I.indicator f (t - x) ≤ f (t - x) :=
        if hx : t - x ∈ I then by simp [hx] else by simp [hx]; exact hf0 (t - x)
      have h2 : I.indicator f x ≤ f x :=
        if hx : x ∈ I then by simp [hx] else by simp [hx]; exact hf0 x
      have hprod : I.indicator f (t - x) * I.indicator f x ≤ f (t - x) * f x :=
        mul_le_mul h1 h2 (indicator_nonneg (fun y _ => hf0 y) _) (hf0 (t - x))
      have hM2_nn : 0 ≤ (1 / M ^ 2 : ℝ) := by positivity
      calc
        f₁ (t - x) * f₁ x = (1 / M ^ 2) * (I.indicator f (t - x) * I.indicator f x) := by
          dsimp [f₁]; ring
        _ ≤ (1 / M ^ 2) * (f (t - x) * f x) := mul_le_mul_of_nonneg_left hprod hM2_nn
    calc
      ∫ x, f₁ (t - x) * f₁ x ≤ ∫ x, (1 / M ^ 2) * (f (t - x) * f x) :=
        integral_mono (htm1.integrable_mul hf₁m) ((htm.integrable_mul hf).const_mul _) hpt
      _ = (1 / M ^ 2) * ∫ x, f (t - x) * f x := integral_const_mul _ _
      _ ≤ (1 / M ^ 2) * S_sup :=
        mul_le_mul_of_nonneg_left (le_csSup (autoconvValues_bddAbove hf) ⟨t, ht, rfl⟩) (by positivity)
  -- Fourier coefficients and scaled certificate parameters
  let a : ℕ → ℝ := fun k => ∫ x, f₁ x * Real.cos (2 * Real.pi * (k : ℝ) * x)
  let b : ℕ → ℝ := fun k => ∫ x, f₁ x * Real.sin (2 * Real.pi * (k : ℝ) * x)
  have hd_pos : (0 : ℝ) < (D : ℝ) := Int.cast_pos.mpr hD
  let d : ℝ := (D : ℝ)
  let μ : ℝ := ((D ^ 2 - sgFn 0 : ℤ) : ℝ) / d ^ 2
  have hμ_nn : 0 ≤ μ := div_nonneg (by exact_mod_cast hmu) (by positivity)
  let sfR : ℕ → ℝ := fun k => (sfFn k : ℝ) / d ^ 2
  let snuR : ℕ → ℝ := fun k => (snuFn k : ℝ) / d ^ 2
  let sgR : ℕ → ℝ := fun k => (sgFn k : ℝ) / d ^ 2
  let rR : ℕ → ℝ := fun k => (rFn k : ℝ) / d
  let mR : ℕ → ℝ := fun k => (mFn k : ℝ) / d
  let AR : ℕ → ℝ := fun k => ((4 * (D ^ 2 - sgFn 0) * rFn k + D * sgFn k : ℤ) : ℝ) / d ^ 3
  let BR : ℕ → ℝ := fun k => ((4 * (D ^ 2 - sgFn 0) * rFn k - D * sgFn k : ℤ) : ℝ) / d ^ 3
  have hμ_sg0 : μ + sgR 0 = 1 := by
    dsimp [μ, sgR, d]
    push_cast
    field_simp [hd_pos.ne']
    ring
  have hAR_eq : ∀ k, AR k = 4 * μ * rR k + sgR k := by
    intro k; dsimp [AR, μ, rR, sgR, d]; push_cast; field_simp [hd_pos.ne']
  have hBR_eq : ∀ k, BR k = 4 * μ * rR k - sgR k := by
    intro k; dsimp [BR, μ, rR, sgR, d]; push_cast; field_simp [hd_pos.ne']
  have hAR_nn : ∀ k ∈ Finset.Icc 1 K, 0 ≤ AR k := by
    intro k hk
    have hk' := Finset.mem_Icc.mp hk
    exact div_nonneg (by exact_mod_cast hA_nonneg k hk'.1 hk'.2) (by positivity)
  -- 1. Finite Bessel inequality multiplied by μ ≥ 0
  have hbessel := finite_bessel_autoconv f₁ hf₁0 hf₁m hf₁supp hf₁mass K hΩ
  have hbessel_μ : 2 * μ * ∑ k ∈ Finset.Icc 1 K, (a k ^ 2 + b k ^ 2) ^ 2 ≤ μ * (Ω - 1) := by
    have hmul := mul_le_mul_of_nonneg_left hbessel hμ_nn
    linarith
  have hquad_bessel :
      ∑ k ∈ Finset.Icc 1 K, (4 * μ * rR k * (a k ^ 2 + b k ^ 2) - 2 * μ * rR k ^ 2) ≤
        2 * μ * ∑ k ∈ Finset.Icc 1 K, (a k ^ 2 + b k ^ 2) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    have hsq : 0 ≤ 2 * μ * ((a k ^ 2 + b k ^ 2) - rR k) ^ 2 :=
      mul_nonneg (mul_nonneg (by norm_num) hμ_nn) (sq_nonneg _)
    linarith
  -- 2. Direct-T_g Gram inequality divided by d^2
  have hgram_g_raw := gram_g_le f₁ hf₁m hf₁supp hf₁mass K hΩ Vg hVg_len
  have hgram_g : ∑ k ∈ Finset.Icc 1 K, sgR k * (a k ^ 2 - b k ^ 2) ≤ sgR 0 * (Ω - 1) := by
    have hdiv := div_le_div_of_nonneg_right hgram_g_raw (by positivity : (0 : ℝ) ≤ d ^ 2)
    rw [Finset.sum_div] at hdiv
    have hlhs : ∑ k ∈ Finset.Icc 1 K, (bandSumRows k Vg : ℝ) * (a k ^ 2 - b k ^ 2) / d ^ 2 =
        ∑ k ∈ Finset.Icc 1 K, sgR k * (a k ^ 2 - b k ^ 2) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hkK := (Finset.mem_Icc.mp hk).2
      rw [hsg k hkK]
      dsimp [sgR]; ring
    have hrhs : (bandSumRows 0 Vg : ℝ) * (Ω - 1) / d ^ 2 = sgR 0 * (Ω - 1) := by
      rw [hsg 0 (Nat.zero_le K)]
      dsimp [sgR]; ring
    rw [hlhs, hrhs] at hdiv
    exact hdiv
  -- Combine Bessel and Vg to bound Ω - 1 from below
  have h_omega_1 :
      ∑ k ∈ Finset.Icc 1 K, (AR k * a k ^ 2 + BR k * b k ^ 2 - 2 * μ * rR k ^ 2) ≤ Ω - 1 := by
    have hsum_eq :
        ∑ k ∈ Finset.Icc 1 K, (AR k * a k ^ 2 + BR k * b k ^ 2 - 2 * μ * rR k ^ 2) =
          (∑ k ∈ Finset.Icc 1 K, (4 * μ * rR k * (a k ^ 2 + b k ^ 2) - 2 * μ * rR k ^ 2)) +
            ∑ k ∈ Finset.Icc 1 K, sgR k * (a k ^ 2 - b k ^ 2) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hAR_eq k, hBR_eq k]; ring
    rw [hsum_eq]
    have hcomb := add_le_add (hquad_bessel.trans hbessel_μ) hgram_g
    rw [← add_mul, hμ_sg0, one_mul] at hcomb
    exact hcomb
  -- Bound |b k| ≤ 1 so b k ^ 2 ≤ 1 and BR k * b k ^ 2 ≥ min (BR k) 0
  have hb_sq_le_one : ∀ k : ℕ, b k ^ 2 ≤ 1 := by
    intro k
    have hfint := integrable_of_memLp_Icc hf₁m hf₁supp
    have hsin_int : Integrable (fun x => f₁ x * Real.sin (2 * Real.pi * (k : ℝ) * x)) :=
      integrable_mul_bounded_cont hfint
        (Real.continuous_sin.comp (continuous_const.mul continuous_id))
        ⟨1, fun x => Real.abs_sin_le_one _⟩
    have hb_le : b k ≤ 1 := by
      calc
        b k ≤ ∫ x, f₁ x := by
          apply integral_mono hsin_int hfint
          intro x
          exact mul_le_of_le_one_right (hf₁0 x) (Real.sin_le_one _)
        _ = 1 := hf₁mass_all
    have hb_ge : -1 ≤ b k := by
      have hneg_le : -∫ x, f₁ x ≤ b k := by
        rw [← integral_neg]
        apply integral_mono hfint.neg hsin_int
        intro x
        have hx0 : 0 ≤ f₁ x := hf₁0 x
        change -f₁ x ≤ f₁ x * Real.sin (2 * Real.pi * (k : ℝ) * x)
        nlinarith [hx0, Real.neg_one_le_sin (2 * Real.pi * (k : ℝ) * x)]
      linarith [hf₁mass_all]
    nlinarith
  have h_omega_2 :
      ∑ k ∈ Finset.Icc 1 K, (2 * AR k * mR k * a k - AR k * mR k ^ 2 + min (BR k) 0 - 2 * μ * rR k ^ 2) ≤
        Ω - 1 := by
    refine le_trans (Finset.sum_le_sum fun k hk => ?_) h_omega_1
    have hA_sq : 2 * AR k * mR k * a k - AR k * mR k ^ 2 ≤ AR k * a k ^ 2 := by
      have hsq : 0 ≤ AR k * (a k - mR k) ^ 2 := mul_nonneg (hAR_nn k hk) (sq_nonneg _)
      linarith
    have hB_bd : min (BR k) 0 ≤ BR k * b k ^ 2 := by
      rcases le_or_gt 0 (BR k) with hB | hB
      · rw [min_eq_right hB]
        exact mul_nonneg hB (sq_nonneg _)
      · rw [min_eq_left hB.le]
        have := hb_sq_le_one k
        nlinarith
    linarith
  -- 3. Plain f₁ Gram sum divided by d^2
  have hgram_f_raw := gram_f_nonneg f₁ hf₁0 hf₁m hf₁supp hf₁mass K Vf hVf_len
  have hgram_f : 0 ≤ sfR 0 + ∑ k ∈ Finset.Icc 1 K, sfR k * a k := by
    have hdiv := div_nonneg hgram_f_raw (by positivity : (0 : ℝ) ≤ d ^ 2)
    rw [add_div, Finset.sum_div] at hdiv
    have h0 : (bandSumRows 0 Vf : ℝ) / d ^ 2 = sfR 0 := by
      rw [hsf 0 (Nat.zero_le K)]
    have hs : ∑ k ∈ Finset.Icc 1 K, (bandSumRows k Vf : ℝ) * a k / d ^ 2 =
        ∑ k ∈ Finset.Icc 1 K, sfR k * a k := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [hsf k (Finset.mem_Icc.mp hk).2]
      dsimp [sfR]; ring
    dsimp [a] at hdiv hs ⊢
    rw [h0, hs] at hdiv
    exact hdiv
  -- 4. Localized f₁ cos(2πx) Gram sum divided by d^2
  have hgram_nu_raw := gram_nu_nonneg f₁ hf₁0 hf₁m hf₁supp hf₁mass K hK Vnu hVnu_len
  have hgram_nu :
      0 ≤ snuR 1 / 2 + (snuR 0 + snuR 2 / 2) * a 1 +
        (∑ k ∈ Finset.Icc 2 (K - 1), ((snuR (k - 1) + snuR (k + 1)) / 2) * a k) +
        (snuR (K - 1) / 2) * a K + (snuR K / 2) * a (K + 1) := by
    have hdiv := div_nonneg hgram_nu_raw (by positivity : (0 : ℝ) ≤ d ^ 2)
    have h_rewrite :
        (((bandSumRows 1 Vnu : ℝ) / 2) +
          ((bandSumRows 0 Vnu : ℝ) + (bandSumRows 2 Vnu : ℝ) / 2) * a 1 +
          (∑ k ∈ Finset.Icc 2 (K - 1),
            (((bandSumRows (k - 1) Vnu : ℝ) + (bandSumRows (k + 1) Vnu : ℝ)) / 2) * a k) +
          ((bandSumRows (K - 1) Vnu : ℝ) / 2) * a K +
          ((bandSumRows K Vnu : ℝ) / 2) * a (K + 1)) / d ^ 2 =
        snuR 1 / 2 + (snuR 0 + snuR 2 / 2) * a 1 +
          (∑ k ∈ Finset.Icc 2 (K - 1), ((snuR (k - 1) + snuR (k + 1)) / 2) * a k) +
          (snuR (K - 1) / 2) * a K + (snuR K / 2) * a (K + 1) := by
      rw [hsnu 0 (by omega), hsnu 1 (by omega), hsnu 2 (by omega),
        hsnu (K - 1) (by omega), hsnu K (by omega)]
      have hmid :
          (∑ k ∈ Finset.Icc 2 (K - 1),
            (((bandSumRows (k - 1) Vnu : ℝ) + (bandSumRows (k + 1) Vnu : ℝ)) / 2) * a k) / d ^ 2 =
          ∑ k ∈ Finset.Icc 2 (K - 1), ((snuR (k - 1) + snuR (k + 1)) / 2) * a k := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk' := Finset.mem_Icc.mp hk
        rw [hsnu (k - 1) (by omega), hsnu (k + 1) (by omega)]
        dsimp [snuR]; ring
      dsimp [snuR]
      rw [add_div, add_div, add_div, add_div, hmid]
      ring
    dsimp [a] at h_rewrite ⊢
    rw [← h_rewrite]
    exact hdiv
  -- Combine all bounds into (numConst : ℝ) / (2 * d^5) + (∑ alpha_k * a_k) / (2 * d^4) ≤ Ω
  have hconst_real :
      (numConst : ℝ) / (2 * d ^ 5) =
        1 - 2 * μ * (∑ k ∈ Finset.Icc 1 K, rR k ^ 2) -
          (∑ k ∈ Finset.Icc 1 K, AR k * mR k ^ 2) +
          (∑ k ∈ Finset.Icc 1 K, min (BR k) 0) - sfR 0 - snuR 1 / 2 := by
    have h1 : (∑ k ∈ Finset.Icc 1 K, ((rFn k : ℝ) ^ 2)) / (D : ℝ) ^ 2 = ∑ k ∈ Finset.Icc 1 K, rR k ^ 2 := by
      rw [Finset.sum_div]; refine Finset.sum_congr rfl fun k _ => by dsimp [rR, d]; ring
    have h2 : (∑ k ∈ Finset.Icc 1 K,
        ((4 : ℝ) * ((D : ℝ) ^ 2 - (sgFn 0 : ℝ)) * (rFn k : ℝ) + (D : ℝ) * (sgFn k : ℝ)) * (mFn k : ℝ) ^ 2) / (D : ℝ) ^ 5 =
        ∑ k ∈ Finset.Icc 1 K, AR k * mR k ^ 2 := by
      rw [Finset.sum_div]; refine Finset.sum_congr rfl fun k _ => by
        dsimp [AR, mR, d]; push_cast; ring
    have h3 : (∑ k ∈ Finset.Icc 1 K,
        min ((4 : ℝ) * ((D : ℝ) ^ 2 - (sgFn 0 : ℝ)) * (rFn k : ℝ) - (D : ℝ) * (sgFn k : ℝ)) 0) / (D : ℝ) ^ 3 =
        ∑ k ∈ Finset.Icc 1 K, min (BR k) 0 := by
      rw [Finset.sum_div]; refine Finset.sum_congr rfl fun k _ => ?_
      dsimp [BR, d]; push_cast
      rw [← min_div_div_right (by positivity : (0 : ℝ) ≤ (D : ℝ) ^ 3), zero_div]
    have hmain :
        (numConst : ℝ) / (2 * (D : ℝ) ^ 5) =
          1 - 2 * (((D : ℝ) ^ 2 - (sgFn 0 : ℝ)) / (D : ℝ) ^ 2) *
                ((∑ k ∈ Finset.Icc 1 K, (rFn k : ℝ) ^ 2) / (D : ℝ) ^ 2) -
              (∑ k ∈ Finset.Icc 1 K,
                (4 * ((D : ℝ) ^ 2 - (sgFn 0 : ℝ)) * (rFn k : ℝ) + (D : ℝ) * (sgFn k : ℝ)) * (mFn k : ℝ) ^ 2) /
                (D : ℝ) ^ 5 +
              (∑ k ∈ Finset.Icc 1 K,
                min (4 * ((D : ℝ) ^ 2 - (sgFn 0 : ℝ)) * (rFn k : ℝ) - (D : ℝ) * (sgFn k : ℝ)) 0) /
                (D : ℝ) ^ 3 -
              (sfFn 0 : ℝ) / (D : ℝ) ^ 2 - (snuFn 1 : ℝ) / (D : ℝ) ^ 2 / 2 := by
      rw [hconst]
      push_cast
      field_simp [hd_pos.ne']
      ring
    dsimp [μ, sfR, snuR, d]
    rw [hmain, h1, h2, h3]
    dsimp [AR, BR, mR, rR, d]; push_cast; ring
  have halpha_real :
      (∑ k ∈ Finset.Icc 1 (K + 1), (alphaFn k : ℝ) * a k) / (2 * d ^ 4) =
        (∑ k ∈ Finset.Icc 1 K, (2 * AR k * mR k - sfR k) * a k) -
          ((snuR 0 + snuR 2 / 2) * a 1 +
            (∑ k ∈ Finset.Icc 2 (K - 1), ((snuR (k - 1) + snuR (k + 1)) / 2) * a k) +
            (snuR (K - 1) / 2) * a K + (snuR K / 2) * a (K + 1)) := by
    rw [sum_Icc_one_K_succ hK, sum_Icc_one_K_split hK (fun k => (alphaFn k : ℝ) * a k),
      sum_Icc_one_K_split hK (fun k => (2 * AR k * mR k - sfR k) * a k)]
    have h_a1 : (alphaFn 1 : ℝ) / (2 * d ^ 4) = 2 * AR 1 * mR 1 - sfR 1 - (snuR 0 + snuR 2 / 2) := by
      rw [halpha_le 1 (by omega) (by omega)]
      simp only [↓reduceIte]
      dsimp [AR, mR, sfR, snuR, d]; push_cast; field_simp [hd_pos.ne']; ring
    have h_amid : ∀ k ∈ Finset.Icc 2 (K - 1),
        (alphaFn k : ℝ) / (2 * d ^ 4) = 2 * AR k * mR k - sfR k - (snuR (k - 1) + snuR (k + 1)) / 2 := by
      intro k hk
      have hk' := Finset.mem_Icc.mp hk
      rw [halpha_le k (by omega) (by omega)]
      have hne1 : k ≠ 1 := by omega
      have hleK : k ≤ K - 1 := hk'.2
      simp only [hne1, ↓reduceIte, hleK]
      dsimp [AR, mR, sfR, snuR, d]; push_cast; field_simp [hd_pos.ne']; ring
    have h_aK : (alphaFn K : ℝ) / (2 * d ^ 4) = 2 * AR K * mR K - sfR K - snuR (K - 1) / 2 := by
      rw [halpha_le K (by omega) le_rfl]
      have hne1 : K ≠ 1 := by omega
      have hnle : ¬ K ≤ K - 1 := by omega
      simp only [hne1, ↓reduceIte, hnle]
      dsimp [AR, mR, sfR, snuR, d]; push_cast; field_simp [hd_pos.ne']; ring
    have h_atop : (alphaFn (K + 1) : ℝ) / (2 * d ^ 4) = -(snuR K / 2) := by
      rw [halpha_top]
      dsimp [snuR, d]; push_cast; field_simp [hd_pos.ne']
    rw [add_div, add_div, add_div, Finset.sum_div]
    have h1' : (alphaFn 1 : ℝ) * a 1 / (2 * d ^ 4) =
        (2 * AR 1 * mR 1 - sfR 1 - (snuR 0 + snuR 2 / 2)) * a 1 := by
      rw [← h_a1]; ring
    have hmid' : ∑ k ∈ Finset.Icc 2 (K - 1), (alphaFn k : ℝ) * a k / (2 * d ^ 4) =
        ∑ k ∈ Finset.Icc 2 (K - 1),
          (2 * AR k * mR k - sfR k - (snuR (k - 1) + snuR (k + 1)) / 2) * a k := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [← h_amid k hk]; ring
    have hK' : (alphaFn K : ℝ) * a K / (2 * d ^ 4) =
        (2 * AR K * mR K - sfR K - snuR (K - 1) / 2) * a K := by
      rw [← h_aK]; ring
    have htop' : (alphaFn (K + 1) : ℝ) * a (K + 1) / (2 * d ^ 4) = -(snuR K / 2) * a (K + 1) := by
      rw [← h_atop]; ring
    rw [h1', hmid', hK', htop']
    have hmid_split :
        ∑ k ∈ Finset.Icc 2 (K - 1), (2 * AR k * mR k - sfR k - (snuR (k - 1) + snuR (k + 1)) / 2) * a k =
          (∑ k ∈ Finset.Icc 2 (K - 1), (2 * AR k * mR k - sfR k) * a k) -
          ∑ k ∈ Finset.Icc 2 (K - 1), ((snuR (k - 1) + snuR (k + 1)) / 2) * a k := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => by ring
    rw [hmid_split]
    ring
  have hcert_le_omega :
      (numConst : ℝ) / (2 * d ^ 5) +
        (∑ k ∈ Finset.Icc 1 (K + 1), (alphaFn k : ℝ) * a k) / (2 * d ^ 4) ≤ Ω := by
    have h_omega_3 :
        (1 - 2 * μ * (∑ k ∈ Finset.Icc 1 K, rR k ^ 2) -
          (∑ k ∈ Finset.Icc 1 K, AR k * mR k ^ 2) +
          (∑ k ∈ Finset.Icc 1 K, min (BR k) 0)) +
          ∑ k ∈ Finset.Icc 1 K, 2 * AR k * mR k * a k ≤ Ω := by
      have h_split_sum :
          ∑ k ∈ Finset.Icc 1 K, (2 * AR k * mR k * a k - AR k * mR k ^ 2 + min (BR k) 0 - 2 * μ * rR k ^ 2) =
            (∑ k ∈ Finset.Icc 1 K, 2 * AR k * mR k * a k) -
              (∑ k ∈ Finset.Icc 1 K, AR k * mR k ^ 2) +
              (∑ k ∈ Finset.Icc 1 K, min (BR k) 0) -
              2 * μ * (∑ k ∈ Finset.Icc 1 K, rR k ^ 2) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      rw [h_split_sum] at h_omega_2
      linarith
    have h_f_sub : ∑ k ∈ Finset.Icc 1 K, (2 * AR k * mR k - sfR k) * a k =
        (∑ k ∈ Finset.Icc 1 K, 2 * AR k * mR k * a k) - ∑ k ∈ Finset.Icc 1 K, sfR k * a k := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => by ring
    rw [hconst_real, halpha_real, h_f_sub]
    linarith
  -- Fold [-1/4, 1/4] onto [0, 1/4] and apply hcell pointwise!
  let Φ : ℝ → ℝ := fun x =>
    ∑ k ∈ Finset.Icc 1 (K + 1), (alphaFn k : ℝ) * Real.cos (2 * Real.pi * (k : ℝ) * x)
  have hΦ_abs : ∀ x : ℝ, Φ |x| = Φ x := by
    intro x
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx]
      dsimp [Φ]
      refine Finset.sum_congr rfl fun k _ => ?_
      have harg : 2 * Real.pi * (k : ℝ) * (-x) = -(2 * Real.pi * (k : ℝ) * x) := by ring
      rw [harg, Real.cos_neg]
  have hpt_I : ∀ x ∈ I,
      (C_num : ℝ) / (C_den : ℝ) ≤ (numConst : ℝ) / (2 * d ^ 5) + Φ x / (2 * d ^ 4) := by
    intro x hx
    let y : ℝ := |x|
    have hy_nonneg : 0 ≤ y := abs_nonneg x
    have hy_le : y ≤ 1 / 4 := abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
    let j : ℕ := min (N - 1) ⌊4 * (N : ℝ) * y⌋₊
    have hj : j < N := lt_of_le_of_lt (Nat.min_le_left _ _) (by omega)
    have h4N_pos : (0 : ℝ) < 4 * (N : ℝ) := by positivity
    have hy_mem : y ∈ Set.Icc ((j : ℝ) / (4 * (N : ℝ))) (((j : ℝ) + 1) / (4 * (N : ℝ))) := by
      by_cases hfl : ⌊4 * (N : ℝ) * y⌋₊ ≤ N - 1
      · have hj_eq : j = ⌊4 * (N : ℝ) * y⌋₊ := Nat.min_eq_right hfl
        rw [hj_eq]
        constructor
        · rw [div_le_iff₀ h4N_pos]
          exact (Nat.floor_le (by positivity)).trans (le_of_eq (by ring))
        · rw [le_div_iff₀ h4N_pos]
          have hlt := Nat.lt_floor_add_one (4 * (N : ℝ) * y)
          linarith
      · have hj_eq : j = N - 1 := Nat.min_eq_left (Nat.le_of_not_le hfl)
        have hN_le_fl : N ≤ ⌊4 * (N : ℝ) * y⌋₊ := by omega
        have hN_le_prod : (N : ℝ) ≤ 4 * (N : ℝ) * y := (Nat.le_floor_iff (by positivity)).mp hN_le_fl
        rw [hj_eq]
        constructor
        · rw [div_le_iff₀ h4N_pos]
          have hNm1 : ((N - 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.sub_le N 1
          linarith
        · rw [le_div_iff₀ h4N_pos]
          have hNm1 : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by
            rw [Nat.cast_sub hN]; ring
          rw [hNm1]
          calc
            y * (4 * (N : ℝ)) ≤ (1 / 4) * (4 * (N : ℝ)) :=
              mul_le_mul_of_nonneg_right hy_le h4N_pos.le
            _ = (N : ℝ) := by ring
    have hc := hcell j hj y hy_mem
    change (C_num : ℝ) / (C_den : ℝ) ≤ (numConst : ℝ) / (2 * d ^ 5) + Φ y / (2 * d ^ 4) at hc
    rw [hΦ_abs x] at hc
    exact hc
  have hpt_all : ∀ x : ℝ,
      f₁ x * ((C_num : ℝ) / (C_den : ℝ)) ≤
        f₁ x * ((numConst : ℝ) / (2 * d ^ 5) + Φ x / (2 * d ^ 4)) := by
    intro x
    by_cases hx : x ∈ I
    · exact mul_le_mul_of_nonneg_left (hpt_I x hx) (hf₁0 x)
    · rw [hf₁supp x hx, zero_mul, zero_mul]
  have hf₁int := integrable_of_memLp_Icc hf₁m hf₁supp
  have hΦ_cont : Continuous Φ := continuous_finsetSum _ fun k _ =>
    continuous_const.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))
  have hΦ_bound : ∃ C : ℝ, ∀ x, |Φ x| ≤ C := by
    refine ⟨∑ k ∈ Finset.Icc 1 (K + 1), |(alphaFn k : ℝ)|, fun x => ?_⟩
    calc
      |Φ x| ≤ ∑ k ∈ Finset.Icc 1 (K + 1), |(alphaFn k : ℝ) * Real.cos (2 * Real.pi * (k : ℝ) * x)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.Icc 1 (K + 1), |(alphaFn k : ℝ)| := by
        apply Finset.sum_le_sum
        intro k _
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  have hf₁Φ_int : Integrable (fun x => f₁ x * Φ x) :=
    integrable_mul_bounded_cont hf₁int hΦ_cont hΦ_bound
  have h_rhs_int : Integrable (fun x => f₁ x * ((numConst : ℝ) / (2 * d ^ 5) + Φ x / (2 * d ^ 4))) := by
    have hrew : (fun x => f₁ x * ((numConst : ℝ) / (2 * d ^ 5) + Φ x / (2 * d ^ 4))) =
        fun x => ((numConst : ℝ) / (2 * d ^ 5)) * f₁ x + (1 / (2 * d ^ 4)) * (f₁ x * Φ x) := by
      ext x; ring
    rw [hrew]
    exact (hf₁int.const_mul _).add (hf₁Φ_int.const_mul _)
  have hint_mono := integral_mono (hf₁int.mul_const _) h_rhs_int hpt_all
  have hlhs_eval : (∫ x, f₁ x * ((C_num : ℝ) / (C_den : ℝ))) = (C_num : ℝ) / (C_den : ℝ) := by
    rw [integral_mul_const, hf₁mass_all, one_mul]
  have hcos_int : ∀ k : ℕ, Integrable (fun x => f₁ x * Real.cos (2 * Real.pi * (k : ℝ) * x)) :=
    fun k => integrable_mul_bounded_cont hf₁int
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))
      ⟨1, fun x => Real.abs_cos_le_one _⟩
  have hrhs_eval :
      (∫ x, f₁ x * ((numConst : ℝ) / (2 * d ^ 5) + Φ x / (2 * d ^ 4))) =
        (numConst : ℝ) / (2 * d ^ 5) +
          (∑ k ∈ Finset.Icc 1 (K + 1), (alphaFn k : ℝ) * a k) / (2 * d ^ 4) := by
    have hrew : (fun x => f₁ x * ((numConst : ℝ) / (2 * d ^ 5) + Φ x / (2 * d ^ 4))) =
        fun x => ((numConst : ℝ) / (2 * d ^ 5)) * f₁ x + (1 / (2 * d ^ 4)) * (f₁ x * Φ x) := by
      ext x; ring
    rw [hrew, integral_add (hf₁int.const_mul _) (hf₁Φ_int.const_mul _),
      integral_const_mul ((numConst : ℝ) / (2 * d ^ 5)) f₁,
      integral_const_mul (1 / (2 * d ^ 4)) (fun x => f₁ x * Φ x),
      hf₁mass_all, mul_one]
    have hΦ_eval : (∫ x, f₁ x * Φ x) = ∑ k ∈ Finset.Icc 1 (K + 1), (alphaFn k : ℝ) * a k := by
      have hrew2 : (fun x => f₁ x * Φ x) =
          fun x => ∑ k ∈ Finset.Icc 1 (K + 1), (alphaFn k : ℝ) * (f₁ x * Real.cos (2 * Real.pi * (k : ℝ) * x)) := by
        ext x; dsimp [Φ]; rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => by ring
      rw [hrew2, integral_finsetSum _ (fun k _ => (hcos_int k).const_mul _)]
      refine Finset.sum_congr rfl fun k _ => integral_const_mul _ _
    rw [hΦ_eval]
    ring
  rw [hlhs_eval, hrhs_eval] at hint_mono
  have hle_Omega : (C_num : ℝ) / (C_den : ℝ) ≤ Ω := hint_mono.trans hcert_le_omega
  have hM2_pos : 0 < M ^ 2 := sq_pos_of_pos hMpos
  change ((C_num : ℝ) / (C_den : ℝ)) * M ^ 2 ≤ S_sup
  calc
    ((C_num : ℝ) / (C_den : ℝ)) * M ^ 2 ≤ Ω * M ^ 2 :=
      mul_le_mul_of_nonneg_right hle_Omega hM2_pos.le
    _ = S_sup := by dsimp [Ω]; field_simp [hM2_pos.ne']

section TaylorAndPi

/- ### 1. Alternating Taylor Bounds and Pi Bounds -/

private lemma nonneg_of_hasDerivAt_nonneg {g g' : ℝ → ℝ}
    (hg0 : g 0 = 0)
    (hderiv : ∀ x, HasDerivAt g (g' x) x)
    (hnonneg : ∀ x, 0 ≤ x → 0 ≤ g' x)
    {t : ℝ} (ht : 0 ≤ t) : 0 ≤ g t := by
  have hmono : MonotoneOn g (Set.Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (0 : ℝ))
      (fun x _ => (hderiv x).continuousAt.continuousWithinAt)
      (fun x _ => (hderiv x).hasDerivWithinAt)
      (fun x hx => hnonneg x (by rw [interior_Ici] at hx; exact hx.le))
  rw [← hg0]
  exact hmono (Set.mem_Ici.mpr le_rfl) ht ht

private lemma sin_le_id {t : ℝ} (ht : 0 ≤ t) : Real.sin t ≤ t := by
  have h := nonneg_of_hasDerivAt_nonneg (g := fun x => x - Real.sin x)
    (g' := fun x => 1 - Real.cos x) (by simp)
    (fun x => (hasDerivAt_id x).sub (Real.hasDerivAt_sin x))
    (fun x _ => sub_nonneg.mpr (Real.cos_le_one x)) ht
  linarith

private lemma one_sub_sq_div_two_le_cos {t : ℝ} (ht : 0 ≤ t) :
    1 - t ^ 2 / 2 ≤ Real.cos t := by
  have h := nonneg_of_hasDerivAt_nonneg (g := fun x => Real.cos x - (1 - x ^ 2 / 2))
    (g' := fun x => x - Real.sin x) (by simp)
    (fun x => ((Real.hasDerivAt_cos x).sub
      ((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_pow 2 x).div_const 2))).congr_deriv
      (by norm_num; ring))
    (fun x hx => sub_nonneg.mpr (sin_le_id hx)) ht
  linarith

private lemma id_sub_cube_div_six_le_sin {t : ℝ} (ht : 0 ≤ t) :
    t - t ^ 3 / 6 ≤ Real.sin t := by
  have h := nonneg_of_hasDerivAt_nonneg (g := fun x => Real.sin x - (x - x ^ 3 / 6))
    (g' := fun x => Real.cos x - (1 - x ^ 2 / 2)) (by simp)
    (fun x => ((Real.hasDerivAt_sin x).sub
      ((hasDerivAt_id x).sub ((hasDerivAt_pow 3 x).div_const 6))).congr_deriv
      (by norm_num; ring))
    (fun x hx => sub_nonneg.mpr (one_sub_sq_div_two_le_cos hx)) ht
  linarith

private lemma cos_le_taylor_deg4 {t : ℝ} (ht : 0 ≤ t) :
    Real.cos t ≤ 1 - t ^ 2 / 2 + t ^ 4 / 24 := by
  have h := nonneg_of_hasDerivAt_nonneg
    (g := fun x => (1 - x ^ 2 / 2 + x ^ 4 / 24) - Real.cos x)
    (g' := fun x => Real.sin x - (x - x ^ 3 / 6)) (by simp)
    (fun x => ((((hasDerivAt_const x (1 : ℝ)).sub
      ((hasDerivAt_pow 2 x).div_const 2)).add
      ((hasDerivAt_pow 4 x).div_const 24)).sub (Real.hasDerivAt_cos x)).congr_deriv
      (by norm_num; ring))
    (fun x hx => sub_nonneg.mpr (id_sub_cube_div_six_le_sin hx)) ht
  linarith

private lemma sin_le_taylor_deg5 {t : ℝ} (ht : 0 ≤ t) :
    Real.sin t ≤ t - t ^ 3 / 6 + t ^ 5 / 120 := by
  have h := nonneg_of_hasDerivAt_nonneg
    (g := fun x => (x - x ^ 3 / 6 + x ^ 5 / 120) - Real.sin x)
    (g' := fun x => (1 - x ^ 2 / 2 + x ^ 4 / 24) - Real.cos x) (by simp)
    (fun x => ((((hasDerivAt_id x).sub
      ((hasDerivAt_pow 3 x).div_const 6)).add
      ((hasDerivAt_pow 5 x).div_const 120)).sub (Real.hasDerivAt_sin x)).congr_deriv
      (by norm_num; ring))
    (fun x hx => sub_nonneg.mpr (cos_le_taylor_deg4 hx)) ht
  linarith

theorem cos_taylor_deg6_le {t : ℝ} (ht : 0 ≤ t) :
    1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 ≤ Real.cos t := by
  have h := nonneg_of_hasDerivAt_nonneg
    (g := fun x => Real.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720))
    (g' := fun x => (x - x ^ 3 / 6 + x ^ 5 / 120) - Real.sin x) (by simp)
    (fun x => ((Real.hasDerivAt_cos x).sub
      ((((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_pow 2 x).div_const 2)).add
        ((hasDerivAt_pow 4 x).div_const 24)).sub ((hasDerivAt_pow 6 x).div_const 720))).congr_deriv
      (by norm_num; ring))
    (fun x hx => sub_nonneg.mpr (sin_le_taylor_deg5 hx)) ht
  linarith

theorem sin_taylor_deg7_le {t : ℝ} (ht : 0 ≤ t) :
    t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 ≤ Real.sin t := by
  have h := nonneg_of_hasDerivAt_nonneg
    (g := fun x => Real.sin x - (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040))
    (g' := fun x => Real.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720)) (by simp)
    (fun x => ((Real.hasDerivAt_sin x).sub
      ((((hasDerivAt_id x).sub ((hasDerivAt_pow 3 x).div_const 6)).add
        ((hasDerivAt_pow 5 x).div_const 120)).sub ((hasDerivAt_pow 7 x).div_const 5040))).congr_deriv
      (by norm_num; ring))
    (fun x hx => sub_nonneg.mpr (cos_taylor_deg6_le hx)) ht
  linarith

theorem cos_le_taylor_deg8 {t : ℝ} (ht : 0 ≤ t) :
    Real.cos t ≤ 1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320 := by
  have h := nonneg_of_hasDerivAt_nonneg
    (g := fun x => (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320) - Real.cos x)
    (g' := fun x => Real.sin x - (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040)) (by simp)
    (fun x => ((((((hasDerivAt_const x (1 : ℝ)).sub
      ((hasDerivAt_pow 2 x).div_const 2)).add
      ((hasDerivAt_pow 4 x).div_const 24)).sub
      ((hasDerivAt_pow 6 x).div_const 720)).add
      ((hasDerivAt_pow 8 x).div_const 40320)).sub (Real.hasDerivAt_cos x)).congr_deriv
      (by norm_num; ring))
    (fun x hx => sub_nonneg.mpr (sin_taylor_deg7_le hx)) ht
  linarith

theorem sin_le_taylor_deg9 {t : ℝ} (ht : 0 ≤ t) :
    Real.sin t ≤ t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 + t ^ 9 / 362880 := by
  have h := nonneg_of_hasDerivAt_nonneg
    (g := fun x => (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880) - Real.sin x)
    (g' := fun x => (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320) - Real.cos x)
    (by simp)
    (fun x => ((((((hasDerivAt_id x).sub
      ((hasDerivAt_pow 3 x).div_const 6)).add
      ((hasDerivAt_pow 5 x).div_const 120)).sub
      ((hasDerivAt_pow 7 x).div_const 5040)).add
      ((hasDerivAt_pow 9 x).div_const 362880)).sub (Real.hasDerivAt_sin x)).congr_deriv
      (by norm_num; ring))
    (fun x hx => sub_nonneg.mpr (cos_le_taylor_deg8 hx)) ht
  linarith

theorem pi_bounds_8d :
    (314159265 : ℝ) / 100000000 < Real.pi ∧ Real.pi < (314159266 : ℝ) / 100000000 :=
  ⟨by linarith [Real.pi_gt_d20], by linarith [Real.pi_lt_d20]⟩

end TaylorAndPi

section CertData

/- ### 2. Exact Certificate Data (N = 80, K = 65, D = 100000, M_cos = 10^7) -/

def certN : Nat := 80
def certK : Nat := 65
def certD : Int := 100000
def certMcos : Int := 10000000
def piScale : Int := 100000000
def piLoNum : Int := 314159265
def piHiNum : Int := 314159266

def vf_0 : List Int := [-1475, 1364, -72, -754, 286, 489, -333, -328, 347, 227, -339, -148, 331, 92, -317, -44, 305, 6, -289, 28, 275, -56, -260, 82, 245, -105, -230, 126, 214, -145, -198, 164, 181, -181, -164, 198, 145, -214, -126, 230, 105, -245, -82, 260, 56, -275, -28, 289, -6, -305, 44, 317, -92, -331, 148, 339, -227, -347, 328, 333, -489, -286, 754, 72, -1364, 1475]
def vf_1 : List Int := [1811, -4165, 2727, 1212, -2528, -55, 2097, -528, -1694, 858, 1342, -1055, -1035, 1173, 764, -1239, -522, 1267, 303, -1268, -103, 1247, -80, -1208, 249, 1152, -404, -1082, 546, 999, -677, -904, 796, 796, -904, -677, 999, 546, -1082, -404, 1152, 249, -1208, -80, 1247, -103, -1268, 303, 1267, -522, -1239, 764, 1173, -1035, -1055, 1342, 858, -1694, -528, 2097, -55, -2528, 1212, 2727, -4165, 1811]
def vf_2 : List Int := [-1733, 4382, -4684, 409, 3808, -2208, -2623, 3046, 1504, -3409, -478, 3477, -445, -3325, 1263, 3005, -1964, -2547, 2540, 1984, -2978, -1341, 3272, 650, -3416, 62, 3411, -766, -3260, 1434, 2972, -2040, -2560, 2560, 2040, -2972, -1434, 3260, 766, -3411, -62, 3416, -650, -3272, 1341, 2978, -1984, -2540, 2547, 1964, -3005, -1263, 3325, 445, -3477, 478, 3409, -1504, -3046, 2623, 2208, -3808, -409, 4684, -4382, 1733]
def vf_3 : List Int := [1209, -3619, 4244, -1168, -2988, 3054, 1294, -3772, 394, 3752, -1920, -3181, 3173, 2195, -4061, -926, 4523, -489, -4528, 1908, 4084, -3195, -3239, 4228, 2071, -4912, -689, 5183, -780, -5015, 2205, 4422, -3456, -3456, 4422, 2205, -5015, -780, 5183, -689, -4912, 2071, 4228, -3239, -3195, 4084, 1908, -4528, -489, 4523, -926, -4061, 2195, 3173, -3181, -1920, 3752, 394, -3772, 1294, 3054, -2988, -1168, 4244, -3619, 1209]
def vf_4 : List Int := [-1279, 3811, -5042, 1913, 3195, -4059, -696, 4513, -1698, -3778, 3603, 2200, -4742, -138, 4964, -2014, -4255, 3873, 2754, -5112, -720, 5517, -1500, -5011, 3533, 3672, -5037, -1714, 5759, -546, -5576, 2741, 4513, -4513, -2741, 5576, 546, -5759, 1714, 5037, -3672, -3533, 5011, 1500, -5517, 720, 5112, -2754, -3873, 4255, 2014, -4964, 138, 4742, -2200, -3603, 3778, 1698, -4513, 696, 4059, -3195, -1913, 5042, -3811, 1279]
def vf_5 : List Int := [1039, -3454, 4836, -2466, -2561, 4663, -628, -4594, 3531, 2828, -5363, -46, 5663, -2919, -4374, 5233, 1852, -6256, 1227, 5698, -4042, -3695, 5847, 763, -6161, 2333, 4896, -4783, -2381, 5947, -726, -5519, 3611, 3611, -5519, -726, 5947, -2381, -4783, 4896, 2333, -6161, 763, 5847, -3695, -4042, 5698, 1227, -6256, 1852, 5233, -4374, -2919, 5663, -46, -5363, 2828, 3531, -4594, -628, 4663, -2561, -2466, 4836, -3454, 1039]
def vf_6 : List Int := [-1058, 3487, -5293, 3141, 2263, -5242, 1776, 4255, -4915, -1158, 5969, -2639, -4577, 5597, 1297, -6541, 2616, 5080, -5671, -1736, 6708, -2253, -5322, 5406, 2022, -6549, 1965, 5261, -5152, -2030, 6352, -1927, -5122, 5122, 1927, -6352, 2030, 5152, -5261, -1965, 6549, -2022, -5406, 5322, 2253, -6708, 1736, 5671, -5080, -2616, 6541, -1297, -5597, 4577, 2639, -5969, 1158, 4915, -4255, -1776, 5242, -2263, -3141, 5293, -3487, 1058]
def vf_7 : List Int := [918, -3294, 5224, -3678, -1585, 5596, -3175, -3533, 6211, -883, -5932, 5164, 2497, -7017, 2327, 5433, -6064, -1181, 6797, -3599, -4141, 6488, -562, -6027, 4926, 2456, -6736, 2402, 5075, -6072, -792, 6686, -3930, -3930, 6686, -792, -6072, 5075, 2402, -6736, 2456, 4926, -6027, -562, 6488, -4141, -3599, 6797, -1181, -6064, 5433, 2327, -7017, 2497, 5164, -5932, -883, 6211, -3533, -3175, 5596, -1585, -3678, 5224, -3294, 918]
def vf_8 : List Int := [-915, 3255, -5504, 4307, 943, -5690, 4437, 2168, -6685, 3336, 4307, -6963, 1115, 6219, -6009, -1513, 7152, -4126, -3773, 7050, -1942, -5369, 6281, 195, -6426, 5086, 2293, -7020, 3412, 4338, -6959, 1217, 6026, -6026, -1217, 6959, -4338, -3412, 7020, -2293, -5086, 6426, -195, -6281, 5369, 1942, -7050, 3773, 4126, -7152, 1513, 6009, -6219, -1115, 6963, -4307, -3336, 6685, -2168, -4437, 5690, -943, -4307, 5504, -3255, 915]
def vf_9 : List Int := [818, -3123, 5477, -4834, -132, 5656, -5694, -681, 6785, -5447, -2187, 7477, -4340, -3632, 7457, -3026, -4603, 7111, -1912, -5318, 6790, -873, -6065, 6405, 337, -6760, 5718, 1644, -7158, 4775, 2805, -7265, 3796, 3796, -7265, 2805, 4775, -7158, 1644, 5718, -6760, 337, 6405, -6065, -873, 6790, -5318, -1912, 7111, -4603, -3026, 7457, -3632, -4340, 7477, -2187, -5447, 6785, -681, -5694, 5656, -132, -4834, 5477, -3123, 818]
def vf_10 : List Int := [-804, 3043, -5630, 5393, -747, -5198, 6630, -1340, -5760, 7161, -1054, -6261, 7081, -611, -6360, 6778, -432, -6220, 6639, -481, -6177, 6714, -482, -6330, 6774, -302, -6498, 6670, -84, -6517, 6507, 2, -6461, 6461, -2, -6507, 6517, 84, -6670, 6498, 302, -6774, 6330, 482, -6714, 6177, 481, -6639, 6220, 432, -6778, 6360, 611, -7081, 6261, 1054, -7161, 5760, 1340, -6630, 5198, 747, -5393, 5630, -3043, 804]
def vf_11 : List Int := [730, -2935, 5603, -5884, 1678, 4695, -7415, 3179, 4415, -7962, 3899, 3806, -7810, 4562, 2737, -7448, 5419, 1525, -7149, 6261, 450, -6803, 6846, -545, -6211, 7210, -1622, -5416, 7512, -2740, -4587, 7734, -3734, -3734, 7734, -4587, -2740, 7512, -5416, -1622, 7210, -6211, -545, 6846, -6803, 450, 6261, -7149, 1525, 5419, -7448, 2737, 4562, -7810, 3806, 3899, -7962, 4415, 3179, -7415, 4695, 1678, -5884, 5603, -2935, 730]
def vf_12 : List Int := [-708, 2828, -5649, 6335, -2681, -3695, 7648, -5180, -2038, 7660, -6614, -102, 6568, -7399, 2144, 4774, -7760, 4376, 2702, -7627, 6161, 557, -6811, 7281, -1647, -5286, 7774, -3831, -3286, 7718, -5733, -1104, 7062, -7062, 1104, 5733, -7718, 3286, 3831, -7774, 5286, 1647, -7281, 6811, -557, -6161, 7627, -2702, -4376, 7760, -4774, -2144, 7399, -6568, 102, 6614, -7660, 2038, 5180, -7648, 3695, 2681, -6335, 5649, -2828, 708]
def vf_13 : List Int := [647, -2725, 5592, -6746, 3664, 2734, -7674, 6707, -287, -6367, 7960, -3491, -3433, 7699, -6284, 194, 6137, -7900, 3631, 3433, -7850, 6294, -37, -6203, 7804, -3558, -3408, 7840, -6324, 2, 6290, -7804, 3461, 3461, -7804, 6290, 2, -6324, 7840, -3408, -3557, 7804, -6203, -37, 6294, -7850, 3433, 3631, -7900, 6137, 194, -6284, 7699, -3433, -3491, 7960, -6367, -287, 6707, -7674, 2734, 3664, -6746, 5592, -2725, 647]
def vf_14 : List Int := [-622, 2599, -5547, 7062, -4668, -1310, 7002, -7935, 3112, 3922, -8065, 6612, -824, -5392, 8044, -5363, -1008, 6805, -7960, 3621, 3162, -7713, 7032, -1664, -4819, 8106, -5921, -343, 6403, -8064, 4224, 2428, -7393, 7393, -2428, -4224, 8064, -6403, 343, 5921, -8106, 4819, 1664, -7032, 7713, -3162, -3621, 7960, -6805, 1008, 5362, -8044, 5392, 824, -6612, 8065, -3922, -3112, 7935, -7002, 1310, 4668, -7062, 5547, -2599, 622]
def vf_15 : List Int := [569, -2493, 5444, -7352, 5602, 11, -6157, 8492, -5353, -1035, 6571, -8091, 4888, 1200, -6676, 8185, -4675, -1711, 7003, -8021, 4251, 2038, -7138, 7972, -3964, -2472, 7386, -7813, 3555, 2816, -7516, 7711, -3228, -3228, 7711, -7516, 2816, 3555, -7813, 7386, -2472, -3964, 7972, -7138, 2038, 4251, -8021, 7003, -1711, -4675, 8185, -6676, 1200, 4888, -8091, 6571, -1035, -5353, 8492, -6157, 11, 5602, -7352, 5444, -2493, 569]
def vf_16 : List Int := [-541, 2350, -5308, 7494, -6470, 1631, 4615, -8391, 7356, -2300, -3778, 7724, -7678, 3651, 2403, -7283, 8229, -4685, -1335, 6555, -8285, 5673, -37, -5690, 8393, -6553, 1196, 4742, -8124, 7222, -2498, -3606, 7821, -7821, 3606, 2498, -7222, 8124, -4742, -1196, 6553, -8393, 5690, 37, -5674, 8285, -6555, 1335, 4685, -8229, 7283, -2403, -3651, 7678, -7724, 3778, 2300, -7356, 8391, -4615, -1631, 6470, -7494, 5308, -2350, 541]
def vf_17 : List Int := [494, -2239, 5156, -7638, 7247, -3058, -3034, 7626, -8351, 5157, 246, -5485, 8301, -7301, 2797, 3065, -7426, 8271, -5309, -86, 5484, -8362, 7303, -2802, -2978, 7336, -8297, 5414, 19, -5470, 8345, -7301, 2873, 2873, -7301, 8345, -5470, 19, 5414, -8297, 7336, -2978, -2802, 7303, -8362, 5483, -86, -5309, 8271, -7426, 3065, 2797, -7301, 8301, -5485, 246, 5157, -8351, 7626, -3034, -3058, 7247, -7638, 5156, -2239, 494]
def vf_18 : List Int := [-464, 2083, -4938, 7587, -7859, 4641, 922, -6109, 8533, -7417, 3476, 1770, -6411, 8560, -7176, 2793, 2680, -6982, 8478, -6619, 2073, 3381, -7470, 8473, -6035, 1210, 4087, -7779, 8345, -5488, 381, 4839, -8069, 8069, -4839, -381, 5488, -8345, 7779, -4087, -1210, 6035, -8473, 7470, -3381, -2073, 6619, -8478, 6982, -2680, -2793, 7176, -8560, 6411, -1770, -3476, 7417, -8533, 6109, -922, -4641, 7859, -7587, 4938, -2083, 464]
def vf_19 : List Int := [421, -1962, 4726, -7551, 8366, -5933, 1040, 4144, -7628, 8451, -6518, 2372, 2712, -6907, 8631, -7322, 3539, 1425, -5941, 8439, -7980, 4726, 136, -4920, 8027, -8382, 5815, -1212, -3791, 7460, -8566, 6728, -2542, -2542, 6728, -8566, 7460, -3791, -1212, 5815, -8382, 8027, -4920, 136, 4726, -7980, 8439, -5941, 1425, 3539, -7322, 8631, -6907, 2712, 2372, -6518, 8451, -7628, 4144, 1040, -5933, 8366, -7551, 4726, -1962, 421]
def vf_20 : List Int := [-390, 1796, -4435, 7298, -8623, 7171, -3227, -1659, 5815, -8195, 8330, -6116, 2020, 2755, -6668, 8551, -7969, 5131, -776, -3871, 7381, -8674, 7428, -4063, -481, 4931, -7956, 8612, -6732, 2922, 1718, -5891, 8368, -8368, 5891, -1718, -2922, 6732, -8612, 7956, -4931, 481, 4063, -7428, 8674, -7381, 3871, 776, -5131, 7969, -8551, 6668, -2755, -2020, 6116, -8330, 8195, -5814, 1659, 3227, -7171, 8623, -7298, 4435, -1796, 390]
def vf_21 : List Int := [349, -1664, 4162, -7070, 8774, -8064, 5062, -890, -3276, 6628, -8514, 8373, -6105, 2316, 1968, -5736, 8165, -8652, 7006, -3631, -594, 4647, -7597, 8731, -7729, 4832, -782, -3438, 6841, -8605, 8269, -5912, 2138, 2138, -5912, 8269, -8605, 6841, -3438, -782, 4832, -7729, 8731, -7597, 4647, -594, -3631, 7006, -8652, 8165, -5736, 1968, 2316, -6105, 8373, -8514, 6628, -3276, -890, 5062, -8064, 8774, -7070, 4162, -1664, 349]
def vf_22 : List Int := [-317, 1493, -3811, 6625, -8627, 8722, -6774, 3491, 278, -3929, 6927, -8630, 8555, -6720, 3606, 153, -3909, 6956, -8618, 8527, -6760, 3709, 70, -3878, 6929, -8575, 8518, -6816, 3786, 22, -3846, 6883, -8541, 8541, -6883, 3845, -22, -3786, 6816, -8518, 8575, -6929, 3878, -70, -3709, 6760, -8527, 8618, -6956, 3909, -153, -3606, 6720, -8555, 8630, -6927, 3929, -278, -3491, 6774, -8722, 8627, -6625, 3811, -1493, 317]
def vf_23 : List Int := [277, -1350, 3478, -6201, 8368, -9004, 7964, -5726, 2772, 597, -3983, 6775, -8432, 8736, -7729, 5544, -2455, -1048, 4359, -6964, 8504, -8740, 7592, -5239, 2084, 1379, -4640, 7192, -8608, 8665, -7381, 4958, -1748, -1748, 4958, -7381, 8665, -8608, 7192, -4640, 1379, 2084, -5239, 7592, -8740, 8504, -6964, 4359, -1048, -2455, 5544, -7729, 8736, -8432, 6775, -3983, 597, 2772, -5726, 7964, -9004, 8368, -6201, 3478, -1350, 277]
def vf_24 : List Int := [-244, 1174, -3076, 5581, -7804, 8934, -8742, 7501, -5518, 2923, 116, -3197, 5834, -7713, 8701, -8696, 7625, -5591, 2896, 105, -3098, 5757, -7727, 8737, -8692, 7635, -5671, 3000, 44, -3058, 5689, -7658, 8726, -8726, 7659, -5689, 3058, -44, -3000, 5671, -7635, 8692, -8737, 7727, -5757, 3098, -105, -2896, 5591, -7625, 8696, -8701, 7713, -5834, 3197, -116, -2923, 5518, -7501, 8742, -8934, 7804, -5581, 3076, -1174, 244]
def vf_25 : List Int := [207, -1020, 2691, -4977, 7137, -8503, 8919, -8580, 7618, -5998, 3766, -1180, -1451, 3926, -6093, 7743, -8678, 8823, -8209, 6886, -4938, 2535, 79, -2671, 5039, -6975, 8284, -8849, 8641, -7680, 6030, -3838, 1315, 1315, -3838, 6031, -7680, 8641, -8849, 8284, -6975, 5039, -2671, 79, 2535, -4938, 6886, -8208, 8823, -8678, 7743, -6093, 3926, -1451, -1180, 3766, -5998, 7618, -8580, 8919, -8503, 7137, -4977, 2691, -1020, 207]
def vf_26 : List Int := [-173, 843, -2253, 4217, -6202, 7698, -8543, 8863, -8751, 8137, -6956, 5308, -3376, 1278, 923, -3103, 5076, -6702, 7921, -8681, 8903, -8549, 7666, -6334, 4615, -2590, 397, 1801, -3879, 5737, -7253, 8306, -8836, 8836, -8306, 7253, -5737, 3879, -1801, -397, 2590, -4615, 6334, -7666, 8549, -8903, 8681, -7921, 6702, -5076, 3103, -923, -1278, 3376, -5308, 6956, -8137, 8751, -8863, 8543, -7698, 6202, -4217, 2253, -843, 173]
def vf_27 : List Int := [-136, 678, -1820, 3456, -5168, 6572, -7589, 8329, -8831, 8994, -8750, 8147, -7260, 6105, -4683, 3062, -1340, -419, 2175, -3856, 5372, -6664, 7699, -8439, 8836, -8873, 8565, -7925, 6964, -5720, 4255, -2627, 889, 889, -2627, 4255, -5720, 6964, -7925, 8565, -8873, 8836, -8439, 7699, -6664, 5372, -3856, 2175, -419, -1341, 3063, -4683, 6105, -7260, 8147, -8750, 8994, -8831, 8329, -7589, 6572, -5168, 3456, -1820, 678, -136]
def vf_28 : List Int := [102, -503, 1364, -2607, 3962, -5169, 6158, -7011, 7776, -8392, 8782, -8954, 8952, -8775, 8389, -7795, 7036, -6141, 5106, -3940, 2688, -1393, 69, 1270, -2582, 3822, -4971, 6020, -6938, 7690, -8261, 8657, -8865, 8865, -8657, 8261, -7690, 6938, -6020, 4971, -3822, 2582, -1270, -69, 1393, -2688, 3940, -5106, 6141, -7036, 7795, -8389, 8775, -8952, 8954, -8782, 8392, -7776, 7011, -6158, 5169, -3962, 2607, -1364, 503, -102]
def vf_29 : List Int := [-66, 330, -895, 1728, -2650, 3501, -4259, 4988, -5713, 6388, -6976, 7489, -7946, 8333, -8626, 8825, -8946, 8983, -8925, 8770, -8533, 8216, -7812, 7324, -6766, 6144, -5457, 4711, -3921, 3094, -2233, 1347, -450, -449, 1346, -2233, 3093, -3920, 4711, -5456, 6143, -6765, 7323, -7811, 8216, -8533, 8770, -8924, 8983, -8945, 8825, -8626, 8333, -7946, 7488, -6976, 6388, -5713, 4988, -4259, 3501, -2650, 1727, -895, 330, -66]
def vf_30 : List Int := [32, -159, 435, -843, 1305, -1748, 2157, -2564, 2987, -3413, 3820, -4211, 4602, -4990, 5362, -5714, 6056, -6390, 6706, -7001, 7279, -7543, 7789, -8010, 8211, -8394, 8557, -8694, 8808, -8901, 8974, -9021, 9042, -9042, 9021, -8974, 8902, -8808, 8695, -8557, 8394, -8211, 8011, -7789, 7544, -7279, 7002, -6707, 6390, -6057, 5715, -5362, 4990, -4602, 4212, -3820, 3413, -2988, 2564, -2158, 1748, -1305, 843, -436, 159, -32]
def cert_vf : List (List Int) := [vf_0, vf_1, vf_2, vf_3, vf_4, vf_5, vf_6, vf_7, vf_8, vf_9, vf_10, vf_11, vf_12, vf_13, vf_14, vf_15, vf_16, vf_17, vf_18, vf_19, vf_20, vf_21, vf_22, vf_23, vf_24, vf_25, vf_26, vf_27, vf_28, vf_29, vf_30]
def vnu_0 : List Int := [-1612, 1147, 336, -685, -151, 505, 105, -398, -83, 337, 80, -288, -77, 258, 81, -230, -82, 211, 87, -193, -90, 180, 96, -166, -100, 157, 106, -147, -111, 139, 118, -131, -124, 124, 131, -118, -139, 111, 147, -106, -157, 100, 166, -96, -180, 90, 193, -87, -211, 82, 230, -81, -258, 77, 288, -80, -337, 83, 398, -105, -505, 151, 685, -336, -1147, 1612]
def vnu_1 : List Int := [2518, -5120, 2093, 2551, -2038, -1657, 1801, 1241, -1594, -1015, 1429, 882, -1297, -800, 1190, 748, -1103, -716, 1030, 697, -969, -687, 917, 685, -872, -689, 833, 697, -800, -710, 771, 726, -747, -747, 726, 771, -710, -800, 697, 833, -689, -872, 685, 917, -687, -969, 697, 1030, -716, -1103, 748, 1190, -800, -1297, 882, 1429, -1015, -1594, 1241, 1801, -1657, -2038, 2551, 2093, -5120, 2518]
def vnu_2 : List Int := [-3180, 8332, -8207, -416, 6475, -1453, -5219, 2114, 4376, -2362, -3789, 2449, 3373, -2461, -3065, 2441, 2837, -2406, -2662, 2368, 2530, -2329, -2429, 2294, 2353, -2265, -2298, 2242, 2259, -2226, -2234, 2219, 2221, -2221, -2219, 2234, 2226, -2259, -2242, 2298, 2265, -2353, -2294, 2429, 2329, -2530, -2368, 2662, 2406, -2837, -2441, 3065, 2461, -3373, -2449, 3789, 2362, -4376, -2114, 5219, 1453, -6475, 416, 8207, -8332, 3180]
def vnu_3 : List Int := [3896, -12898, 17911, -10062, -4416, 8016, 2041, -7868, -64, 7161, -1030, -6537, 1725, 6006, -2197, -5547, 2517, 5168, -2753, -4844, 2927, 4574, -3067, -4342, 3183, 4147, -3288, -3978, 3386, 3833, -3486, -3705, 3591, 3591, -3705, -3486, 3833, 3386, -3978, -3288, 4147, 3183, -4342, -3067, 4574, 2927, -4844, -2753, 5168, 2517, -5547, -2197, 6006, 1725, -6537, -1030, 7161, -64, -7868, 2041, 8016, -4416, -10062, 17911, -12898, 3896]
def vnu_4 : List Int := [-63, 319, -814, 1390, -1838, 2162, -2546, 3059, -3544, 3897, -4241, 4696, -5158, 5500, -5801, 6192, -6605, 6908, -7153, 7471, -7818, 8062, -8236, 8471, -8739, 8910, -9003, 9148, -9328, 9415, -9420, 9469, -9557, 9557, -9469, 9420, -9415, 9328, -9148, 9003, -8910, 8739, -8471, 8236, -8062, 7818, -7471, 7153, -6908, 6605, -6192, 5801, -5500, 5158, -4696, 4241, -3897, 3544, -3059, 2547, -2162, 1838, -1390, 814, -319, 63]
def vnu_5 : List Int := [-13, -92, 621, -1684, 2929, -3854, 4446, -5146, 6117, -6973, 7456, -7864, 8481, -9057, 9275, -9331, 9543, -9749, 9624, -9298, 9097, -8920, 8446, -7762, 7196, -6689, 5928, -4968, 4136, -3408, 2474, -1364, 404, 403, -1364, 2474, -3407, 4136, -4968, 5928, -6689, 7196, -7762, 8446, -8920, 9097, -9297, 9624, -9749, 9543, -9331, 9275, -9057, 8481, -7864, 7456, -6973, 6117, -5146, 4446, -3854, 2929, -1684, 620, -92, -13]
def vnu_6 : List Int := [199, -1001, 2534, -4259, 5495, -6226, 7030, -8103, 8933, -9180, 9234, -9469, 9560, -9105, 8370, -7783, 7150, -6065, 4719, -3560, 2475, -1071, -514, 1833, -2944, 4233, -5609, 6635, -7336, 8103, -8889, 9274, -9265, 9265, -9274, 8889, -8103, 7336, -6635, 5609, -4233, 2944, -1833, 514, 1071, -2475, 3560, -4719, 6065, -7150, 7783, -8370, 9105, -9560, 9469, -9234, 9180, -8933, 8103, -7030, 6226, -5495, 4259, -2534, 1001, -199]
def vnu_7 : List Int := [-24, -198, 1276, -3397, 5773, -7319, 7970, -8616, 9567, -10024, 9466, -8530, 7839, -6923, 5190, -3112, 1418, 151, -2186, 4344, -5883, 6953, -8166, 9305, -9675, 9392, -9113, 8753, -7683, 6012, -4447, 3012, -1125, -1125, 3012, -4447, 6011, -7682, 8753, -9113, 9392, -9675, 9305, -8166, 6953, -5883, 4344, -2186, 151, 1418, -3112, 5190, -6923, 7839, -8530, 9466, -10024, 9567, -8616, 7970, -7319, 5773, -3397, 1276, -198, -24]
def vnu_8 : List Int := [-334, 1666, -4154, 6798, -8367, 8798, -9064, 9503, -9261, 7816, -5920, 4311, -2541, 41, 2609, -4561, 6057, -7710, 9138, -9558, 9176, -8712, 8010, -6416, 4166, -2081, 171, 2138, -4632, 6486, -7644, 8718, -9620, 9620, -8718, 7644, -6486, 4632, -2138, -171, 2081, -4166, 6416, -8010, 8712, -9176, 9558, -9138, 7710, -6057, 4561, -2609, -41, 2541, -4311, 5920, -7816, 9261, -9503, 9064, -8798, 8367, -6798, 4154, -1666, 334]
def vnu_9 : List Int := [27, 326, -1941, 4990, -8151, 9692, -9488, 8905, -8477, 7121, -4227, 962, 1534, -3773, 6472, -8797, 9596, -9282, 8837, -7913, 5633, -2511, -218, 2560, -5258, 7882, -9250, 9386, -9219, 8664, -6832, 3945, -1195, -1195, 3945, -6832, 8664, -9219, 9386, -9250, 7882, -5258, 2560, -218, -2511, 5633, -7913, 8837, -9281, 9596, -8797, 6472, -3773, 1534, 962, -4227, 7121, -8477, 8905, -9488, 9692, -8151, 4990, -1941, 326, 27]
def vnu_10 : List Int := [-468, 2303, -5611, 8816, -10059, 9259, -7908, 6636, -4422, 775, 2950, -5462, 7238, -9018, 9982, -9053, 6838, -4566, 2088, 1298, -4883, 7284, -8491, 9341, -9532, 8077, -5296, 2464, 213, -3389, 6631, -8623, 9174, -9174, 8623, -6631, 3389, -213, -2464, 5296, -8077, 9532, -9341, 8491, -7284, 4883, -1298, -2088, 4566, -6838, 9053, -9982, 9018, -7238, 5462, -2950, -775, 4422, -6636, 7908, -9259, 10059, -8816, 5611, -2303, 468]
def vnu_11 : List Int := [21, 485, -2611, 6398, -9866, 10618, -8584, 5812, -3334, 93, 4319, -8041, 9410, -9161, 8496, -6749, 2994, 1560, -4980, 7234, -9191, 10141, -8715, 5456, -2090, -1105, 4837, -8336, 9851, -9275, 7894, -5849, 2267, 2267, -5849, 7894, -9275, 9851, -8336, 4837, -1105, -2090, 5456, -8715, 10141, -9191, 7234, -4980, 1560, 2994, -6749, 8496, -9161, 9410, -8041, 4319, 94, -3334, 5812, -8584, 10618, -9866, 6398, -2611, 485, 21]
def vnu_12 : List Int := [-601, 2899, -6847, 10162, -10336, 7451, -3836, 747, 2746, -6927, 9800, -9728, 7715, -5326, 2202, 2315, -6736, 8990, -9187, 8547, -6763, 2911, 1954, -5684, 7857, -9309, 9567, -7351, 3220, 836, -4161, 7362, -9798, 9798, -7362, 4161, -836, -3220, 7351, -9567, 9309, -7857, 5684, -1954, -2911, 6763, -8547, 9187, -8990, 6736, -2315, -2202, 5326, -7715, 9728, -9800, 6927, -2746, -747, 3836, -7451, 10336, -10162, 6847, -2899, 601]
def vnu_13 : List Int := [-3, -677, 3272, -7546, 10761, -9949, 5405, -292, -3475, 6705, -9676, 10266, -7074, 2009, 2339, -5835, 9041, -10434, 8242, -3603, -922, 4719, -8303, 10420, -9126, 5033, -559, -3435, 7396, -10209, 9779, -6303, 2031, 2031, -6303, 9779, -10209, 7396, -3435, -559, 5033, -9126, 10420, -8303, 4718, -922, -3603, 8242, -10433, 9041, -5835, 2339, 2009, -7074, 10266, -9676, 6705, -3475, -292, 5405, -9949, 10761, -7546, 3272, -677, -3]
def vnu_14 : List Int := [731, -3440, 7807, -10733, 9159, -3713, -1932, 5559, -8012, 9717, -8703, 3929, 2075, -6225, 8376, -9431, 8291, -3754, -2281, 6634, -8641, 9272, -7932, 3471, 2551, -6977, 8846, -9145, 7607, -3163, -2849, 7292, -9007, 9007, -7292, 2849, 3163, -7607, 9145, -8846, 6977, -2551, -3471, 7932, -9272, 8641, -6634, 2281, 3754, -8291, 9431, -8376, 6225, -2075, -3929, 8704, -9717, 8012, -5559, 1932, 3713, -9159, 10733, -7807, 3440, -731]
def vnu_15 : List Int := [-28, 900, -3900, 8366, -10758, 7791, -667, -5818, 8711, -8963, 7647, -3625, -3100, 8909, -10283, 7795, -3876, -971, 6665, -10547, 9667, -4887, -537, 5168, -9003, 10373, -7213, 870, 4875, -8213, 9567, -8366, 3449, 3449, -8366, 9567, -8213, 4875, 870, -7213, 10373, -9003, 5168, -537, -4887, 9667, -10547, 6665, -971, -3876, 7795, -10283, 8909, -3100, -3625, 7647, -8963, 8711, -5818, -667, 7791, -10758, 8366, -3900, 900, -28]
def vnu_16 : List Int := [854, -3901, 8424, -10470, 6690, 1171, -7586, 9404, -8105, 5420, -586, -6077, 10586, -9573, 4607, 696, -5292, 9200, -10152, 6011, 1016, -6486, 8836, -8942, 6364, -317, -6598, 10003, -8830, 5269, -526, -5339, 10030, -10030, 5339, 526, -5269, 8830, -10003, 6598, 317, -6364, 8942, -8836, 6486, -1016, -6011, 10152, -9200, 5292, -696, -4607, 9573, -10586, 6077, 586, -5420, 8105, -9404, 7586, -1171, -6690, 10470, -8424, 3901, -854]
def vnu_17 : List Int := [-71, 1149, -4467, 8803, -9868, 4507, 4510, -10440, 9809, -5052, -402, 5764, -10011, 9738, -3464, -4733, 9353, -9188, 6026, -577, -6345, 10904, -9248, 2638, 4126, -8274, 9588, -7173, 446, 7264, -10663, 8285, -2934, -2934, 8285, -10663, 7264, 446, -7173, 9588, -8274, 4126, 2639, -9248, 10904, -6345, -577, 6026, -9188, 9353, -4733, -3464, 9738, -10011, 5764, -402, -5052, 9809, -10440, 4510, 4507, -9868, 8803, -4467, 1149, -71]
def vnu_18 : List Int := [966, -4257, 8653, -9400, 3306, 6121, -11294, 8910, -2642, -3039, 7353, -9817, 7514, 254, -8230, 10490, -7030, 1567, 4091, -9122, 10271, -4955, -3574, 9053, -9217, 5980, -600, -6227, 10829, -8929, 1644, 5412, -8799, 8799, -5412, -1644, 8929, -10829, 6227, 600, -5980, 9217, -9053, 3574, 4955, -10271, 9122, -4091, -1567, 7030, -10490, 8230, -254, -7514, 9817, -7353, 3039, 2642, -8910, 11294, -6121, -3306, 9400, -8653, 4257, -966]
def vnu_19 : List Int := [-125, 1412, -4941, 8824, -8204, 657, 8894, -12003, 6123, 2922, -8472, 9069, -5868, -739, 8449, -11380, 6026, 3381, -9403, 9243, -4800, -1919, 8683, -10898, 5432, 4021, -9983, 9179, -3880, -2941, 8969, -10456, 4729, 4729, -10456, 8969, -2941, -3880, 9179, -9983, 4021, 5432, -10898, 8683, -1919, -4800, 9243, -9403, 3381, 6026, -11380, 8448, -739, -5868, 9069, -8471, 2922, 6123, -12003, 8894, 657, -8204, 8824, -4941, 1412, -125]
def vnu_20 : List Int := [1058, -4471, 8443, -7617, -456, 10000, -11814, 4076, 5545, -9570, 7761, -3046, -3497, 9721, -10121, 2333, 7432, -10820, 6733, 44, -6071, 9737, -8039, -153, 9114, -10971, 4961, 2919, -7980, 9202, -5616, -2687, 10353, -10353, 2687, 5616, -9202, 7980, -2919, -4961, 10971, -9114, 153, 8039, -9737, 6071, -44, -6733, 10820, -7432, -2333, 10121, -9721, 3497, 3046, -7761, 9570, -5545, -4076, 11814, -10000, 455, 7617, -8443, 4471, -1058]
def vnu_21 : List Int := [-189, 1679, -5286, 8419, -5968, -3101, 11459, -10019, -752, 10373, -10423, 2838, 5177, -9220, 7937, -974, -8212, 11654, -4952, -5991, 11127, -7303, -768, 7588, -9878, 5486, 4129, -11425, 9095, 886, -9201, 9743, -3927, -3927, 9743, -9201, 886, 9095, -11425, 4129, 5486, -9878, 7588, -768, -7303, 11127, -5991, -4952, 11654, -8212, -974, 7937, -9220, 5177, 2838, -10423, 10373, -752, -10019, 11459, -3101, -5968, 8419, -5286, 1679, -189]
def vnu_22 : List Int := [1120, -4502, 7770, -5315, -3947, 11892, -8966, -3110, 11922, -9227, -342, 7500, -8766, 5231, 2077, -9682, 10234, -1006, -9644, 11079, -3128, -5661, 9199, -7079, 353, 8085, -11196, 4211, 7089, -11559, 5931, 3074, -8544, 8544, -3074, -5931, 11559, -7089, -4211, 11196, -8085, -353, 7079, -9199, 5661, 3128, -11079, 9644, 1006, -10234, 9682, -2077, -5231, 8766, -7500, 342, 9227, -11922, 3110, 8966, -11892, 3947, 5315, -7770, 4502, -1120]
def vnu_23 : List Int := [-261, 1934, -5474, 7616, -3439, -6131, 11686, -5276, -7762, 13051, -4623, -7786, 11368, -4521, -4845, 9541, -7029, -1510, 10083, -9950, -600, 11195, -10315, -652, 9846, -9321, 1395, 7030, -10091, 4757, 5930, -12068, 6222, 6222, -12068, 5930, 4757, -10091, 7030, 1395, -9321, 9846, -652, -10315, 11195, -600, -9950, 10083, -1510, -7029, 9541, -4845, -4521, 11368, -7786, -4623, 13052, -7762, -5276, 11686, -6131, -3439, 7616, -5474, 1934, -261]
def vnu_24 : List Int := [1136, -4304, 6639, -2776, -6523, 11363, -3769, -9517, 12897, -1926, -10427, 10794, -1068, -7553, 8838, -3825, -4313, 10281, -7228, -4370, 12614, -7362, -5636, 11773, -5945, -3964, 9161, -7187, -469, 9038, -10248, 557, 10830, -10830, -557, 10248, -9038, 469, 7187, -9161, 3964, 5945, -11773, 5636, 7362, -12614, 4370, 7228, -10281, 4313, 3825, -8838, 7553, 1068, -10794, 10427, 1926, -12897, 9517, 3769, -11363, 6523, 2776, -6639, 4304, -1136]
def vnu_25 : List Int := [-338, 2163, -5481, 6482, -937, -7965, 9708, 491, -11921, 9640, 4909, -13809, 5972, 8363, -11990, 2356, 8345, -9599, 1802, 7484, -9936, 2132, 9233, -11180, -218, 12079, -9680, -4018, 12292, -6373, -5493, 10525, -5038, -5038, 10525, -5493, -6373, 12292, -4018, -9680, 12079, -218, -11180, 9233, 2132, -9936, 7484, 1802, -9599, 8345, 2356, -11990, 8363, 5972, -13809, 4909, 9640, -11921, 491, 9708, -7965, -937, 6482, -5481, 2163, -338]
def vnu_26 : List Int := [1094, -3859, 5141, -372, -7708, 8700, 1848, -12397, 8110, 7353, -14142, 3094, 11257, -11053, -1566, 10466, -7379, -2006, 8602, -7439, -1260, 10229, -8679, -4055, 13193, -6232, -8598, 12492, -1519, -9789, 9160, 330, -8296, 8296, -330, -9160, 9789, 1519, -12492, 8598, 6232, -13193, 4055, 8679, -10229, 1260, 7439, -8602, 2006, 7379, -10466, 1566, 11053, -11257, -3094, 14142, -7353, -8110, 12397, -1848, -8700, 7708, 372, -5141, 3859, -1094]
def vnu_27 : List Int := [-417, 2342, -5278, 5098, 1232, -8368, 6224, 5296, -11736, 2401, 11703, -10503, -5752, 14600, -3253, -12399, 10761, 4927, -12959, 4015, 8776, -9838, -459, 9573, -7595, -3418, 11137, -5352, -8279, 12107, 484, -13273, 8203, 8203, -13273, 484, 12107, -8279, -5352, 11137, -3418, -7595, 9573, -459, -9838, 8776, 4015, -12959, 4927, 10761, -12399, -3253, 14600, -5752, -10503, 11703, 2401, -11736, 5296, 6224, -8368, 1231, 5098, -5278, 2342, -417]
def vnu_28 : List Int := [985, -3176, 3433, 1525, -7349, 4837, 5870, -10833, 643, 12397, -8839, -8141, 14415, -152, -14391, 8520, 8633, -12891, 65, 11169, -7402, -4318, 9752, -4119, -6005, 9808, -1871, -9815, 9820, 4094, -13758, 4497, 11641, -11641, -4497, 13758, -4094, -9820, 9815, 1871, -9808, 6004, 4119, -9752, 4318, 7402, -11169, -65, 12891, -8633, -8520, 14391, 152, -14415, 8141, 8839, -12398, -643, 10833, -5870, -4837, 7349, -1525, -3433, 3176, -985]
def vnu_29 : List Int := [493, -2447, 4844, -3579, -2791, 7402, -2323, -7647, 7867, 4374, -11744, 1343, 12587, -7797, -9980, 13101, 4515, -15709, 2400, 14827, -8934, -10626, 13349, 4196, -14474, 2758, 12029, -8380, -6704, 11172, -26, -10402, 6307, 6307, -10402, -27, 11172, -6704, -8380, 12029, 2758, -14474, 4196, 13349, -10626, -8934, 14827, 2400, -15709, 4515, 13101, -9980, -7797, 12587, 1343, -11744, 4374, 7867, -7647, -2323, 7402, -2791, -3579, 4844, -2447, 493]
def vnu_30 : List Int := [-813, 2321, -1746, -2643, 5731, -1062, -7110, 6230, 5120, -10619, -323, 12574, -5879, -11277, 11701, 6891, -15470, -465, 16079, -6364, -13283, 11831, 7762, -14519, -936, 13746, -5416, -9753, 9634, 3639, -10626, 2928, 8160, -8160, -2928, 10626, -3639, -9634, 9753, 5416, -13746, 935, 14519, -7762, -11831, 13283, 6364, -16079, 465, 15470, -6891, -11701, 11277, 5879, -12574, 323, 10619, -5120, -6230, 7110, 1062, -5731, 2643, 1746, -2321, 813]
def vnu_31 : List Int := [596, -1398, 301, 2920, -3475, -1549, 5743, -1284, -6560, 4647, 5883, -7879, -3874, 10488, 813, -12118, 2938, 12544, -6970, -11679, 10859, 9569, -14207, -6380, 16669, 2384, -17993, 2071, 18031, -6592, -16758, 10781, 14271, -14271, -10782, 16757, 6592, -18030, -2071, 17993, -2383, -16669, 6379, 14207, -9568, -10860, 11679, 6970, -12544, -2938, 12118, -813, -10488, 3874, 7879, -5883, -4647, 6560, 1284, -5743, 1549, 3475, -2920, -301, 1398, -596]
def vnu_32 : List Int := [-564, 2454, -4170, 2056, 3554, -5404, -873, 7103, -2635, -7160, 6218, 5736, -9336, -3091, 11587, -436, -12696, 4447, 12517, -8519, -11036, 12234, 8367, -15217, -4738, 17166, 464, -17880, 4078, 17273, -8484, -15383, 12366, 12366, -15383, -8484, 17273, 4078, -17880, 463, 17166, -4737, -15217, 8367, 12234, -11036, -8519, 12517, 4448, -12696, -436, 11587, -3091, -9336, 5736, 6218, -7160, -2635, 7103, -873, -5404, 3554, 2056, -4170, 2454, -564]
def cert_vnu : List (List Int) := [vnu_0, vnu_1, vnu_2, vnu_3, vnu_4, vnu_5, vnu_6, vnu_7, vnu_8, vnu_9, vnu_10, vnu_11, vnu_12, vnu_13, vnu_14, vnu_15, vnu_16, vnu_17, vnu_18, vnu_19, vnu_20, vnu_21, vnu_22, vnu_23, vnu_24, vnu_25, vnu_26, vnu_27, vnu_28, vnu_29, vnu_30, vnu_31, vnu_32]
def vg_0 : List Int := [-375, -562, -101, 446, 249, -342, -317, 266, 357, -198, -380, 140, 394, -86, -401, 38, 403, 9, -400, -51, 393, 92, -383, -130, 369, 166, -352, -199, 333, 231, -311, -260, 287, 287, -260, -311, 231, 333, -199, -352, 166, 369, -130, -383, 92, 393, -51, -400, 9, 403, 38, -401, -86, 394, 140, -380, -198, 357, 266, -317, -342, 249, 446, -101, -562, -375]
def vg_1 : List Int := [179, 524, 492, -103, -505, -101, 457, 228, -396, -315, 330, 378, -262, -424, 194, 456, -127, -477, 60, 488, 6, -489, -70, 482, 131, -468, -190, 446, 244, -417, -295, 382, 341, -341, -382, 295, 417, -244, -446, 190, 468, -131, -482, 70, 489, -6, -488, -60, 477, 127, -456, -194, 424, 262, -378, -330, 315, 396, -228, -457, 101, 505, 103, -492, -524, -179]
def vg_2 : List Int := [-357, -604, -201, 493, 502, -250, -629, 5, 660, 244, -599, -459, 468, 632, -278, -739, 55, 778, 183, -739, -409, 633, 606, -463, -750, 250, 832, -9, -841, -234, 778, 460, -646, -646, 460, 778, -234, -841, -9, 832, 250, -750, -463, 606, 633, -409, -739, 183, 778, 55, -739, -278, 632, 468, -459, -599, 244, 660, 5, -629, -250, 502, 493, -201, -604, -357]
def vg_3 : List Int := [175, 555, 621, 23, -612, -379, 446, 609, -200, -722, -78, 724, 353, -622, -588, 434, 757, -184, -837, -96, 820, 373, -707, -612, 510, 787, -253, -876, -35, 868, 322, -763, -574, 574, 763, -322, -868, 35, 876, 253, -787, -510, 612, 707, -373, -820, 96, 837, 184, -757, -434, 588, 622, -353, -724, 78, 722, 200, -609, -446, 379, 612, -23, -621, -555, -175]
def vg_4 : List Int := [-358, -664, -316, 502, 756, -22, -827, -455, 633, 832, -223, -982, -267, 880, 714, -540, -989, 60, 1022, 444, -798, -833, 378, 1012, 134, -929, -601, 611, 907, -135, -968, -368, 773, 773, -368, -968, -135, 907, 611, -601, -929, 134, 1012, 378, -833, -798, 444, 1022, 60, -989, -540, 714, 880, -267, -982, -223, 832, 633, -455, -827, -22, 756, 502, -316, -664, -358]
def vg_5 : List Int := [178, 602, 770, 195, -661, -707, 236, 916, 306, -795, -775, 399, 1023, 143, -969, -663, 628, 1000, -98, -1049, -461, 794, 883, -310, -1041, -258, 889, 743, -473, -998, -82, 948, 609, -609, -948, 82, 998, 473, -743, -889, 258, 1041, 310, -883, -794, 461, 1049, 98, -1000, -628, 663, 969, -143, -1023, -399, 775, 795, -306, -916, -236, 707, 661, -195, -770, -602, -178]
def vg_6 : List Int := [-364, -729, -455, 453, 988, 342, -814, -973, 172, 1152, 625, -747, -1139, -22, 1120, 788, -559, -1157, -257, 956, 932, -276, -1121, -532, 740, 1072, 26, -1066, -786, 522, 1165, 293, -965, -965, 293, 1165, 522, -786, -1066, 26, 1072, 740, -532, -1121, -276, 932, 956, -257, -1157, -559, 788, 1120, -22, -1139, -747, 625, 1152, 172, -973, -814, 342, 988, 453, -455, -729, -364]
def vg_7 : List Int := [179, 641, 921, 423, -602, -1020, -193, 956, 944, -300, -1201, -563, 811, 1149, 18, -1123, -831, 498, 1184, 387, -880, -1043, 91, 1111, 747, -553, -1169, -319, 941, 1023, -189, -1168, -673, 673, 1168, 189, -1023, -941, 319, 1169, 553, -747, -1111, -91, 1043, 880, -387, -1184, -498, 831, 1123, -18, -1149, -811, 563, 1201, 300, -944, -956, 193, 1020, 602, -423, -921, -641, -179]
def vg_8 : List Int := [-370, -795, -612, 336, 1153, 793, -522, -1315, -600, 838, 1328, 311, -1032, -1194, -41, 1129, 1056, -156, -1193, -932, 359, 1274, 786, -586, -1315, -572, 811, 1285, 333, -974, -1194, -104, 1093, 1093, -104, -1194, -974, 333, 1285, 811, -572, -1315, -586, 786, 1274, 359, -932, -1193, -156, 1056, 1129, -41, -1194, -1032, 311, 1328, 838, -600, -1315, -522, 793, 1153, 336, -612, -795, -370]
def vg_9 : List Int := [178, 670, 1064, 696, -411, -1224, -762, 596, 1355, 616, -816, -1343, -402, 952, 1261, 230, -1026, -1189, -96, 1105, 1136, -51, -1198, -1060, 226, 1271, 943, -398, -1304, -808, 546, 1310, 676, -676, -1310, -546, 808, 1304, 398, -943, -1271, -226, 1060, 1198, 51, -1136, -1105, 96, 1189, 1026, -230, -1261, -952, 402, 1343, 816, -616, -1355, -596, 762, 1224, 411, -696, -1064, -670, -178]
def vg_10 : List Int := [-375, -858, -783, 150, 1210, 1242, 32, -1264, -1325, -91, 1202, 1338, 250, -1028, -1358, -455, 877, 1425, 649, -751, -1454, -782, 622, 1432, 907, -443, -1373, -1040, 253, 1326, 1176, -77, -1267, -1267, -77, 1176, 1326, 253, -1040, -1373, -443, 907, 1432, 622, -782, -1454, -751, 649, 1425, 877, -455, -1358, -1028, 250, 1338, 1202, -91, -1325, -1264, 32, 1242, 1210, 150, -783, -858, -375]
def vg_11 : List Int := [173, 683, 1185, 992, -83, -1226, -1303, -132, 1197, 1407, 320, -1025, -1421, -557, 785, 1433, 814, -543, -1429, -1026, 315, 1371, 1182, -70, -1247, -1302, -196, 1083, 1398, 459, -900, -1455, -695, 695, 1455, 900, -459, -1398, -1083, 196, 1302, 1247, 70, -1182, -1371, -315, 1026, 1429, 543, -814, -1433, -785, 557, 1421, 1025, -320, -1407, -1197, 132, 1303, 1226, 83, -992, -1185, -683, -173]
def vg_12 : List Int := [-383, -925, -970, -101, 1137, 1602, 742, -742, -1590, -1156, 134, 1279, 1468, 579, -761, -1550, -1146, 168, 1354, 1481, 475, -869, -1544, -1055, 237, 1367, 1460, 422, -945, -1573, -988, 342, 1402, 1402, 342, -988, -1573, -945, 422, 1460, 1367, 237, -1055, -1544, -869, 475, 1481, 1354, 168, -1146, -1550, -761, 579, 1468, 1279, 134, -1156, -1590, -742, 742, 1602, 1137, -101, -970, -925, -383]
def vg_13 : List Int := [167, 684, 1280, 1290, 359, -973, -1621, -999, 398, 1462, 1416, 353, -944, -1560, -1047, 250, 1384, 1490, 480, -880, -1576, -1110, 163, 1315, 1509, 591, -773, -1569, -1198, 60, 1267, 1534, 676, -676, -1534, -1267, -60, 1198, 1569, 773, -591, -1509, -1315, -163, 1110, 1576, 880, -480, -1490, -1384, -250, 1047, 1560, 944, -353, -1416, -1462, -398, 999, 1621, 973, -359, -1290, -1280, -684, -167]
def vg_14 : List Int := [-393, -994, -1168, -413, 913, 1775, 1437, 160, -1140, -1669, -1208, -51, 1164, 1711, 1198, -83, -1304, -1690, -1039, 224, 1351, 1674, 975, -341, -1452, -1651, -829, 487, 1498, 1605, 739, -593, -1570, -1570, -593, 739, 1605, 1498, 487, -829, -1651, -1452, -341, 975, 1674, 1351, 224, -1039, -1690, -1304, -83, 1198, 1711, 1164, -51, -1208, -1669, -1140, 160, 1437, 1775, 913, -413, -1168, -994, -393]
def vg_15 : List Int := [158, 674, 1347, 1568, 876, -461, -1558, -1665, -753, 566, 1522, 1605, 768, -538, -1547, -1631, -733, 591, 1551, 1599, 718, -589, -1559, -1609, -699, 626, 1572, 1588, 675, -633, -1574, -1590, -662, 662, 1590, 1574, 633, -675, -1588, -1572, -626, 699, 1609, 1559, 589, -718, -1599, -1551, -591, 733, 1631, 1547, 538, -768, -1605, -1522, -566, 753, 1665, 1558, 461, -876, -1568, -1347, -674, -158]
def vg_16 : List Int := [-402, -1058, -1366, -771, 536, 1681, 1903, 1160, -54, -1169, -1765, -1567, -594, 713, 1667, 1792, 1074, -121, -1259, -1823, -1517, -460, 821, 1690, 1751, 998, -223, -1353, -1844, -1440, -337, 913, 1719, 1719, 913, -337, -1440, -1844, -1353, -223, 998, 1751, 1690, 821, -460, -1517, -1823, -1259, -121, 1074, 1792, 1667, 713, -594, -1567, -1765, -1169, -54, 1160, 1903, 1681, 536, -771, -1366, -1058, -402]
def vg_17 : List Int := [148, 648, 1371, 1790, 1404, 260, -1033, -1789, -1693, -858, 343, 1411, 1859, 1444, 350, -893, -1710, -1751, -1006, 203, 1332, 1851, 1514, 485, -756, -1649, -1797, -1126, 68, 1234, 1829, 1585, 621, -621, -1585, -1829, -1234, -68, 1126, 1797, 1649, 756, -485, -1514, -1851, -1332, -203, 1006, 1751, 1710, 893, -350, -1444, -1859, -1411, -343, 858, 1693, 1789, 1033, -260, -1404, -1790, -1371, -648, -148]
def vg_18 : List Int := [-413, -1124, -1566, -1158, 30, 1299, 1973, 1886, 1221, 197, -940, -1794, -1978, -1408, -352, 792, 1667, 1988, 1602, 618, -583, -1548, -1960, -1697, -835, 345, 1412, 1960, 1806, 1029, -102, -1210, -1898, -1898, -1210, -102, 1029, 1806, 1960, 1412, 345, -835, -1697, -1960, -1548, -583, 618, 1602, 1988, 1667, 792, -352, -1408, -1978, -1794, -940, 197, 1221, 1886, 1973, 1299, 30, -1158, -1566, -1124, -413]
def vg_19 : List Int := [134, 606, 1345, 1925, 1867, 1070, -117, -1205, -1853, -1904, -1332, -286, 879, 1735, 1986, 1572, 642, -511, -1504, -1983, -1777, -969, 158, 1231, 1897, 1920, 1285, 212, -926, -1747, -1981, -1547, -583, 583, 1547, 1981, 1747, 926, -212, -1285, -1920, -1897, -1231, -158, 969, 1777, 1983, 1504, 511, -642, -1572, -1986, -1735, -879, 286, 1332, 1904, 1853, 1205, 117, -1070, -1867, -1925, -1345, -606, -134]
def vg_20 : List Int := [-427, -1196, -1769, -1564, -571, 653, 1566, 2024, 2076, 1689, 831, -288, -1299, -1930, -2096, -1778, -1002, 64, 1110, 1849, 2128, 1907, 1213, 194, -878, -1706, -2100, -1988, -1386, -420, 664, 1567, 2068, 2068, 1567, 664, -420, -1386, -1988, -2100, -1706, -878, 194, 1213, 1907, 2128, 1849, 1110, 64, -1002, -1778, -2096, -1930, -1299, -288, 831, 1689, 2076, 2024, 1566, 653, -571, -1564, -1769, -1196, -427]
def vg_21 : List Int := [119, 551, 1274, 1960, 2196, 1819, 985, -30, -1009, -1775, -2139, -1976, -1322, -364, 665, 1545, 2072, 2103, 1623, 760, -272, -1240, -1922, -2147, -1853, -1118, -124, 898, 1713, 2123, 2024, 1441, 520, -520, -1441, -2024, -2123, -1713, -898, 124, 1118, 1853, 2147, 1922, 1240, 272, -760, -1623, -2103, -2072, -1545, -665, 364, 1322, 1976, 2139, 1775, 1009, 30, -985, -1819, -2196, -1960, -1274, -551, -119]
def vg_22 : List Int := [-444, -1268, -1966, -1963, -1217, -187, 707, 1421, 2014, 2363, 2274, 1760, 1000, 137, -768, -1591, -2142, -2303, -2096, -1582, -809, 128, 1047, 1772, 2207, 2309, 2045, 1431, 577, -351, -1209, -1887, -2271, -2271, -1887, -1209, -351, 577, 1431, 2045, 2309, 2207, 1772, 1047, 128, -809, -1582, -2096, -2303, -2142, -1591, -768, 137, 1000, 1760, 2274, 2363, 2014, 1421, 707, -187, -1217, -1963, -1966, -1268, -444]
def vg_23 : List Int := [102, 479, 1144, 1864, 2315, 2335, 1976, 1360, 560, -347, -1218, -1885, -2245, -2269, -1958, -1338, -502, 409, 1248, 1898, 2266, 2286, 1949, 1313, 483, -421, -1265, -1916, -2268, -2270, -1928, -1293, -455, 455, 1293, 1928, 2270, 2268, 1916, 1265, 421, -483, -1313, -1949, -2286, -2266, -1898, -1248, -409, 502, 1338, 1958, 2269, 2245, 1885, 1218, 347, -560, -1360, -1976, -2335, -2315, -1864, -1144, -479, -102]
def vg_24 : List Int := [466, 1350, 2163, 2344, 1850, 1103, 439, -196, -933, -1670, -2190, -2446, -2520, -2424, -2080, -1498, -793, -62, 682, 1399, 1983, 2349, 2496, 2438, 2160, 1655, 989, 253, -498, -1224, -1850, -2289, -2503, -2503, -2289, -1850, -1224, -498, 253, 989, 1655, 2160, 2438, 2496, 2349, 1983, 1399, 682, -62, -793, -1498, -2080, -2424, -2520, -2446, -2190, -1670, -933, -196, 439, 1103, 1850, 2344, 2163, 1350, 466]
def vg_25 : List Int := [-81, -387, -951, -1619, -2165, -2463, -2532, -2417, -2112, -1607, -949, -222, 510, 1204, 1803, 2238, 2469, 2487, 2295, 1901, 1334, 650, -84, -812, -1475, -2010, -2366, -2515, -2449, -2172, -1702, -1082, -370, 370, 1082, 1702, 2172, 2449, 2515, 2366, 2010, 1475, 812, 84, -650, -1334, -1901, -2295, -2487, -2469, -2238, -1803, -1204, -510, 222, 949, 1607, 2112, 2417, 2532, 2463, 2165, 1619, 951, 387, 81]
def vg_26 : List Int := [500, 1461, 2388, 2721, 2437, 1975, 1641, 1315, 800, 160, -414, -903, -1402, -1911, -2313, -2566, -2731, -2832, -2807, -2625, -2338, -1991, -1564, -1041, -471, 89, 638, 1183, 1689, 2101, 2413, 2642, 2776, 2776, 2642, 2413, 2101, 1689, 1183, 638, 89, -471, -1041, -1564, -1991, -2338, -2625, -2807, -2832, -2731, -2566, -2313, -1911, -1402, -903, -414, 160, 800, 1315, 1641, 1975, 2437, 2721, 2388, 1461, 500]
def vg_27 : List Int := [-57, -277, -693, -1220, -1719, -2112, -2413, -2644, -2788, -2812, -2718, -2526, -2246, -1874, -1422, -919, -387, 161, 708, 1224, 1688, 2085, 2403, 2627, 2744, 2752, 2655, 2454, 2154, 1769, 1315, 812, 275, -275, -812, -1315, -1769, -2154, -2454, -2655, -2752, -2744, -2627, -2403, -2085, -1688, -1224, -708, -161, 387, 919, 1422, 1874, 2246, 2526, 2718, 2812, 2788, 2644, 2413, 2112, 1719, 1220, 693, 277, 57]
def vg_28 : List Int := [564, 1651, 2717, 3164, 3003, 2739, 2699, 2717, 2551, 2255, 2024, 1851, 1602, 1258, 937, 666, 366, 6, -344, -643, -940, -1270, -1589, -1855, -2097, -2350, -2587, -2769, -2911, -3048, -3168, -3233, -3247, -3247, -3233, -3168, -3048, -2911, -2769, -2587, -2350, -2097, -1855, -1589, -1270, -940, -643, -344, 6, 366, 666, 937, 1258, 1602, 1851, 2024, 2255, 2551, 2717, 2699, 2739, 3003, 3164, 2717, 1651, 564]
def vg_29 : List Int := [-29, -141, -361, -654, -960, -1242, -1508, -1772, -2028, -2259, -2465, -2650, -2813, -2948, -3049, -3122, -3167, -3179, -3157, -3104, -3022, -2909, -2765, -2593, -2397, -2176, -1932, -1669, -1389, -1096, -791, -477, -159, 159, 477, 791, 1096, 1389, 1669, 1932, 2176, 2397, 2593, 2765, 2909, 3022, 3104, 3157, 3179, 3167, 3122, 3049, 2948, 2813, 2650, 2465, 2259, 2028, 1772, 1508, 1242, 960, 654, 361, 141, 29]
def vg_30 : List Int := [619, 1798, 2927, 3371, 3185, 2955, 3031, 3200, 3190, 3073, 3064, 3147, 3162, 3094, 3070, 3116, 3136, 3094, 3067, 3094, 3116, 3089, 3064, 3079, 3100, 3084, 3060, 3069, 3090, 3082, 3060, 3062, 3084, 3084, 3062, 3060, 3082, 3090, 3069, 3060, 3084, 3100, 3079, 3064, 3089, 3116, 3094, 3067, 3094, 3136, 3116, 3070, 3094, 3162, 3147, 3064, 3073, 3190, 3200, 3031, 2955, 3185, 3371, 2927, 1798, 619]
def cert_vg : List (List Int) := [vg_0, vg_1, vg_2, vg_3, vg_4, vg_5, vg_6, vg_7, vg_8, vg_9, vg_10, vg_11, vg_12, vg_13, vg_14, vg_15, vg_16, vg_17, vg_18, vg_19, vg_20, vg_21, vg_22, vg_23, vg_24, vg_25, vg_26, vg_27, vg_28, vg_29, vg_30]

def certAlphas : List Int := [2158529329721600, -1005009128683520, -3390414316820480, 8979832196509440, -6490022630698880, -4916395550883840, 11713654299526400, -9340241616411520, 3205041832042240, 175441883439360, -919483535377920, 401904072716800, 2055549318519680, -7931034872739200, 11347522114870400, -7768697050548480, -659269261393920, 5528052893638400, -3694610483941760, -368836454730240, 1125181094753280, 129798554500480, 776879743318400, -4251924274337920, 5861688180555520, -2923834193876480, -4088961854750720, 8182620243968000, -4169143006976000, -6493064588808320, 14696059777552640, -12084118987621760, 1074002209859840, 7491452656830720, -6667810372280320, 350491212332800, 2981146911283200, -616123767709440, -4229358058548480, 7680005289262080, -7882154360627200, 5312234829048320, -206307296229120, -5042854970012800, 6952134337392640, -4321911280788480, -268139512764800, 3229494524270080, -3650643107198720, 2877856735771520, -1726706847135360, -457603818321920, 2846294609228800, -3238726305994880, 495326212108800, 2714967973113600, -3655700655660800, 1848431570821760, -47076872783360, -399844512071680, -219748320366080, 372662012723840, 91228118997120, -370459582601600, 280509359040000, -100000000000000]
def certNumConst : Int := 25958391060532052419311360

def sfFn (r : Nat) : Int := (if Nat.ble r 32 then (if Nat.ble r 16 then (if Nat.ble r 8 then (if Nat.ble r 4 then (if Nat.ble r 2 then (if Nat.ble r 1 then (if Nat.ble r 0 then (57095329284 : Int) else (-86844970260 : Int)) else (30340289470 : Int)) else (if Nat.ble r 3 then (8357007586 : Int) else (-11219238610 : Int))) else (if Nat.ble r 6 then (if Nat.ble r 5 then (-1471789274 : Int) else (5528291482 : Int)) else (if Nat.ble r 7 then (112687856 : Int) else (-3238302074 : Int)))) else (if Nat.ble r 12 then (if Nat.ble r 10 then (if Nat.ble r 9 then (284529784 : Int) else (2070395604 : Int)) else (if Nat.ble r 11 then (-378866244 : Int) else (-1428848438 : Int))) else (if Nat.ble r 14 then (if Nat.ble r 13 then (404850182 : Int) else (1022649148 : Int)) else (if Nat.ble r 15 then (-389775084 : Int) else (-762704404 : Int))))) else (if Nat.ble r 24 then (if Nat.ble r 20 then (if Nat.ble r 18 then (if Nat.ble r 17 then (372699704 : Int) else (576895392 : Int)) else (if Nat.ble r 19 then (-347067670 : Int) else (-447796808 : Int))) else (if Nat.ble r 22 then (if Nat.ble r 21 then (327773718 : Int) else (346664824 : Int)) else (if Nat.ble r 23 then (-305775520 : Int) else (-271465954 : Int)))) else (if Nat.ble r 28 then (if Nat.ble r 26 then (if Nat.ble r 25 then (288589430 : Int) else (209096052 : Int)) else (if Nat.ble r 27 then (-270521420 : Int) else (-160154790 : Int))) else (if Nat.ble r 30 then (if Nat.ble r 29 then (256109508 : Int) else (117108710 : Int)) else (if Nat.ble r 31 then (-241329224 : Int) else (-80170010 : Int)))))) else (if Nat.ble r 49 then (if Nat.ble r 41 then (if Nat.ble r 37 then (if Nat.ble r 35 then (if Nat.ble r 34 then (if Nat.ble r 33 then (226670496 : Int) else (47985396 : Int)) else (-212159220 : Int)) else (if Nat.ble r 36 then (-19403332 : Int) else (197883696 : Int))) else (if Nat.ble r 39 then (if Nat.ble r 38 then (-7342354 : Int) else (-182147478 : Int)) else (if Nat.ble r 40 then (31579850 : Int) else (165460850 : Int)))) else (if Nat.ble r 45 then (if Nat.ble r 43 then (if Nat.ble r 42 then (-54699908 : Int) else (-145688464 : Int)) else (if Nat.ble r 44 then (74836802 : Int) else (123786352 : Int))) else (if Nat.ble r 47 then (if Nat.ble r 46 then (-92601788 : Int) else (-98622478 : Int)) else (if Nat.ble r 48 then (107040460 : Int) else (69366412 : Int))))) else (if Nat.ble r 57 then (if Nat.ble r 53 then (if Nat.ble r 51 then (if Nat.ble r 50 then (-116032566 : Int) else (-36373836 : Int)) else (if Nat.ble r 52 then (117509628 : Int) else (105948 : Int))) else (if Nat.ble r 55 then (if Nat.ble r 54 then (-107301950 : Int) else (35284272 : Int)) else (if Nat.ble r 56 then (83062890 : Int) else (-64313044 : Int)))) else (if Nat.ble r 61 then (if Nat.ble r 59 then (if Nat.ble r 58 then (-41390974 : Int) else (72567356 : Int)) else (if Nat.ble r 60 then (-9486084 : Int) else (-43512422 : Int))) else (if Nat.ble r 63 then (if Nat.ble r 62 then (37749530 : Int) else (-14225926 : Int)) else (if Nat.ble r 64 then (5967880 : Int) else (-3747636 : Int)))))))
def snuFn (r : Nat) : Int := (if Nat.ble r 32 then (if Nat.ble r 16 then (if Nat.ble r 8 then (if Nat.ble r 4 then (if Nat.ble r 2 then (if Nat.ble r 1 then (if Nat.ble r 0 then (110569552002 : Int) else (-133265327032 : Int)) else (-19514685858 : Int)) else (if Nat.ble r 3 then (64779816148 : Int) else (-1125716642 : Int))) else (if Nat.ble r 6 then (if Nat.ble r 5 then (-39808423104 : Int) else (6081951936 : Int)) else (if Nat.ble r 7 then (27094978556 : Int) else (-7342223704 : Int)))) else (if Nat.ble r 12 then (if Nat.ble r 10 then (if Nat.ble r 9 then (-19592031416 : Int) else (7525978468 : Int)) else (if Nat.ble r 11 then (14631789116 : Int) else (-7261535320 : Int))) else (if Nat.ble r 14 then (if Nat.ble r 13 then (-11165335868 : Int) else (6850233056 : Int)) else (if Nat.ble r 15 then (8596618370 : Int) else (-6360597324 : Int))))) else (if Nat.ble r 24 then (if Nat.ble r 20 then (if Nat.ble r 18 then (if Nat.ble r 17 then (-6646024026 : Int) else (5859543050 : Int)) else (if Nat.ble r 19 then (5112135192 : Int) else (-5351340796 : Int))) else (if Nat.ble r 22 then (if Nat.ble r 21 then (-3893681326 : Int) else (4856821572 : Int)) else (if Nat.ble r 23 then (2905184396 : Int) else (-4371581208 : Int)))) else (if Nat.ble r 28 then (if Nat.ble r 26 then (if Nat.ble r 25 then (-2102691218 : Int) else (3903868690 : Int)) else (if Nat.ble r 27 then (1444571974 : Int) else (-3449533590 : Int))) else (if Nat.ble r 30 then (if Nat.ble r 29 then (-909557886 : Int) else (3013398740 : Int)) else (if Nat.ble r 31 then (474480002 : Int) else (-2591783662 : Int)))))) else (if Nat.ble r 49 then (if Nat.ble r 41 then (if Nat.ble r 37 then (if Nat.ble r 35 then (if Nat.ble r 34 then (if Nat.ble r 33 then (-129311644 : Int) else (2189116786 : Int)) else (-139962922 : Int)) else (if Nat.ble r 36 then (-1803042324 : Int) else (337736250 : Int))) else (if Nat.ble r 39 then (if Nat.ble r 38 then (1438597674 : Int) else (-472701404 : Int)) else (if Nat.ble r 40 then (-1096371202 : Int) else (547819006 : Int)))) else (if Nat.ble r 45 then (if Nat.ble r 43 then (if Nat.ble r 42 then (782273396 : Int) else (-569712200 : Int)) else (if Nat.ble r 44 then (-499609178 : Int) else (542570440 : Int))) else (if Nat.ble r 47 then (if Nat.ble r 46 then (253916748 : Int) else (-471046722 : Int)) else (if Nat.ble r 48 then (-53191690 : Int) else (363270504 : Int))))) else (if Nat.ble r 57 then (if Nat.ble r 53 then (if Nat.ble r 51 then (if Nat.ble r 50 then (-94905866 : Int) else (-229925300 : Int)) else (if Nat.ble r 52 then (182721578 : Int) else (86492858 : Int))) else (if Nat.ble r 55 then (if Nat.ble r 54 then (-205047570 : Int) else (46423002 : Int)) else (if Nat.ble r 56 then (160746774 : Int) else (-138073020 : Int)))) else (if Nat.ble r 61 then (if Nat.ble r 59 then (if Nat.ble r 58 then (-66309692 : Int) else (159072342 : Int)) else (if Nat.ble r 60 then (-40818654 : Int) else (-88549744 : Int))) else (if Nat.ble r 63 then (if Nat.ble r 62 then (79646284 : Int) else (-13132774 : Int)) else (if Nat.ble r 64 then (-7552836 : Int) else (10000 : Int)))))))
def sgFn (r : Nat) : Int := (if Nat.ble r 32 then (if Nat.ble r 16 then (if Nat.ble r 8 then (if Nat.ble r 4 then (if Nat.ble r 2 then (if Nat.ble r 1 then (if Nat.ble r 0 then (4005339560 : Int) else (6878353504 : Int)) else (4408222812 : Int)) else (if Nat.ble r 3 then (2353235246 : Int) else (1532014696 : Int))) else (if Nat.ble r 6 then (if Nat.ble r 5 then (1435578214 : Int) else (1305340928 : Int)) else (if Nat.ble r 7 then (1015079716 : Int) else (828146720 : Int)))) else (if Nat.ble r 12 then (if Nat.ble r 10 then (if Nat.ble r 9 then (801900300 : Int) else (764799888 : Int)) else (if Nat.ble r 11 then (655136374 : Int) else (573160956 : Int))) else (if Nat.ble r 14 then (if Nat.ble r 13 then (560425730 : Int) else (543953480 : Int)) else (if Nat.ble r 15 then (487462504 : Int) else (441413636 : Int))))) else (if Nat.ble r 24 then (if Nat.ble r 20 then (if Nat.ble r 18 then (if Nat.ble r 17 then (433442332 : Int) else (424520612 : Int)) else (if Nat.ble r 19 then (390727244 : Int) else (361146212 : Int))) else (if Nat.ble r 22 then (if Nat.ble r 21 then (355122834 : Int) else (349452816 : Int)) else (if Nat.ble r 23 then (327291146 : Int) else (306623968 : Int)))) else (if Nat.ble r 28 then (if Nat.ble r 26 then (if Nat.ble r 25 then (301574464 : Int) else (297613396 : Int)) else (if Nat.ble r 27 then (282343816 : Int) else (267168824 : Int))) else (if Nat.ble r 30 then (if Nat.ble r 29 then (262661112 : Int) else (259612852 : Int)) else (if Nat.ble r 31 then (248710820 : Int) else (237125244 : Int)))))) else (if Nat.ble r 49 then (if Nat.ble r 41 then (if Nat.ble r 37 then (if Nat.ble r 35 then (if Nat.ble r 34 then (if Nat.ble r 33 then (232881954 : Int) else (230349884 : Int)) else (222477736 : Int)) else (if Nat.ble r 36 then (213417408 : Int) else (209171544 : Int))) else (if Nat.ble r 39 then (if Nat.ble r 38 then (206734668 : Int) else (200978564 : Int)) else (if Nat.ble r 40 then (193824496 : Int) else (189483630 : Int)))) else (if Nat.ble r 45 then (if Nat.ble r 43 then (if Nat.ble r 42 then (186896900 : Int) else (182628754 : Int)) else (if Nat.ble r 44 then (176843420 : Int) else (172149854 : Int))) else (if Nat.ble r 47 then (if Nat.ble r 46 then (169285320 : Int) else (166677402 : Int)) else (if Nat.ble r 48 then (162745756 : Int) else (157713284 : Int))))) else (if Nat.ble r 57 then (if Nat.ble r 53 then (if Nat.ble r 51 then (if Nat.ble r 50 then (153628436 : Int) else (151706830 : Int)) else (if Nat.ble r 52 then (149605276 : Int) else (144398134 : Int))) else (if Nat.ble r 55 then (if Nat.ble r 54 then (138299264 : Int) else (136236932 : Int)) else (if Nat.ble r 56 then (136640664 : Int) else (132056400 : Int)))) else (if Nat.ble r 61 then (if Nat.ble r 59 then (if Nat.ble r 58 then (122035664 : Int) else (116764196 : Int)) else (if Nat.ble r 60 then (120889928 : Int) else (121365822 : Int))) else (if Nat.ble r 63 then (if Nat.ble r 62 then (101379776 : Int) else (62927838 : Int)) else (if Nat.ble r 64 then (25773944 : Int) else (5343030 : Int)))))))
def rFn (r : Nat) : Int := (if Nat.ble r 32 then (if Nat.ble r 16 then (if Nat.ble r 8 then (if Nat.ble r 4 then (if Nat.ble r 2 then (if Nat.ble r 1 then (if Nat.ble r 0 then (0 : Int) else (28686 : Int)) else (18384 : Int)) else (if Nat.ble r 3 then (9814 : Int) else (6389 : Int))) else (if Nat.ble r 6 then (if Nat.ble r 5 then (5987 : Int) else (5443 : Int)) else (if Nat.ble r 7 then (4233 : Int) else (3453 : Int)))) else (if Nat.ble r 12 then (if Nat.ble r 10 then (if Nat.ble r 9 then (3343 : Int) else (3189 : Int)) else (if Nat.ble r 11 then (2732 : Int) else (2390 : Int))) else (if Nat.ble r 14 then (if Nat.ble r 13 then (2337 : Int) else (2269 : Int)) else (if Nat.ble r 15 then (2033 : Int) else (1841 : Int))))) else (if Nat.ble r 24 then (if Nat.ble r 20 then (if Nat.ble r 18 then (if Nat.ble r 17 then (1808 : Int) else (1770 : Int)) else (if Nat.ble r 19 then (1629 : Int) else (1506 : Int))) else (if Nat.ble r 22 then (if Nat.ble r 21 then (1481 : Int) else (1457 : Int)) else (if Nat.ble r 23 then (1365 : Int) else (1279 : Int)))) else (if Nat.ble r 28 then (if Nat.ble r 26 then (if Nat.ble r 25 then (1258 : Int) else (1242 : Int)) else (if Nat.ble r 27 then (1178 : Int) else (1115 : Int))) else (if Nat.ble r 30 then (if Nat.ble r 29 then (1096 : Int) else (1083 : Int)) else (if Nat.ble r 31 then (1038 : Int) else (989 : Int)))))) else (if Nat.ble r 49 then (if Nat.ble r 41 then (if Nat.ble r 37 then (if Nat.ble r 35 then (if Nat.ble r 34 then (if Nat.ble r 33 then (971 : Int) else (961 : Int)) else (928 : Int)) else (if Nat.ble r 36 then (890 : Int) else (872 : Int))) else (if Nat.ble r 39 then (if Nat.ble r 38 then (862 : Int) else (838 : Int)) else (if Nat.ble r 40 then (808 : Int) else (790 : Int)))) else (if Nat.ble r 45 then (if Nat.ble r 43 then (if Nat.ble r 42 then (779 : Int) else (761 : Int)) else (if Nat.ble r 44 then (741 : Int) else (718 : Int))) else (if Nat.ble r 47 then (if Nat.ble r 46 then (708 : Int) else (695 : Int)) else (if Nat.ble r 48 then (679 : Int) else (658 : Int))))) else (if Nat.ble r 57 then (if Nat.ble r 53 then (if Nat.ble r 51 then (if Nat.ble r 50 then (641 : Int) else (633 : Int)) else (if Nat.ble r 52 then (624 : Int) else (602 : Int))) else (if Nat.ble r 55 then (if Nat.ble r 54 then (577 : Int) else (568 : Int)) else (if Nat.ble r 56 then (570 : Int) else (551 : Int)))) else (if Nat.ble r 61 then (if Nat.ble r 59 then (if Nat.ble r 58 then (509 : Int) else (487 : Int)) else (if Nat.ble r 60 then (504 : Int) else (506 : Int))) else (if Nat.ble r 63 then (if Nat.ble r 62 then (423 : Int) else (431 : Int)) else (if Nat.ble r 64 then (107 : Int) else (276 : Int)))))))
def mFn (r : Nat) : Int := (if Nat.ble r 32 then (if Nat.ble r 16 then (if Nat.ble r 8 then (if Nat.ble r 4 then (if Nat.ble r 2 then (if Nat.ble r 1 then (if Nat.ble r 0 then (0 : Int) else (50765 : Int)) else (-22132 : Int)) else (if Nat.ble r 3 then (-20858 : Int) else (20674 : Int))) else (if Nat.ble r 6 then (if Nat.ble r 5 then (17519 : Int) else (-15872 : Int)) else (if Nat.ble r 7 then (-12730 : Int) else (15479 : Int)))) else (if Nat.ble r 12 then (if Nat.ble r 10 then (if Nat.ble r 9 then (11742 : Int) else (-13394 : Int)) else (if Nat.ble r 11 then (-9414 : Int) else (13278 : Int))) else (if Nat.ble r 14 then (if Nat.ble r 13 then (8891 : Int) else (-12045 : Int)) else (if Nat.ble r 15 then (-7405 : Int) else (12018 : Int))))) else (if Nat.ble r 24 then (if Nat.ble r 20 then (if Nat.ble r 18 then (if Nat.ble r 17 then (7044 : Int) else (-11177 : Int)) else (if Nat.ble r 19 then (-5961 : Int) else (11174 : Int))) else (if Nat.ble r 22 then (if Nat.ble r 21 then (5672 : Int) else (-10559 : Int)) else (if Nat.ble r 23 then (-4821 : Int) else (10563 : Int)))) else (if Nat.ble r 28 then (if Nat.ble r 26 then (if Nat.ble r 25 then (4561 : Int) else (-10086 : Int)) else (if Nat.ble r 27 then (-3856 : Int) else (10080 : Int))) else (if Nat.ble r 30 then (if Nat.ble r 29 then (3600 : Int) else (-9701 : Int)) else (if Nat.ble r 31 then (-2993 : Int) else (9679 : Int)))))) else (if Nat.ble r 49 then (if Nat.ble r 41 then (if Nat.ble r 37 then (if Nat.ble r 35 then (if Nat.ble r 34 then (if Nat.ble r 33 then (2726 : Int) else (-9362 : Int)) else (-2186 : Int)) else (if Nat.ble r 36 then (9313 : Int) else (1890 : Int))) else (if Nat.ble r 39 then (if Nat.ble r 38 then (-9053 : Int) else (-1399 : Int)) else (if Nat.ble r 40 then (8969 : Int) else (1058 : Int)))) else (if Nat.ble r 45 then (if Nat.ble r 43 then (if Nat.ble r 42 then (-8748 : Int) else (-598 : Int)) else (if Nat.ble r 44 then (8605 : Int) else (187 : Int))) else (if Nat.ble r 47 then (if Nat.ble r 46 then (-8414 : Int) else (259 : Int)) else (if Nat.ble r 48 then (8188 : Int) else (-771 : Int))))) else (if Nat.ble r 57 then (if Nat.ble r 53 then (if Nat.ble r 51 then (if Nat.ble r 50 then (-8007 : Int) else (1227 : Int)) else (if Nat.ble r 52 then (7648 : Int) else (-1890 : Int))) else (if Nat.ble r 55 then (if Nat.ble r 54 then (-7411 : Int) else (2415 : Int)) else (if Nat.ble r 56 then (6837 : Int) else (-3270 : Int)))) else (if Nat.ble r 61 then (if Nat.ble r 59 then (if Nat.ble r 58 then (-6309 : Int) else (4068 : Int)) else (if Nat.ble r 60 then (5327 : Int) else (-4967 : Int))) else (if Nat.ble r 63 then (if Nat.ble r 62 then (-3223 : Int) else (6563 : Int)) else (if Nat.ble r 64 then (-595 : Int) else (-5250 : Int)))))))
def alphaFn (r : Nat) : Int := (if Nat.ble r 33 then (if Nat.ble r 16 then (if Nat.ble r 8 then (if Nat.ble r 4 then (if Nat.ble r 2 then (if Nat.ble r 1 then (if Nat.ble r 0 then (0 : Int) else (2158529329721600 : Int)) else (-1005009128683520 : Int)) else (if Nat.ble r 3 then (-3390414316820480 : Int) else (8979832196509440 : Int))) else (if Nat.ble r 6 then (if Nat.ble r 5 then (-6490022630698880 : Int) else (-4916395550883840 : Int)) else (if Nat.ble r 7 then (11713654299526400 : Int) else (-9340241616411520 : Int)))) else (if Nat.ble r 12 then (if Nat.ble r 10 then (if Nat.ble r 9 then (3205041832042240 : Int) else (175441883439360 : Int)) else (if Nat.ble r 11 then (-919483535377920 : Int) else (401904072716800 : Int))) else (if Nat.ble r 14 then (if Nat.ble r 13 then (2055549318519680 : Int) else (-7931034872739200 : Int)) else (if Nat.ble r 15 then (11347522114870400 : Int) else (-7768697050548480 : Int))))) else (if Nat.ble r 25 then (if Nat.ble r 21 then (if Nat.ble r 19 then (if Nat.ble r 18 then (if Nat.ble r 17 then (-659269261393920 : Int) else (5528052893638400 : Int)) else (-3694610483941760 : Int)) else (if Nat.ble r 20 then (-368836454730240 : Int) else (1125181094753280 : Int))) else (if Nat.ble r 23 then (if Nat.ble r 22 then (129798554500480 : Int) else (776879743318400 : Int)) else (if Nat.ble r 24 then (-4251924274337920 : Int) else (5861688180555520 : Int)))) else (if Nat.ble r 29 then (if Nat.ble r 27 then (if Nat.ble r 26 then (-2923834193876480 : Int) else (-4088961854750720 : Int)) else (if Nat.ble r 28 then (8182620243968000 : Int) else (-4169143006976000 : Int))) else (if Nat.ble r 31 then (if Nat.ble r 30 then (-6493064588808320 : Int) else (14696059777552640 : Int)) else (if Nat.ble r 32 then (-12084118987621760 : Int) else (1074002209859840 : Int)))))) else (if Nat.ble r 50 then (if Nat.ble r 42 then (if Nat.ble r 38 then (if Nat.ble r 36 then (if Nat.ble r 35 then (if Nat.ble r 34 then (7491452656830720 : Int) else (-6667810372280320 : Int)) else (350491212332800 : Int)) else (if Nat.ble r 37 then (2981146911283200 : Int) else (-616123767709440 : Int))) else (if Nat.ble r 40 then (if Nat.ble r 39 then (-4229358058548480 : Int) else (7680005289262080 : Int)) else (if Nat.ble r 41 then (-7882154360627200 : Int) else (5312234829048320 : Int)))) else (if Nat.ble r 46 then (if Nat.ble r 44 then (if Nat.ble r 43 then (-206307296229120 : Int) else (-5042854970012800 : Int)) else (if Nat.ble r 45 then (6952134337392640 : Int) else (-4321911280788480 : Int))) else (if Nat.ble r 48 then (if Nat.ble r 47 then (-268139512764800 : Int) else (3229494524270080 : Int)) else (if Nat.ble r 49 then (-3650643107198720 : Int) else (2877856735771520 : Int))))) else (if Nat.ble r 58 then (if Nat.ble r 54 then (if Nat.ble r 52 then (if Nat.ble r 51 then (-1726706847135360 : Int) else (-457603818321920 : Int)) else (if Nat.ble r 53 then (2846294609228800 : Int) else (-3238726305994880 : Int))) else (if Nat.ble r 56 then (if Nat.ble r 55 then (495326212108800 : Int) else (2714967973113600 : Int)) else (if Nat.ble r 57 then (-3655700655660800 : Int) else (1848431570821760 : Int)))) else (if Nat.ble r 62 then (if Nat.ble r 60 then (if Nat.ble r 59 then (-47076872783360 : Int) else (-399844512071680 : Int)) else (if Nat.ble r 61 then (-219748320366080 : Int) else (372662012723840 : Int))) else (if Nat.ble r 64 then (if Nat.ble r 63 then (91228118997120 : Int) else (-370459582601600 : Int)) else (if Nat.ble r 65 then (280509359040000 : Int) else (-100000000000000 : Int)))))))
def cosLoFn (r : Nat) : Int := (if Nat.ble r 80 then (if Nat.ble r 40 then (if Nat.ble r 20 then (if Nat.ble r 10 then (if Nat.ble r 5 then (if Nat.ble r 2 then (if Nat.ble r 1 then (if Nat.ble r 0 then (10000000 : Int) else (9998072 : Int)) else (9992290 : Int)) else (if Nat.ble r 4 then (if Nat.ble r 3 then (9982656 : Int) else (9969173 : Int)) else (9951847 : Int))) else (if Nat.ble r 8 then (if Nat.ble r 7 then (if Nat.ble r 6 then (9930684 : Int) else (9905693 : Int)) else (9876883 : Int)) else (if Nat.ble r 9 then (9844265 : Int) else (9807852 : Int)))) else (if Nat.ble r 15 then (if Nat.ble r 13 then (if Nat.ble r 12 then (if Nat.ble r 11 then (9767658 : Int) else (9723699 : Int)) else (9675990 : Int)) else (if Nat.ble r 14 then (9624552 : Int) else (9569403 : Int))) else (if Nat.ble r 18 then (if Nat.ble r 17 then (if Nat.ble r 16 then (9510565 : Int) else (9448060 : Int)) else (9381913 : Int)) else (if Nat.ble r 19 then (9312149 : Int) else (9238795 : Int))))) else (if Nat.ble r 30 then (if Nat.ble r 25 then (if Nat.ble r 23 then (if Nat.ble r 22 then (if Nat.ble r 21 then (9161879 : Int) else (9081431 : Int)) else (8997482 : Int)) else (if Nat.ble r 24 then (8910064 : Int) else (8819211 : Int))) else (if Nat.ble r 28 then (if Nat.ble r 27 then (if Nat.ble r 26 then (8724958 : Int) else (8627342 : Int)) else (8526399 : Int)) else (if Nat.ble r 29 then (8422169 : Int) else (8314692 : Int)))) else (if Nat.ble r 35 then (if Nat.ble r 33 then (if Nat.ble r 32 then (if Nat.ble r 31 then (8204009 : Int) else (8090163 : Int)) else (7973198 : Int)) else (if Nat.ble r 34 then (7853159 : Int) else (7730092 : Int))) else (if Nat.ble r 38 then (if Nat.ble r 37 then (if Nat.ble r 36 then (7604044 : Int) else (7475064 : Int)) else (7343201 : Int)) else (if Nat.ble r 39 then (7208506 : Int) else (7071032 : Int)))))) else (if Nat.ble r 60 then (if Nat.ble r 50 then (if Nat.ble r 45 then (if Nat.ble r 43 then (if Nat.ble r 42 then (if Nat.ble r 41 then (6930871 : Int) else (6788005 : Int)) else (6642522 : Int)) else (if Nat.ble r 44 then (6494479 : Int) else (6343931 : Int))) else (if Nat.ble r 48 then (if Nat.ble r 47 then (if Nat.ble r 46 then (6190938 : Int) else (6035558 : Int)) else (5877852 : Int)) else (if Nat.ble r 49 then (5717879 : Int) else (5555702 : Int)))) else (if Nat.ble r 55 then (if Nat.ble r 53 then (if Nat.ble r 52 then (if Nat.ble r 51 then (5391383 : Int) else (5224985 : Int)) else (5056573 : Int)) else (if Nat.ble r 54 then (4886212 : Int) else (4713967 : Int))) else (if Nat.ble r 58 then (if Nat.ble r 57 then (if Nat.ble r 56 then (4539904 : Int) else (4364092 : Int)) else (4186597 : Int)) else (if Nat.ble r 59 then (4007488 : Int) else (3826834 : Int))))) else (if Nat.ble r 70 then (if Nat.ble r 65 then (if Nat.ble r 63 then (if Nat.ble r 62 then (if Nat.ble r 61 then (3644704 : Int) else (3461170 : Int)) else (3276301 : Int)) else (if Nat.ble r 64 then (3090169 : Int) else (2902846 : Int))) else (if Nat.ble r 68 then (if Nat.ble r 67 then (if Nat.ble r 66 then (2714404 : Int) else (2524915 : Int)) else (2334453 : Int)) else (if Nat.ble r 69 then (2143091 : Int) else (1950903 : Int)))) else (if Nat.ble r 75 then (if Nat.ble r 73 then (if Nat.ble r 72 then (if Nat.ble r 71 then (1757962 : Int) else (1564344 : Int)) else (1370123 : Int)) else (if Nat.ble r 74 then (1175373 : Int) else (980171 : Int))) else (if Nat.ble r 78 then (if Nat.ble r 77 then (if Nat.ble r 76 then (784590 : Int) else (588708 : Int)) else (392598 : Int)) else (if Nat.ble r 79 then (196336 : Int) else (0 : Int))))))) else (if Nat.ble r 120 then (if Nat.ble r 100 then (if Nat.ble r 90 then (if Nat.ble r 85 then (if Nat.ble r 83 then (if Nat.ble r 82 then (if Nat.ble r 81 then (-196337 : Int) else (-392599 : Int)) else (-588709 : Int)) else (if Nat.ble r 84 then (-784591 : Int) else (-980172 : Int))) else (if Nat.ble r 88 then (if Nat.ble r 87 then (if Nat.ble r 86 then (-1175374 : Int) else (-1370124 : Int)) else (-1564345 : Int)) else (if Nat.ble r 89 then (-1757963 : Int) else (-1950904 : Int)))) else (if Nat.ble r 95 then (if Nat.ble r 93 then (if Nat.ble r 92 then (if Nat.ble r 91 then (-2143092 : Int) else (-2334454 : Int)) else (-2524916 : Int)) else (if Nat.ble r 94 then (-2714405 : Int) else (-2902847 : Int))) else (if Nat.ble r 98 then (if Nat.ble r 97 then (if Nat.ble r 96 then (-3090170 : Int) else (-3276302 : Int)) else (-3461171 : Int)) else (if Nat.ble r 99 then (-3644706 : Int) else (-3826835 : Int))))) else (if Nat.ble r 110 then (if Nat.ble r 105 then (if Nat.ble r 103 then (if Nat.ble r 102 then (if Nat.ble r 101 then (-4007489 : Int) else (-4186598 : Int)) else (-4364093 : Int)) else (if Nat.ble r 104 then (-4539906 : Int) else (-4713968 : Int))) else (if Nat.ble r 108 then (if Nat.ble r 107 then (if Nat.ble r 106 then (-4886213 : Int) else (-5056574 : Int)) else (-5224986 : Int)) else (if Nat.ble r 109 then (-5391384 : Int) else (-5555703 : Int)))) else (if Nat.ble r 115 then (if Nat.ble r 113 then (if Nat.ble r 112 then (if Nat.ble r 111 then (-5717880 : Int) else (-5877853 : Int)) else (-6035560 : Int)) else (if Nat.ble r 114 then (-6190940 : Int) else (-6343933 : Int))) else (if Nat.ble r 118 then (if Nat.ble r 117 then (if Nat.ble r 116 then (-6494481 : Int) else (-6642525 : Int)) else (-6788008 : Int)) else (if Nat.ble r 119 then (-6930874 : Int) else (-7071069 : Int)))))) else (if Nat.ble r 140 then (if Nat.ble r 130 then (if Nat.ble r 125 then (if Nat.ble r 123 then (if Nat.ble r 122 then (if Nat.ble r 121 then (-7208537 : Int) else (-7343226 : Int)) else (-7475084 : Int)) else (if Nat.ble r 124 then (-7604060 : Int) else (-7730105 : Int))) else (if Nat.ble r 128 then (if Nat.ble r 127 then (if Nat.ble r 126 then (-7853170 : Int) else (-7973207 : Int)) else (-8090170 : Int)) else (if Nat.ble r 129 then (-8204015 : Int) else (-8314697 : Int)))) else (if Nat.ble r 135 then (if Nat.ble r 133 then (if Nat.ble r 132 then (if Nat.ble r 131 then (-8422173 : Int) else (-8526402 : Int)) else (-8627344 : Int)) else (if Nat.ble r 134 then (-8724961 : Int) else (-8819213 : Int))) else (if Nat.ble r 138 then (if Nat.ble r 137 then (if Nat.ble r 136 then (-8910066 : Int) else (-8997483 : Int)) else (-9081432 : Int)) else (if Nat.ble r 139 then (-9161880 : Int) else (-9238796 : Int))))) else (if Nat.ble r 150 then (if Nat.ble r 145 then (if Nat.ble r 143 then (if Nat.ble r 142 then (if Nat.ble r 141 then (-9312150 : Int) else (-9381914 : Int)) else (-9448061 : Int)) else (if Nat.ble r 144 then (-9510566 : Int) else (-9569404 : Int))) else (if Nat.ble r 148 then (if Nat.ble r 147 then (if Nat.ble r 146 then (-9624553 : Int) else (-9675991 : Int)) else (-9723700 : Int)) else (if Nat.ble r 149 then (-9767659 : Int) else (-9807853 : Int)))) else (if Nat.ble r 155 then (if Nat.ble r 153 then (if Nat.ble r 152 then (if Nat.ble r 151 then (-9844266 : Int) else (-9876884 : Int)) else (-9905694 : Int)) else (if Nat.ble r 154 then (-9930685 : Int) else (-9951848 : Int))) else (if Nat.ble r 158 then (if Nat.ble r 157 then (if Nat.ble r 156 then (-9969174 : Int) else (-9982657 : Int)) else (-9992291 : Int)) else (if Nat.ble r 159 then (-9998073 : Int) else (-10000000 : Int))))))))
def cosHiFn (r : Nat) : Int := (if Nat.ble r 80 then (if Nat.ble r 40 then (if Nat.ble r 20 then (if Nat.ble r 10 then (if Nat.ble r 5 then (if Nat.ble r 2 then (if Nat.ble r 1 then (if Nat.ble r 0 then (10000000 : Int) else (9998073 : Int)) else (9992291 : Int)) else (if Nat.ble r 4 then (if Nat.ble r 3 then (9982657 : Int) else (9969174 : Int)) else (9951848 : Int))) else (if Nat.ble r 8 then (if Nat.ble r 7 then (if Nat.ble r 6 then (9930685 : Int) else (9905694 : Int)) else (9876884 : Int)) else (if Nat.ble r 9 then (9844266 : Int) else (9807853 : Int)))) else (if Nat.ble r 15 then (if Nat.ble r 13 then (if Nat.ble r 12 then (if Nat.ble r 11 then (9767659 : Int) else (9723700 : Int)) else (9675991 : Int)) else (if Nat.ble r 14 then (9624553 : Int) else (9569404 : Int))) else (if Nat.ble r 18 then (if Nat.ble r 17 then (if Nat.ble r 16 then (9510566 : Int) else (9448061 : Int)) else (9381914 : Int)) else (if Nat.ble r 19 then (9312150 : Int) else (9238796 : Int))))) else (if Nat.ble r 30 then (if Nat.ble r 25 then (if Nat.ble r 23 then (if Nat.ble r 22 then (if Nat.ble r 21 then (9161880 : Int) else (9081432 : Int)) else (8997483 : Int)) else (if Nat.ble r 24 then (8910066 : Int) else (8819213 : Int))) else (if Nat.ble r 28 then (if Nat.ble r 27 then (if Nat.ble r 26 then (8724961 : Int) else (8627344 : Int)) else (8526402 : Int)) else (if Nat.ble r 29 then (8422173 : Int) else (8314697 : Int)))) else (if Nat.ble r 35 then (if Nat.ble r 33 then (if Nat.ble r 32 then (if Nat.ble r 31 then (8204015 : Int) else (8090170 : Int)) else (7973207 : Int)) else (if Nat.ble r 34 then (7853170 : Int) else (7730105 : Int))) else (if Nat.ble r 38 then (if Nat.ble r 37 then (if Nat.ble r 36 then (7604060 : Int) else (7475084 : Int)) else (7343226 : Int)) else (if Nat.ble r 39 then (7208537 : Int) else (7071069 : Int)))))) else (if Nat.ble r 60 then (if Nat.ble r 50 then (if Nat.ble r 45 then (if Nat.ble r 43 then (if Nat.ble r 42 then (if Nat.ble r 41 then (6930874 : Int) else (6788008 : Int)) else (6642525 : Int)) else (if Nat.ble r 44 then (6494481 : Int) else (6343933 : Int))) else (if Nat.ble r 48 then (if Nat.ble r 47 then (if Nat.ble r 46 then (6190940 : Int) else (6035560 : Int)) else (5877853 : Int)) else (if Nat.ble r 49 then (5717880 : Int) else (5555703 : Int)))) else (if Nat.ble r 55 then (if Nat.ble r 53 then (if Nat.ble r 52 then (if Nat.ble r 51 then (5391384 : Int) else (5224986 : Int)) else (5056574 : Int)) else (if Nat.ble r 54 then (4886213 : Int) else (4713968 : Int))) else (if Nat.ble r 58 then (if Nat.ble r 57 then (if Nat.ble r 56 then (4539906 : Int) else (4364093 : Int)) else (4186598 : Int)) else (if Nat.ble r 59 then (4007489 : Int) else (3826835 : Int))))) else (if Nat.ble r 70 then (if Nat.ble r 65 then (if Nat.ble r 63 then (if Nat.ble r 62 then (if Nat.ble r 61 then (3644706 : Int) else (3461171 : Int)) else (3276302 : Int)) else (if Nat.ble r 64 then (3090170 : Int) else (2902847 : Int))) else (if Nat.ble r 68 then (if Nat.ble r 67 then (if Nat.ble r 66 then (2714405 : Int) else (2524916 : Int)) else (2334454 : Int)) else (if Nat.ble r 69 then (2143092 : Int) else (1950904 : Int)))) else (if Nat.ble r 75 then (if Nat.ble r 73 then (if Nat.ble r 72 then (if Nat.ble r 71 then (1757963 : Int) else (1564345 : Int)) else (1370124 : Int)) else (if Nat.ble r 74 then (1175374 : Int) else (980172 : Int))) else (if Nat.ble r 78 then (if Nat.ble r 77 then (if Nat.ble r 76 then (784591 : Int) else (588709 : Int)) else (392599 : Int)) else (if Nat.ble r 79 then (196337 : Int) else (0 : Int))))))) else (if Nat.ble r 120 then (if Nat.ble r 100 then (if Nat.ble r 90 then (if Nat.ble r 85 then (if Nat.ble r 83 then (if Nat.ble r 82 then (if Nat.ble r 81 then (-196336 : Int) else (-392598 : Int)) else (-588708 : Int)) else (if Nat.ble r 84 then (-784590 : Int) else (-980171 : Int))) else (if Nat.ble r 88 then (if Nat.ble r 87 then (if Nat.ble r 86 then (-1175373 : Int) else (-1370123 : Int)) else (-1564344 : Int)) else (if Nat.ble r 89 then (-1757962 : Int) else (-1950903 : Int)))) else (if Nat.ble r 95 then (if Nat.ble r 93 then (if Nat.ble r 92 then (if Nat.ble r 91 then (-2143091 : Int) else (-2334453 : Int)) else (-2524915 : Int)) else (if Nat.ble r 94 then (-2714404 : Int) else (-2902846 : Int))) else (if Nat.ble r 98 then (if Nat.ble r 97 then (if Nat.ble r 96 then (-3090169 : Int) else (-3276301 : Int)) else (-3461170 : Int)) else (if Nat.ble r 99 then (-3644704 : Int) else (-3826834 : Int))))) else (if Nat.ble r 110 then (if Nat.ble r 105 then (if Nat.ble r 103 then (if Nat.ble r 102 then (if Nat.ble r 101 then (-4007488 : Int) else (-4186597 : Int)) else (-4364092 : Int)) else (if Nat.ble r 104 then (-4539904 : Int) else (-4713967 : Int))) else (if Nat.ble r 108 then (if Nat.ble r 107 then (if Nat.ble r 106 then (-4886212 : Int) else (-5056573 : Int)) else (-5224985 : Int)) else (if Nat.ble r 109 then (-5391383 : Int) else (-5555702 : Int)))) else (if Nat.ble r 115 then (if Nat.ble r 113 then (if Nat.ble r 112 then (if Nat.ble r 111 then (-5717879 : Int) else (-5877852 : Int)) else (-6035558 : Int)) else (if Nat.ble r 114 then (-6190938 : Int) else (-6343931 : Int))) else (if Nat.ble r 118 then (if Nat.ble r 117 then (if Nat.ble r 116 then (-6494479 : Int) else (-6642522 : Int)) else (-6788005 : Int)) else (if Nat.ble r 119 then (-6930871 : Int) else (-7071032 : Int)))))) else (if Nat.ble r 140 then (if Nat.ble r 130 then (if Nat.ble r 125 then (if Nat.ble r 123 then (if Nat.ble r 122 then (if Nat.ble r 121 then (-7208506 : Int) else (-7343201 : Int)) else (-7475064 : Int)) else (if Nat.ble r 124 then (-7604044 : Int) else (-7730092 : Int))) else (if Nat.ble r 128 then (if Nat.ble r 127 then (if Nat.ble r 126 then (-7853159 : Int) else (-7973198 : Int)) else (-8090163 : Int)) else (if Nat.ble r 129 then (-8204009 : Int) else (-8314692 : Int)))) else (if Nat.ble r 135 then (if Nat.ble r 133 then (if Nat.ble r 132 then (if Nat.ble r 131 then (-8422169 : Int) else (-8526399 : Int)) else (-8627342 : Int)) else (if Nat.ble r 134 then (-8724958 : Int) else (-8819211 : Int))) else (if Nat.ble r 138 then (if Nat.ble r 137 then (if Nat.ble r 136 then (-8910064 : Int) else (-8997482 : Int)) else (-9081431 : Int)) else (if Nat.ble r 139 then (-9161879 : Int) else (-9238795 : Int))))) else (if Nat.ble r 150 then (if Nat.ble r 145 then (if Nat.ble r 143 then (if Nat.ble r 142 then (if Nat.ble r 141 then (-9312149 : Int) else (-9381913 : Int)) else (-9448060 : Int)) else (if Nat.ble r 144 then (-9510565 : Int) else (-9569403 : Int))) else (if Nat.ble r 148 then (if Nat.ble r 147 then (if Nat.ble r 146 then (-9624552 : Int) else (-9675990 : Int)) else (-9723699 : Int)) else (if Nat.ble r 149 then (-9767658 : Int) else (-9807852 : Int)))) else (if Nat.ble r 155 then (if Nat.ble r 153 then (if Nat.ble r 152 then (if Nat.ble r 151 then (-9844265 : Int) else (-9876883 : Int)) else (-9905693 : Int)) else (if Nat.ble r 154 then (-9930684 : Int) else (-9951847 : Int))) else (if Nat.ble r 158 then (if Nat.ble r 157 then (if Nat.ble r 156 then (-9969173 : Int) else (-9982656 : Int)) else (-9992290 : Int)) else (if Nat.ble r 159 then (-9998072 : Int) else (-10000000 : Int))))))))

def intLe : Int → Int → Bool
  | .ofNat a, .ofNat b => Nat.ble a b
  | .ofNat _, .negSucc _ => false
  | .negSucc _, .ofNat _ => true
  | .negSucc a, .negSucc b => Nat.ble b a

def intEq : Int → Int → Bool
  | .ofNat a, .ofNat b => Nat.beq a b
  | .negSucc a, .negSucc b => Nat.beq a b
  | _, _ => false

def checkBandRange (rows : List (List Int)) (fn : Nat → Int) (start : Nat) : Nat → Bool
  | 0 => true
  | cnt + 1 =>
    let k := start + cnt
    if intEq (bandSumRows k rows) (fn k) then checkBandRange rows fn start cnt else false

def checkAlphaEntry (k : Nat) : Bool :=
  let D := certD
  let D2 := D * D
  let muInt := D2 - sgFn 0
  if Nat.ble k certK then
    let A_k := 4 * muInt * rFn k + D * sgFn k
    let tNu :=
      if Nat.beq k 1 then 2 * D2 * snuFn 0 + D2 * snuFn 2
      else if Nat.ble k (certK - 1) then D2 * (snuFn (k - 1) + snuFn (k + 1))
      else D2 * snuFn (certK - 1)
    let aCalc := 4 * A_k * mFn k - 2 * D2 * sfFn k - tNu
    intLe 0 A_k && intEq (alphaFn k) aCalc
  else
    intEq (alphaFn k) (-(D2 * snuFn certK))

def checkAlphaTail : Nat → Bool
  | 0 => true
  | k + 1 => if checkAlphaEntry (k + 1) then checkAlphaTail k else false

def checkAlphaListMatch : Nat → List Int → Bool
  | _, [] => true
  | k, a :: rest => if intEq a (alphaFn k) then checkAlphaListMatch (k + 1) rest else false

def sumTermsAux (muInt D : Int) : Nat → Int → Int → Int → (Int × Int × Int)
  | 0, sr, sa, sb => (sr, sa, sb)
  | k + 1, sr, sa, sb =>
    let kk := k + 1
    let rk := rFn kk
    let mk := mFn kk
    let Ak := 4 * muInt * rk + D * sgFn kk
    let Bk := 4 * muInt * rk - D * sgFn kk
    let bneg := if intLe 0 Bk then 0 else Bk
    sumTermsAux muInt D k (sr + rk * rk) (sa + Ak * mk * mk) (sb + bneg)

def checkConstEq : Bool :=
  let D := certD
  let D2 := D * D
  let D3 := D2 * D
  let D5 := D3 * D2
  let muInt := D2 - sgFn 0
  let (sumR2, sumAm2, sumBneg) := sumTermsAux muInt D certK 0 0 0
  let expected := 2 * D5 - 4 * D * muInt * sumR2 - 2 * sumAm2 + 2 * D2 * sumBneg
    - 2 * D3 * sfFn 0 - D3 * snuFn 1
  intLe 0 muInt && intEq certNumConst expected

def foldIdx (q N : Nat) : Nat :=
  let m := q % (4 * N)
  if Nat.ble m (2 * N) then m else 4 * N - m

def cellTerm (j k : Nat) (a : Int) : Int :=
  let i0 := foldIdx (k * j) certN
  let i1 := foldIdx (k * (j + 1)) certN
  let c0Lo := cosLoFn i0
  let c1Lo := cosLoFn i1
  let c0Hi := cosHiFn i0
  let c1Hi := cosHiFn i1
  let baseLo := if intLe c0Lo c1Lo then c0Lo else c1Lo
  let baseHi := if intLe c1Hi c0Hi then c0Hi else c1Hi
  let mMult := (k * (j + 1)) / (2 * certN)
  let straddle := Nat.ble (k * j) (2 * certN * mMult) && Nat.ble (2 * certN * mMult) (k * (j + 1))
  let loC := if straddle && Nat.beq (mMult % 2) 1 then -certMcos else baseLo
  let hiC := if straddle && Nat.beq (mMult % 2) 0 then certMcos else baseHi
  if intLe 0 a then a * loC else a * hiC

def cellSum : Nat → Nat → List Int → Int
  | _, _, [] => 0
  | j, k, a :: rest => cellTerm j k a + cellSum j (k + 1) rest

def certMinCellNum : Int := -528606715237356490317440

def checkCellRange (start : Nat) : Nat → Bool
  | 0 => true
  | cnt + 1 =>
    let j := start + cnt
    if intLe certMinCellNum (cellSum j 1 certAlphas) then
      checkCellRange start cnt
    else false

def checkCosEntry (N : Nat) (r : Nat) : Bool :=
  let lo := cosLoFn r
  let hi := cosHiFn r
  if Nat.beq r 0 then intEq lo certMcos && intEq hi certMcos
  else if Nat.beq r N then intEq lo 0 && intEq hi 0
  else if Nat.beq r (2 * N) then intEq lo (-certMcos) && intEq hi (-certMcos)
  else if Nat.ble (r + 1) N then
    let den1 := (2 * (N : Int)) * piScale
    let d2 := den1 * den1
    let d4 := d2 * d2
    let d6 := d4 * d2
    if Nat.ble (2 * r) N then
      let nHi := (r : Int) * piHiNum
      let n2 := nHi * nHi
      let n4 := n2 * n2
      let n6 := n4 * n2
      let lhsLo := lo * 720 * d6
      let rhsLo := certMcos * (720 * d6 - 360 * n2 * d4 + 30 * n4 * d2 - n6)
      let nLo := (r : Int) * piLoNum
      let d8 := d4 * d4
      let m2 := nLo * nLo
      let m4 := m2 * m2
      let m6 := m4 * m2
      let m8 := m4 * m4
      let lhsHi := certMcos * (40320 * d8 - 20160 * m2 * d6 + 1680 * m4 * d4 - 56 * m6 * d2 + m8)
      let rhsHi := hi * 40320 * d8
      intLe lhsLo rhsLo && intLe lhsHi rhsHi
    else
      let r4 : Int := (N : Int) - (r : Int)
      let nLo := r4 * piLoNum
      let d3 := d2 * den1
      let d5 := d3 * d2
      let d7 := d5 * d2
      let m2 := nLo * nLo
      let m3 := m2 * nLo
      let m5 := m3 * m2
      let m7 := m5 * m2
      let lhsLo := lo * 5040 * d7
      let rhsLo := certMcos * (5040 * nLo * d6 - 840 * m3 * d4 + 42 * m5 * d2 - m7)
      let nHi := r4 * piHiNum
      let d8 := d4 * d4
      let d9 := d7 * d2
      let p2 := nHi * nHi
      let p3 := p2 * nHi
      let p5 := p3 * p2
      let p7 := p5 * p2
      let p9 := p7 * p2
      let lhsHi := certMcos * (362880 * nHi * d8 - 60480 * p3 * d6 + 3024 * p5 * d4 - 72 * p7 * d2 + p9)
      let rhsHi := hi * 362880 * d9
      intLe lhsLo rhsLo && intLe lhsHi rhsHi
  else
    let rSym := 2 * N - r
    intEq lo (-cosHiFn rSym) && intEq hi (-cosLoFn rSym)

def checkCosTail (N : Nat) : Nat → Bool
  | 0 => checkCosEntry N 0
  | r + 1 => if checkCosEntry N (r + 1) then checkCosTail N r else false

private theorem sf_0_ok : checkBandRange cert_vf sfFn 0 22 = true := by decide
private theorem sf_1_ok : checkBandRange cert_vf sfFn 22 22 = true := by decide
private theorem sf_2_ok : checkBandRange cert_vf sfFn 44 22 = true := by decide
private theorem snu_0_ok : checkBandRange cert_vnu snuFn 0 22 = true := by decide
private theorem snu_1_ok : checkBandRange cert_vnu snuFn 22 22 = true := by decide
private theorem snu_2_ok : checkBandRange cert_vnu snuFn 44 22 = true := by decide
private theorem sg_0_ok : checkBandRange cert_vg sgFn 0 22 = true := by decide
private theorem sg_1_ok : checkBandRange cert_vg sgFn 22 22 = true := by decide
private theorem sg_2_ok : checkBandRange cert_vg sgFn 44 22 = true := by decide
private theorem vf_len_ok : cert_vf.all (fun r => Nat.beq r.length 66) = true := by decide
private theorem vnu_len_ok : cert_vnu.all (fun r => Nat.beq r.length 66) = true := by decide
private theorem vg_len_ok : cert_vg.all (fun r => Nat.beq r.length 66) = true := by decide
private theorem alphas_ok :
    (checkAlphaTail (certK + 1) && checkAlphaListMatch 1 certAlphas && checkConstEq) = true := by
  decide
private theorem alphas_len_ok : certAlphas.length = 66 := by decide
private theorem cos_ok : checkCosTail certN (2 * certN) = true := by decide
private theorem cells_0_ok : checkCellRange 0 20 = true := by decide
private theorem cells_1_ok : checkCellRange 20 20 = true := by decide
private theorem cells_2_ok : checkCellRange 40 20 = true := by decide
private theorem cells_3_ok : checkCellRange 60 20 = true := by decide

end CertData

section CertSoundness

open scoped BigOperators

/- ### 3. Soundness of Integer Checks, Cosine Table, Straddle Rule, and Cell Bound -/

theorem intLe_iff (a b : ℤ) : intLe a b = true ↔ a ≤ b := by
  cases a with
  | ofNat a =>
    cases b with
    | ofNat b =>
      change Nat.ble a b = true ↔ (a : ℤ) ≤ (b : ℤ)
      rw [Nat.ble_eq]
      omega
    | negSucc b =>
      change false = true ↔ (a : ℤ) ≤ Int.negSucc b
      constructor
      · intro h; simp at h
      · intro h; omega
  | negSucc a =>
    cases b with
    | ofNat b =>
      change true = true ↔ Int.negSucc a ≤ (b : ℤ)
      constructor
      · intro _; omega
      · intro _; rfl
    | negSucc b =>
      change Nat.ble b a = true ↔ Int.negSucc a ≤ Int.negSucc b
      rw [Nat.ble_eq]
      omega

theorem intEq_iff (a b : ℤ) : intEq a b = true ↔ a = b := by
  cases a with
  | ofNat a =>
    cases b with
    | ofNat b =>
      change Nat.beq a b = true ↔ (a : ℤ) = (b : ℤ)
      rw [Nat.beq_eq]
      omega
    | negSucc b =>
      change false = true ↔ (a : ℤ) = Int.negSucc b
      constructor
      · intro h; simp at h
      · intro h; omega
  | negSucc a =>
    cases b with
    | ofNat b =>
      change false = true ↔ Int.negSucc a = (b : ℤ)
      constructor
      · intro h; simp at h
      · intro h; omega
    | negSucc b =>
      change Nat.beq a b = true ↔ Int.negSucc a = Int.negSucc b
      rw [Nat.beq_eq]
      omega

theorem checkBandRange_sound (rows : List (List ℤ)) (fn : ℕ → ℤ) (start : ℕ) :
    ∀ n, checkBandRange rows fn start n = true →
      ∀ k, start ≤ k → k < start + n → bandSumRows k rows = fn k := by
  intro n
  induction n with
  | zero => intro _ k hk1 hk2; omega
  | succ n ih =>
    intro h k hk1 hk2
    dsimp [checkBandRange] at h
    split_ifs at h with heq
    by_cases hkn : k = start + n
    · subst hkn; exact (intEq_iff _ _).mp heq
    · exact ih h k hk1 (by omega)

theorem checkAlphaTail_sound :
    ∀ n, checkAlphaTail n = true → ∀ k, 1 ≤ k → k ≤ n → checkAlphaEntry k = true := by
  intro n
  induction n with
  | zero => intro _ k hk1 hk2; omega
  | succ n ih =>
    intro h k hk1 hk2
    dsimp [checkAlphaTail] at h
    split_ifs at h with hent
    by_cases hkn : k = n + 1
    · subst hkn; exact hent
    · exact ih h k hk1 (by omega)

def listGetZ : List ℤ → ℕ → ℤ
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, n + 1 => listGetZ xs n

theorem checkAlphaListMatch_sound :
    ∀ (xs : List ℤ) (k₀ : ℕ), checkAlphaListMatch k₀ xs = true →
      ∀ idx < xs.length, listGetZ xs idx = alphaFn (k₀ + idx) := by
  intro xs
  induction xs with
  | nil => intro _ _ idx h; simp at h
  | cons a rest ih =>
    intro k₀ h idx hidx
    dsimp [checkAlphaListMatch] at h
    split_ifs at h with heq
    cases idx with
    | zero =>
      dsimp [listGetZ]
      exact (intEq_iff _ _).mp heq
    | succ idx =>
      dsimp [listGetZ]
      simp only [List.length_cons, Nat.add_lt_add_iff_right] at hidx
      rw [show k₀ + (idx + 1) = k₀ + 1 + idx by omega]
      exact ih (k₀ + 1) h idx hidx

theorem sumTermsAux_eq (muInt D : ℤ) :
    ∀ (n : ℕ) (sr sa sb : ℤ),
      sumTermsAux muInt D n sr sa sb =
        (sr + ∑ k ∈ Finset.Icc 1 n, (rFn k) ^ 2,
         sa + ∑ k ∈ Finset.Icc 1 n, (4 * muInt * rFn k + D * sgFn k) * (mFn k) ^ 2,
         sb + ∑ k ∈ Finset.Icc 1 n, min (4 * muInt * rFn k - D * sgFn k) 0) := by
  intro n
  induction n with
  | zero =>
    intro sr sa sb
    simp [sumTermsAux]
  | succ n ih =>
    intro sr sa sb
    dsimp [sumTermsAux]
    rw [ih]
    have h1 : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot : n + 1 ∉ Finset.Icc 1 n := by
      simp only [Finset.mem_Icc]
      omega
    rw [h1, Finset.sum_insert hnot, Finset.sum_insert hnot, Finset.sum_insert hnot]
    have hmin : (if intLe 0 (4 * muInt * rFn (n + 1) - D * sgFn (n + 1)) then (0 : ℤ)
        else 4 * muInt * rFn (n + 1) - D * sgFn (n + 1)) =
        min (4 * muInt * rFn (n + 1) - D * sgFn (n + 1)) 0 := by
      split_ifs with h
      · have hle := (intLe_iff _ _).mp h
        omega
      · have hgt : ¬ (0 ≤ 4 * muInt * rFn (n + 1) - D * sgFn (n + 1)) :=
          fun hle => h ((intLe_iff _ _).mpr hle)
        omega
    rw [hmin]
    refine Prod.ext (by ring) (Prod.ext (by ring) (by ring))

theorem checkCosTail_sound (N : ℕ) :
    ∀ n, checkCosTail N n = true → ∀ r ≤ n, checkCosEntry N r = true := by
  intro n
  induction n with
  | zero =>
    intro h r hr
    have hr0 : r = 0 := by omega
    subst hr0
    exact h
  | succ n ih =>
    intro h r hr
    dsimp [checkCosTail] at h
    split_ifs at h with hent
    by_cases hrn : r = n + 1
    · subst hrn; exact hent
    · exact ih h r (by omega)

theorem checkCellRange_sound (start : ℕ) :
    ∀ n, checkCellRange start n = true →
      ∀ j, start ≤ j → j < start + n → certMinCellNum ≤ cellSum j 1 certAlphas := by
  intro n
  induction n with
  | zero => intro _ j hj1 hj2; omega
  | succ n ih =>
    intro h j hj1 hj2
    dsimp [checkCellRange] at h
    split_ifs at h with hle
    by_cases hjn : j = start + n
    · subst hjn; exact (intLe_iff _ _).mp hle
    · exact ih h j hj1 (by omega)

theorem foldIdx_le {q N : ℕ} (hN : 0 < N) : foldIdx q N ≤ 2 * N := by
  dsimp [foldIdx]
  have hm : q % (4 * N) < 4 * N := Nat.mod_lt q (by omega)
  split_ifs with h
  · exact Nat.ble_eq.mp h
  · have h' : ¬ (q % (4 * N) ≤ 2 * N) := fun hle => h (Nat.ble_eq.mpr hle)
    omega

theorem foldIdx_cos {q N : ℕ} (hN : 0 < N) :
    Real.cos (Real.pi * (q : ℝ) / (2 * (N : ℝ))) =
      Real.cos (Real.pi * (foldIdx q N : ℝ) / (2 * (N : ℝ))) := by
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hdiv : q = (q % (4 * N)) + 4 * N * (q / (4 * N)) := by
    have := Nat.div_add_mod q (4 * N)
    omega
  have h1 : Real.pi * (q : ℝ) / (2 * (N : ℝ)) =
      Real.pi * ((q % (4 * N) : ℕ) : ℝ) / (2 * (N : ℝ)) +
        ((q / (4 * N) : ℕ) : ℝ) * (2 * Real.pi) := by
    have hc : (q : ℝ) = ((q % (4 * N) : ℕ) : ℝ) + 4 * (N : ℝ) * ((q / (4 * N) : ℕ) : ℝ) := by
      exact_mod_cast hdiv
    rw [hc]
    field_simp [hN0]
    ring
  rw [h1, Real.cos_add_nat_mul_two_pi]
  dsimp [foldIdx]
  split_ifs with h
  · rfl
  · have h' : ¬ (q % (4 * N) ≤ 2 * N) := fun hle => h (Nat.ble_eq.mpr hle)
    have hm : q % (4 * N) < 4 * N := Nat.mod_lt q (by omega)
    have hsub : ((4 * N - q % (4 * N) : ℕ) : ℝ) = 4 * (N : ℝ) - ((q % (4 * N) : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    have h2 : Real.pi * ((q % (4 * N) : ℕ) : ℝ) / (2 * (N : ℝ)) =
        2 * Real.pi - Real.pi * ((4 * N - q % (4 * N) : ℕ) : ℝ) / (2 * (N : ℝ)) := by
      rw [hsub]
      field_simp [hN0]
      ring
    rw [h2, Real.cos_two_pi_sub]

private lemma cos_sub_odd_pi (q : ℕ) (u : ℝ) :
    Real.cos (u - ((2 * q + 1 : ℕ) : ℝ) * Real.pi) = -Real.cos u := by
  have h : u - ((2 * q + 1 : ℕ) : ℝ) * Real.pi = (u - Real.pi) - (q : ℝ) * (2 * Real.pi) := by
    push_cast; ring
  rw [h, Real.cos_sub_nat_mul_two_pi, ← Real.cos_neg, neg_sub, Real.cos_pi_sub]

private lemma cos_odd_pi_sub (q : ℕ) (u : ℝ) :
    Real.cos (((2 * q + 1 : ℕ) : ℝ) * Real.pi - u) = -Real.cos u := by
  rw [← Real.cos_neg, neg_sub, cos_sub_odd_pi]

theorem cos_interval_straddle {N k j : ℕ} (hN : 0 < N) (hk : k < 2 * N)
    {x : ℝ} (hx : x ∈ Set.Icc ((j : ℝ) / (4 * (N : ℝ))) (((j : ℝ) + 1) / (4 * (N : ℝ)))) :
    let mMult := (k * (j + 1)) / (2 * N)
    let straddle := k * j ≤ 2 * N * mMult ∧ 2 * N * mMult ≤ k * (j + 1)
    let c0 := Real.cos (Real.pi * (foldIdx (k * j) N : ℝ) / (2 * (N : ℝ)))
    let c1 := Real.cos (Real.pi * (foldIdx (k * (j + 1)) N : ℝ) / (2 * (N : ℝ)))
    (if straddle ∧ mMult % 2 = 1 then (-1 : ℝ) else min c0 c1) ≤
        Real.cos (2 * Real.pi * (k : ℝ) * x) ∧
      Real.cos (2 * Real.pi * (k : ℝ) * x) ≤
        (if straddle ∧ mMult % 2 = 0 then (1 : ℝ) else max c0 c1) := by
  intro mMult straddle c0 c1
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hk0 : 0 ≤ 2 * Real.pi * (k : ℝ) := by positivity
  set θ := 2 * Real.pi * (k : ℝ) * x
  set a := Real.pi * ((k * j : ℕ) : ℝ) / (2 * (N : ℝ))
  set b := Real.pi * ((k * (j + 1) : ℕ) : ℝ) / (2 * (N : ℝ))
  have ha_eq : a = 2 * Real.pi * (k : ℝ) * ((j : ℝ) / (4 * (N : ℝ))) := by
    dsimp [a]; push_cast; field_simp [hN0]; ring
  have hb_eq : b = 2 * Real.pi * (k : ℝ) * (((j : ℝ) + 1) / (4 * (N : ℝ))) := by
    dsimp [b]; push_cast; field_simp [hN0]; ring
  have ha_le : a ≤ θ := by
    rw [ha_eq]; exact mul_le_mul_of_nonneg_left hx.1 hk0
  have hle_b : θ ≤ b := by
    rw [hb_eq]; exact mul_le_mul_of_nonneg_left hx.2 hk0
  have hc0 : c0 = Real.cos a := (foldIdx_cos hN).symm
  have hc1 : c1 = Real.cos b := (foldIdx_cos hN).symm
  rw [hc0, hc1]
  have hm_le : 2 * N * mMult ≤ k * (j + 1) := Nat.mul_div_le (k * (j + 1)) (2 * N)
  have hm_lt : k * (j + 1) < 2 * N * (mMult + 1) := by
    have h := Nat.lt_div_mul_add (by omega : 0 < 2 * N) (a := k * (j + 1))
    dsimp [mMult] at *
    nlinarith
  have hkb_le : b ≤ ((mMult + 1 : ℕ) : ℝ) * Real.pi := by
    dsimp [b]
    rw [div_le_iff₀ (by positivity)]
    have hcast : ((k * (j + 1) : ℕ) : ℝ) ≤ (2 * (N : ℝ)) * ((mMult + 1 : ℕ) : ℝ) := by
      exact_mod_cast hm_lt.le
    nlinarith [Real.pi_pos]
  by_cases hstr : straddle
  · have hkj_le : k * j ≤ 2 * N * mMult := hstr.1
    have hkm_lt : 2 * N * mMult < k * j + 2 * N := by
      have : k * (j + 1) = k * j + k := by ring
      omega
    have ha_ge_prev : ((mMult : ℝ) - 1) * Real.pi ≤ a := by
      dsimp [a]
      rw [le_div_iff₀ (by positivity)]
      have hcast : 2 * (N : ℝ) * ((mMult : ℝ) - 1) ≤ ((k * j : ℕ) : ℝ) := by
        have h1 : (2 * N * mMult : ℝ) ≤ (k * j : ℕ) + 2 * N := by exact_mod_cast hkm_lt.le
        linarith
      nlinarith [Real.pi_pos]
    have ha_le_m : a ≤ (mMult : ℝ) * Real.pi := by
      dsimp [a]
      rw [div_le_iff₀ (by positivity)]
      have hcast : ((k * j : ℕ) : ℝ) ≤ 2 * (N : ℝ) * (mMult : ℝ) := by exact_mod_cast hkj_le
      nlinarith [Real.pi_pos]
    have hm_le_b : (mMult : ℝ) * Real.pi ≤ b := by
      dsimp [b]
      rw [le_div_iff₀ (by positivity)]
      have hcast : 2 * (N : ℝ) * (mMult : ℝ) ≤ ((k * (j + 1) : ℕ) : ℝ) := by exact_mod_cast hm_le
      nlinarith [Real.pi_pos]
    rcases Nat.mod_two_eq_zero_or_one mMult with heven | hodd
    · have hif1 : ¬ (straddle ∧ mMult % 2 = 1) := by omega
      have hif2 : straddle ∧ mMult % 2 = 0 := ⟨hstr, heven⟩
      rw [if_neg hif1, if_pos hif2]
      refine ⟨?_, Real.cos_le_one θ⟩
      obtain ⟨q, hq⟩ : ∃ q, mMult = 2 * q := ⟨mMult / 2, by omega⟩
      have hmq : (mMult : ℝ) * Real.pi = (q : ℝ) * (2 * Real.pi) := by
        rw [hq]; push_cast; ring
      rcases le_total θ ((mMult : ℝ) * Real.pi) with hθ | hθ
      · have h1 : 0 ≤ (q : ℝ) * (2 * Real.pi) - θ := by linarith
        have h2 : (q : ℝ) * (2 * Real.pi) - a ≤ Real.pi := by linarith
        have hcos := Real.cos_le_cos_of_nonneg_of_le_pi h1 h2
          (by linarith : (q : ℝ) * (2 * Real.pi) - θ ≤ (q : ℝ) * (2 * Real.pi) - a)
        rw [Real.cos_nat_mul_two_pi_sub, Real.cos_nat_mul_two_pi_sub] at hcos
        exact le_trans (min_le_left _ _) hcos
      · have h1 : 0 ≤ θ - (q : ℝ) * (2 * Real.pi) := by linarith
        have h2 : b - (q : ℝ) * (2 * Real.pi) ≤ Real.pi := by
          push_cast at hkb_le; linarith
        have hcos := Real.cos_le_cos_of_nonneg_of_le_pi h1 h2
          (by linarith : θ - (q : ℝ) * (2 * Real.pi) ≤ b - (q : ℝ) * (2 * Real.pi))
        rw [Real.cos_sub_nat_mul_two_pi, Real.cos_sub_nat_mul_two_pi] at hcos
        exact le_trans (min_le_right _ _) hcos
    · have hif1 : straddle ∧ mMult % 2 = 1 := ⟨hstr, hodd⟩
      have hif2 : ¬ (straddle ∧ mMult % 2 = 0) := by omega
      rw [if_pos hif1, if_neg hif2]
      refine ⟨Real.neg_one_le_cos θ, ?_⟩
      obtain ⟨q, hq⟩ : ∃ q, mMult = 2 * q + 1 := ⟨mMult / 2, by omega⟩
      have hmq : (mMult : ℝ) * Real.pi = ((2 * q + 1 : ℕ) : ℝ) * Real.pi := by
        rw [hq]
      rcases le_total θ ((mMult : ℝ) * Real.pi) with hθ | hθ
      · have h1 : 0 ≤ ((2 * q + 1 : ℕ) : ℝ) * Real.pi - θ := by linarith
        have h2 : ((2 * q + 1 : ℕ) : ℝ) * Real.pi - a ≤ Real.pi := by linarith
        have hcos := Real.cos_le_cos_of_nonneg_of_le_pi h1 h2
          (by linarith : ((2 * q + 1 : ℕ) : ℝ) * Real.pi - θ ≤ ((2 * q + 1 : ℕ) : ℝ) * Real.pi - a)
        rw [cos_odd_pi_sub, cos_odd_pi_sub] at hcos
        exact le_trans (by linarith) (le_max_left _ _)
      · have h1 : 0 ≤ θ - ((2 * q + 1 : ℕ) : ℝ) * Real.pi := by linarith
        have h2 : b - ((2 * q + 1 : ℕ) : ℝ) * Real.pi ≤ Real.pi := by
          push_cast at hkb_le; linarith
        have hcos := Real.cos_le_cos_of_nonneg_of_le_pi h1 h2
          (by linarith : θ - ((2 * q + 1 : ℕ) : ℝ) * Real.pi ≤ b - ((2 * q + 1 : ℕ) : ℝ) * Real.pi)
        rw [cos_sub_odd_pi, cos_sub_odd_pi] at hcos
        exact le_trans (by linarith) (le_max_right _ _)
  · have hif1 : ¬ (straddle ∧ mMult % 2 = 1) := fun h => hstr h.1
    have hif2 : ¬ (straddle ∧ mMult % 2 = 0) := fun h => hstr h.1
    rw [if_neg hif1, if_neg hif2]
    have hmkj : 2 * N * mMult < k * j := by
      by_contra hle
      exact hstr ⟨not_lt.mp hle, hm_le⟩
    have hm_le_a : (mMult : ℝ) * Real.pi ≤ a := by
      dsimp [a]
      rw [le_div_iff₀ (by positivity)]
      have hcast : 2 * (N : ℝ) * (mMult : ℝ) ≤ ((k * j : ℕ) : ℝ) := by exact_mod_cast hmkj.le
      nlinarith [Real.pi_pos]
    rcases Nat.mod_two_eq_zero_or_one mMult with heven | hodd
    · obtain ⟨q, hq⟩ : ∃ q, mMult = 2 * q := ⟨mMult / 2, by omega⟩
      have hmq : (mMult : ℝ) * Real.pi = (q : ℝ) * (2 * Real.pi) := by
        rw [hq]; push_cast; ring
      have ha1 : 0 ≤ a - (q : ℝ) * (2 * Real.pi) := by linarith
      have hθ1 : 0 ≤ θ - (q : ℝ) * (2 * Real.pi) := by linarith
      have hb2 : b - (q : ℝ) * (2 * Real.pi) ≤ Real.pi := by push_cast at hkb_le; linarith
      have hθ2 : θ - (q : ℝ) * (2 * Real.pi) ≤ Real.pi := by linarith
      have hlo := Real.cos_le_cos_of_nonneg_of_le_pi hθ1 hb2
        (by linarith : θ - (q : ℝ) * (2 * Real.pi) ≤ b - (q : ℝ) * (2 * Real.pi))
      have hhi := Real.cos_le_cos_of_nonneg_of_le_pi ha1 hθ2
        (by linarith : a - (q : ℝ) * (2 * Real.pi) ≤ θ - (q : ℝ) * (2 * Real.pi))
      rw [Real.cos_sub_nat_mul_two_pi, Real.cos_sub_nat_mul_two_pi] at hlo hhi
      exact ⟨le_trans (min_le_right _ _) hlo, le_trans hhi (le_max_left _ _)⟩
    · obtain ⟨q, hq⟩ : ∃ q, mMult = 2 * q + 1 := ⟨mMult / 2, by omega⟩
      have hmq : (mMult : ℝ) * Real.pi = ((2 * q + 1 : ℕ) : ℝ) * Real.pi := by rw [hq]
      have ha1 : 0 ≤ a - ((2 * q + 1 : ℕ) : ℝ) * Real.pi := by linarith
      have hθ1 : 0 ≤ θ - ((2 * q + 1 : ℕ) : ℝ) * Real.pi := by linarith
      have hb2 : b - ((2 * q + 1 : ℕ) : ℝ) * Real.pi ≤ Real.pi := by push_cast at hkb_le; linarith
      have hθ2 : θ - ((2 * q + 1 : ℕ) : ℝ) * Real.pi ≤ Real.pi := by linarith
      have hlo := Real.cos_le_cos_of_nonneg_of_le_pi ha1 hθ2
        (by linarith : a - ((2 * q + 1 : ℕ) : ℝ) * Real.pi ≤ θ - ((2 * q + 1 : ℕ) : ℝ) * Real.pi)
      have hhi := Real.cos_le_cos_of_nonneg_of_le_pi hθ1 hb2
        (by linarith : θ - ((2 * q + 1 : ℕ) : ℝ) * Real.pi ≤ b - ((2 * q + 1 : ℕ) : ℝ) * Real.pi)
      rw [cos_sub_odd_pi, cos_sub_odd_pi] at hlo hhi
      exact ⟨le_trans (min_le_left _ _) (by linarith), le_trans (by linarith) (le_max_right _ _)⟩

private lemma nat_beq_self (a : ℕ) : Nat.beq a a = true := Nat.beq_eq.mpr rfl

private lemma nat_beq_false {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b with
  | true => exact absurd (Nat.beq_eq.mp hb) h
  | false => rfl

private lemma nat_ble_false {a b : ℕ} (h : ¬ a ≤ b) : Nat.ble a b = false := by
  cases hb : Nat.ble a b with
  | true => exact absurd (Nat.ble_eq.mp hb) h
  | false => rfl

private lemma checkCosEntry_le_N {N r : ℕ} (hN : 0 < N) (hr : r ≤ N)
    (hok : checkCosEntry N r = true) :
    (cosLoFn r : ℝ) / (certMcos : ℝ) ≤ Real.cos (Real.pi * (r : ℝ) / (2 * (N : ℝ))) ∧
      Real.cos (Real.pi * (r : ℝ) / (2 * (N : ℝ))) ≤ (cosHiFn r : ℝ) / (certMcos : ℝ) := by
  have hMpos : (0 : ℝ) < (certMcos : ℝ) := by norm_num [certMcos]
  have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  have hN0 : (N : ℝ) ≠ 0 := hNpos.ne'
  dsimp [checkCosEntry] at hok
  by_cases hr0 : r = 0
  · subst hr0
    simp only [nat_beq_self, ↓reduceIte, Bool.and_eq_true, intEq_iff] at hok
    rcases hok with ⟨hlo, hhi⟩
    rw [hlo, hhi]
    norm_num [certMcos]
  · have hbeq0 : Nat.beq r 0 = false := nat_beq_false hr0
    rw [hbeq0] at hok
    by_cases hrN : r = N
    · subst hrN
      simp only [nat_beq_self, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
        intEq_iff] at hok
      rcases hok with ⟨hlo, hhi⟩
      rw [hlo, hhi]
      have harg : Real.pi * (r : ℝ) / (2 * (r : ℝ)) = Real.pi / 2 := by
        field_simp [hN0]
      rw [harg, Real.cos_pi_div_two]
      norm_num
    · have hbeqN : Nat.beq r N = false := nat_beq_false hrN
      have hbeq2N : Nat.beq r (2 * N) = false := nat_beq_false (by omega)
      have hbleN : Nat.ble (r + 1) N = true := Nat.ble_eq.mpr (by omega)
      rw [hbeqN, hbeq2N, hbleN] at hok
      simp only [Bool.false_eq_true, ↓reduceIte] at hok
      set den1 : ℝ := (2 * (N : ℝ)) * (piScale : ℝ)
      have hden1 : 0 < den1 := by dsimp [den1, piScale]; positivity
      have hpi := pi_bounds_8d
      by_cases h2r : 2 * r ≤ N
      · have hble2r : Nat.ble (2 * r) N = true := Nat.ble_eq.mpr h2r
        rw [hble2r] at hok
        simp only [↓reduceIte, Bool.and_eq_true, intLe_iff] at hok
        rcases hok with ⟨hleLo, hleHi⟩
        set tLo : ℝ := (r : ℝ) * (piLoNum : ℝ) / den1
        set tHi : ℝ := (r : ℝ) * (piHiNum : ℝ) / den1
        set θ : ℝ := Real.pi * (r : ℝ) / (2 * (N : ℝ))
        have hr_le : (r : ℝ) / (2 * (N : ℝ)) ≤ 1 / 4 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          have : 2 * (r : ℝ) ≤ (N : ℝ) := by exact_mod_cast h2r
          linarith
        have htLo_pos : 0 ≤ tLo := by dsimp [tLo, piLoNum]; positivity
        have htHi_pos : 0 ≤ tHi := by dsimp [tHi, piHiNum]; positivity
        have hθ_pos : 0 ≤ θ := by dsimp [θ]; positivity
        have htLo_le : tLo ≤ θ := by
          have heq1 : tLo = ((r : ℝ) / (2 * (N : ℝ))) * ((314159265 : ℝ) / 100000000) := by
            dsimp [tLo, den1, piLoNum, piScale]; norm_num; ring
          have heq2 : θ = ((r : ℝ) / (2 * (N : ℝ))) * Real.pi := by
            dsimp [θ]; ring
          rw [heq1, heq2]
          exact mul_le_mul_of_nonneg_left hpi.1.le (by positivity)
        have hθ_le_tHi : θ ≤ tHi := by
          have heq1 : θ = ((r : ℝ) / (2 * (N : ℝ))) * Real.pi := by
            dsimp [θ]; ring
          have heq2 : tHi = ((r : ℝ) / (2 * (N : ℝ))) * ((314159266 : ℝ) / 100000000) := by
            dsimp [tHi, den1, piHiNum, piScale]; norm_num; ring
          rw [heq1, heq2]
          exact mul_le_mul_of_nonneg_left hpi.2.le (by positivity)
        have htHi_le_pi : tHi ≤ Real.pi := by
          have heq : tHi = ((r : ℝ) / (2 * (N : ℝ))) * ((314159266 : ℝ) / 100000000) := by
            dsimp [tHi, den1, piHiNum, piScale]; norm_num; ring
          rw [heq]
          have h1 : ((r : ℝ) / (2 * (N : ℝ))) * ((314159266 : ℝ) / 100000000) ≤
              (1 / 4 : ℝ) * ((314159266 : ℝ) / 100000000) :=
            mul_le_mul_of_nonneg_right hr_le (by norm_num)
          linarith [Real.pi_gt_three]
        have hcos_lo : Real.cos tHi ≤ Real.cos θ :=
          Real.cos_le_cos_of_nonneg_of_le_pi hθ_pos htHi_le_pi hθ_le_tHi
        have hcos_hi : Real.cos θ ≤ Real.cos tLo :=
          Real.cos_le_cos_of_nonneg_of_le_pi htLo_pos (hθ_le_tHi.trans htHi_le_pi) htLo_le
        have hcastLo : (cosLoFn r : ℝ) * 720 * den1 ^ 6 ≤
            (certMcos : ℝ) * (720 * den1 ^ 6 - 360 * ((r : ℝ) * (piHiNum : ℝ)) ^ 2 * den1 ^ 4 +
              30 * ((r : ℝ) * (piHiNum : ℝ)) ^ 4 * den1 ^ 2 - ((r : ℝ) * (piHiNum : ℝ)) ^ 6) := by
          have h' := Int.cast_le (R := ℝ).mpr hleLo
          push_cast at h'
          refine (le_of_eq ?_).trans (h'.trans (le_of_eq ?_)) <;> ((try dsimp [den1]); ring)
        have hpolyLo : (cosLoFn r : ℝ) / (certMcos : ℝ) ≤
            1 - tHi ^ 2 / 2 + tHi ^ 4 / 24 - tHi ^ 6 / 720 := by
          have hrat : 1 - tHi ^ 2 / 2 + tHi ^ 4 / 24 - tHi ^ 6 / 720 =
              (720 * den1 ^ 6 - 360 * ((r : ℝ) * (piHiNum : ℝ)) ^ 2 * den1 ^ 4 +
                30 * ((r : ℝ) * (piHiNum : ℝ)) ^ 4 * den1 ^ 2 - ((r : ℝ) * (piHiNum : ℝ)) ^ 6) /
                (720 * den1 ^ 6) := by
            dsimp [tHi]
            field_simp [hden1.ne']
            ring
          rw [hrat, div_le_div_iff₀ hMpos (by positivity)]
          linarith
        have hcastHi : (certMcos : ℝ) * (40320 * den1 ^ 8 - 20160 * ((r : ℝ) * (piLoNum : ℝ)) ^ 2 * den1 ^ 6 +
            1680 * ((r : ℝ) * (piLoNum : ℝ)) ^ 4 * den1 ^ 4 - 56 * ((r : ℝ) * (piLoNum : ℝ)) ^ 6 * den1 ^ 2 +
            ((r : ℝ) * (piLoNum : ℝ)) ^ 8) ≤ (cosHiFn r : ℝ) * 40320 * den1 ^ 8 := by
          have h' := Int.cast_le (R := ℝ).mpr hleHi
          push_cast at h'
          refine (le_of_eq ?_).trans (h'.trans (le_of_eq ?_)) <;> ((try dsimp [den1]); ring)
        have hpolyHi : 1 - tLo ^ 2 / 2 + tLo ^ 4 / 24 - tLo ^ 6 / 720 + tLo ^ 8 / 40320 ≤
            (cosHiFn r : ℝ) / (certMcos : ℝ) := by
          have hrat : 1 - tLo ^ 2 / 2 + tLo ^ 4 / 24 - tLo ^ 6 / 720 + tLo ^ 8 / 40320 =
              (40320 * den1 ^ 8 - 20160 * ((r : ℝ) * (piLoNum : ℝ)) ^ 2 * den1 ^ 6 +
                1680 * ((r : ℝ) * (piLoNum : ℝ)) ^ 4 * den1 ^ 4 - 56 * ((r : ℝ) * (piLoNum : ℝ)) ^ 6 * den1 ^ 2 +
                ((r : ℝ) * (piLoNum : ℝ)) ^ 8) / (40320 * den1 ^ 8) := by
            dsimp [tLo]
            field_simp [hden1.ne']
            ring
          rw [hrat, div_le_div_iff₀ (by positivity) hMpos]
          linarith
        exact ⟨hpolyLo.trans ((cos_taylor_deg6_le htHi_pos).trans hcos_lo),
          hcos_hi.trans ((cos_le_taylor_deg8 htLo_pos).trans hpolyHi)⟩
      · have hble2r : Nat.ble (2 * r) N = false := nat_ble_false h2r
        rw [hble2r] at hok
        simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, intLe_iff] at hok
        rcases hok with ⟨hleLo, hleHi⟩
        set r4 : ℕ := N - r
        have hr4_real : (N : ℝ) - (r : ℝ) = (r4 : ℝ) := by
          rw [Nat.cast_sub (by omega)]
        set sLo : ℝ := (r4 : ℝ) * (piLoNum : ℝ) / den1
        set sHi : ℝ := (r4 : ℝ) * (piHiNum : ℝ) / den1
        set θ' : ℝ := Real.pi * (r4 : ℝ) / (2 * (N : ℝ))
        have hcos_sin : Real.cos (Real.pi * (r : ℝ) / (2 * (N : ℝ))) = Real.sin θ' := by
          have harg : Real.pi * (r : ℝ) / (2 * (N : ℝ)) = Real.pi / 2 - θ' := by
            dsimp [θ']; rw [← hr4_real]; field_simp [hN0]; ring
          rw [harg, Real.cos_pi_div_two_sub]
        rw [hcos_sin]
        have hr4_le : (r4 : ℝ) / (2 * (N : ℝ)) ≤ 1 / 4 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          have : 2 * (r4 : ℝ) ≤ (N : ℝ) := by
            have : 2 * r4 ≤ N := by omega
            exact_mod_cast this
          linarith
        have hsLo_pos : 0 ≤ sLo := by dsimp [sLo, piLoNum]; positivity
        have hsHi_pos : 0 ≤ sHi := by dsimp [sHi, piHiNum]; positivity
        have hsLo_le : sLo ≤ θ' := by
          have heq1 : sLo = ((r4 : ℝ) / (2 * (N : ℝ))) * ((314159265 : ℝ) / 100000000) := by
            dsimp [sLo, den1, piLoNum, piScale]; norm_num; ring
          have heq2 : θ' = ((r4 : ℝ) / (2 * (N : ℝ))) * Real.pi := by
            dsimp [θ']; ring
          rw [heq1, heq2]
          exact mul_le_mul_of_nonneg_left hpi.1.le (by positivity)
        have hθ'_le_sHi : θ' ≤ sHi := by
          have heq1 : θ' = ((r4 : ℝ) / (2 * (N : ℝ))) * Real.pi := by
            dsimp [θ']; ring
          have heq2 : sHi = ((r4 : ℝ) / (2 * (N : ℝ))) * ((314159266 : ℝ) / 100000000) := by
            dsimp [sHi, den1, piHiNum, piScale]; norm_num; ring
          rw [heq1, heq2]
          exact mul_le_mul_of_nonneg_left hpi.2.le (by positivity)
        have hsHi_le_pi2 : sHi ≤ Real.pi / 2 := by
          have heq : sHi = ((r4 : ℝ) / (2 * (N : ℝ))) * ((314159266 : ℝ) / 100000000) := by
            dsimp [sHi, den1, piHiNum, piScale]; norm_num; ring
          rw [heq]
          have h1 : ((r4 : ℝ) / (2 * (N : ℝ))) * ((314159266 : ℝ) / 100000000) ≤
              (1 / 4 : ℝ) * ((314159266 : ℝ) / 100000000) :=
            mul_le_mul_of_nonneg_right hr4_le (by norm_num)
          linarith [Real.pi_gt_three]
        have hsin_lo : Real.sin sLo ≤ Real.sin θ' :=
          Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
            (hθ'_le_sHi.trans hsHi_le_pi2) hsLo_le
        have hsin_hi : Real.sin θ' ≤ Real.sin sHi :=
          Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
            hsHi_le_pi2 hθ'_le_sHi
        have hcastLo : (cosLoFn r : ℝ) * 5040 * den1 ^ 7 ≤
            (certMcos : ℝ) * (5040 * ((r4 : ℝ) * (piLoNum : ℝ)) * den1 ^ 6 -
              840 * ((r4 : ℝ) * (piLoNum : ℝ)) ^ 3 * den1 ^ 4 +
              42 * ((r4 : ℝ) * (piLoNum : ℝ)) ^ 5 * den1 ^ 2 -
              ((r4 : ℝ) * (piLoNum : ℝ)) ^ 7) := by
          have h' := Int.cast_le (R := ℝ).mpr hleLo
          push_cast at h'
          refine (le_of_eq ?_).trans (h'.trans (le_of_eq ?_)) <;>
            ((try dsimp [den1]); (try rw [← hr4_real]); ring)
        have hpolyLo : (cosLoFn r : ℝ) / (certMcos : ℝ) ≤
            sLo - sLo ^ 3 / 6 + sLo ^ 5 / 120 - sLo ^ 7 / 5040 := by
          have hrat : sLo - sLo ^ 3 / 6 + sLo ^ 5 / 120 - sLo ^ 7 / 5040 =
              (5040 * ((r4 : ℝ) * (piLoNum : ℝ)) * den1 ^ 6 -
                840 * ((r4 : ℝ) * (piLoNum : ℝ)) ^ 3 * den1 ^ 4 +
                42 * ((r4 : ℝ) * (piLoNum : ℝ)) ^ 5 * den1 ^ 2 -
                ((r4 : ℝ) * (piLoNum : ℝ)) ^ 7) / (5040 * den1 ^ 7) := by
            dsimp [sLo]
            field_simp [hden1.ne']
            ring
          rw [hrat, div_le_div_iff₀ hMpos (by positivity)]
          linarith
        have hcastHi : (certMcos : ℝ) * (362880 * ((r4 : ℝ) * (piHiNum : ℝ)) * den1 ^ 8 -
            60480 * ((r4 : ℝ) * (piHiNum : ℝ)) ^ 3 * den1 ^ 6 +
            3024 * ((r4 : ℝ) * (piHiNum : ℝ)) ^ 5 * den1 ^ 4 -
            72 * ((r4 : ℝ) * (piHiNum : ℝ)) ^ 7 * den1 ^ 2 +
            ((r4 : ℝ) * (piHiNum : ℝ)) ^ 9) ≤ (cosHiFn r : ℝ) * 362880 * den1 ^ 9 := by
          have h' := Int.cast_le (R := ℝ).mpr hleHi
          push_cast at h'
          refine (le_of_eq ?_).trans (h'.trans (le_of_eq ?_)) <;>
            ((try dsimp [den1]); (try rw [← hr4_real]); ring)
        have hpolyHi : sHi - sHi ^ 3 / 6 + sHi ^ 5 / 120 - sHi ^ 7 / 5040 + sHi ^ 9 / 362880 ≤
            (cosHiFn r : ℝ) / (certMcos : ℝ) := by
          have hrat : sHi - sHi ^ 3 / 6 + sHi ^ 5 / 120 - sHi ^ 7 / 5040 + sHi ^ 9 / 362880 =
              (362880 * ((r4 : ℝ) * (piHiNum : ℝ)) * den1 ^ 8 -
                60480 * ((r4 : ℝ) * (piHiNum : ℝ)) ^ 3 * den1 ^ 6 +
                3024 * ((r4 : ℝ) * (piHiNum : ℝ)) ^ 5 * den1 ^ 4 -
                72 * ((r4 : ℝ) * (piHiNum : ℝ)) ^ 7 * den1 ^ 2 +
                ((r4 : ℝ) * (piHiNum : ℝ)) ^ 9) / (362880 * den1 ^ 9) := by
            dsimp [sHi]
            field_simp [hden1.ne']
            ring
          rw [hrat, div_le_div_iff₀ (by positivity) hMpos]
          linarith
        exact ⟨hpolyLo.trans ((sin_taylor_deg7_le hsLo_pos).trans hsin_lo),
          hsin_hi.trans ((sin_le_taylor_deg9 hsHi_pos).trans hpolyHi)⟩

theorem cert80_cos_table_bounds :
    ∀ r ≤ 2 * certN,
      (cosLoFn r : ℝ) / (certMcos : ℝ) ≤
          Real.cos (Real.pi * (r : ℝ) / (2 * (certN : ℝ))) ∧
        Real.cos (Real.pi * (r : ℝ) / (2 * (certN : ℝ))) ≤
          (cosHiFn r : ℝ) / (certMcos : ℝ) := by
  have hall : ∀ r ≤ 2 * certN, checkCosEntry certN r = true :=
    checkCosTail_sound certN (2 * certN) cos_ok
  have hN : 0 < certN := by decide
  intro r hr
  by_cases hrN : r ≤ certN
  · exact checkCosEntry_le_N hN hrN (hall r hr)
  · by_cases hr2N : r = 2 * certN
    · subst hr2N
      have hlo : cosLoFn (2 * certN) = -certMcos := by decide
      have hhi : cosHiFn (2 * certN) = -certMcos := by decide
      rw [hlo, hhi]
      have harg : Real.pi * ((2 * certN : ℕ) : ℝ) / (2 * (certN : ℝ)) = Real.pi := by
        norm_num [certN]
      rw [harg, Real.cos_pi]
      norm_num [certMcos]
    · have hgt : certN < r := Nat.lt_of_not_ge hrN
      have hlt : r < 2 * certN := Nat.lt_of_le_of_ne hr hr2N
      set rSym := 2 * certN - r
      have hrSym_le : rSym ≤ certN := by omega
      have hsym := checkCosEntry_le_N hN hrSym_le (hall rSym (by omega))
      have hok := hall r hr
      dsimp [checkCosEntry] at hok
      have h1 : Nat.beq r 0 = false := nat_beq_false (by omega)
      have h2 : Nat.beq r certN = false := nat_beq_false (by omega)
      have h3 : Nat.beq r (2 * certN) = false := nat_beq_false hr2N
      have h4 : Nat.ble (r + 1) certN = false := nat_ble_false (by omega)
      rw [h1, h2, h3, h4] at hok
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, intEq_iff] at hok
      rcases hok with ⟨hlo, hhi⟩
      rw [show 2 * certN - r = rSym by rfl] at hlo hhi
      have hrSym_real : (rSym : ℝ) = 2 * (certN : ℝ) - (r : ℝ) := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      have harg : Real.pi * (r : ℝ) / (2 * (certN : ℝ)) =
          Real.pi - Real.pi * (rSym : ℝ) / (2 * (certN : ℝ)) := by
        rw [hrSym_real]; norm_num [certN]; ring
      rw [harg, Real.cos_pi_sub, hlo, hhi]
      push_cast
      rw [neg_div, neg_div]
      constructor <;> linarith [hsym.1, hsym.2]

private lemma cellTerm_le {j k : ℕ} (_hk1 : 1 ≤ k) (hk2 : k < 2 * certN)
    {x : ℝ} (hx : x ∈ Set.Icc ((j : ℝ) / (4 * 80)) (((j : ℝ) + 1) / (4 * 80)))
    (a : ℤ) :
    ((cellTerm j k a : ℤ) : ℝ) ≤
      (certMcos : ℝ) * ((a : ℝ) * Real.cos (2 * Real.pi * (k : ℝ) * x)) := by
  have hN : 0 < certN := by decide
  have hMpos : (0 : ℝ) < (certMcos : ℝ) := by norm_num [certMcos]
  set i0 := foldIdx (k * j) certN
  set i1 := foldIdx (k * (j + 1)) certN
  have hb0 := cert80_cos_table_bounds i0 (foldIdx_le hN)
  have hb1 := cert80_cos_table_bounds i1 (foldIdx_le hN)
  have hstr := cos_interval_straddle hN hk2 (j := j) (x := x) (by simpa [certN] using hx)
  dsimp only [cellTerm]
  set baseLo := if intLe (cosLoFn i0) (cosLoFn i1) then cosLoFn i0 else cosLoFn i1
  set baseHi := if intLe (cosHiFn i1) (cosHiFn i0) then cosHiFn i0 else cosHiFn i1
  set mMult := (k * (j + 1)) / (2 * certN)
  set straddleB := Nat.ble (k * j) (2 * certN * mMult) && Nat.ble (2 * certN * mMult) (k * (j + 1))
  set loC := if straddleB && Nat.beq (mMult % 2) 1 then -certMcos else baseLo
  set hiC := if straddleB && Nat.beq (mMult % 2) 0 then certMcos else baseHi
  have hstrB_iff : straddleB = true ↔ k * j ≤ 2 * certN * mMult ∧ 2 * certN * mMult ≤ k * (j + 1) := by
    dsimp [straddleB]
    rw [Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq]
  have hbaseLo : (baseLo : ℝ) / (certMcos : ℝ) ≤
      min (Real.cos (Real.pi * (i0 : ℝ) / (2 * (certN : ℝ))))
        (Real.cos (Real.pi * (i1 : ℝ) / (2 * (certN : ℝ)))) := by
    dsimp [baseLo]
    split_ifs with h
    · have hle : (cosLoFn i0 : ℝ) ≤ (cosLoFn i1 : ℝ) := Int.cast_le.mpr ((intLe_iff _ _).mp h)
      exact le_min hb0.1 ((div_le_div_iff_of_pos_right hMpos).mpr hle |>.trans hb1.1)
    · have hgt : (cosLoFn i1 : ℝ) ≤ (cosLoFn i0 : ℝ) := by
        have : ¬ (cosLoFn i0 ≤ cosLoFn i1) := fun h1 => h ((intLe_iff _ _).mpr h1)
        exact_mod_cast (by omega : cosLoFn i1 ≤ cosLoFn i0)
      exact le_min ((div_le_div_iff_of_pos_right hMpos).mpr hgt |>.trans hb0.1) hb1.1
  have hbaseHi : max (Real.cos (Real.pi * (i0 : ℝ) / (2 * (certN : ℝ))))
        (Real.cos (Real.pi * (i1 : ℝ) / (2 * (certN : ℝ)))) ≤
      (baseHi : ℝ) / (certMcos : ℝ) := by
    dsimp [baseHi]
    split_ifs with h
    · have hle : (cosHiFn i1 : ℝ) ≤ (cosHiFn i0 : ℝ) := Int.cast_le.mpr ((intLe_iff _ _).mp h)
      exact max_le hb0.2 (hb1.2.trans ((div_le_div_iff_of_pos_right hMpos).mpr hle))
    · have hgt : (cosHiFn i0 : ℝ) ≤ (cosHiFn i1 : ℝ) := by
        have : ¬ (cosHiFn i1 ≤ cosHiFn i0) := fun h1 => h ((intLe_iff _ _).mpr h1)
        exact_mod_cast (by omega : cosHiFn i0 ≤ cosHiFn i1)
      exact max_le (hb0.2.trans ((div_le_div_iff_of_pos_right hMpos).mpr hgt)) hb1.2
  have hloC : (loC : ℝ) / (certMcos : ℝ) ≤ Real.cos (2 * Real.pi * (k : ℝ) * x) := by
    dsimp [loC]
    split_ifs with h1
    · rw [Bool.and_eq_true, hstrB_iff, Nat.beq_eq] at h1
      have h1' : (k * j ≤ 2 * certN * mMult ∧ 2 * certN * mMult ≤ k * (j + 1)) ∧ mMult % 2 = 1 := h1
      have := hstr.1
      rw [if_pos h1'] at this
      push_cast
      rw [neg_div, div_self hMpos.ne']
      exact this
    · have h1' : ¬ ((k * j ≤ 2 * certN * mMult ∧ 2 * certN * mMult ≤ k * (j + 1)) ∧ mMult % 2 = 1) := by
        intro hc
        apply h1
        rw [Bool.and_eq_true, hstrB_iff, Nat.beq_eq]
        exact hc
      have := hstr.1
      rw [if_neg h1'] at this
      exact hbaseLo.trans this
  have hhiC : Real.cos (2 * Real.pi * (k : ℝ) * x) ≤ (hiC : ℝ) / (certMcos : ℝ) := by
    dsimp [hiC]
    split_ifs with h1
    · rw [Bool.and_eq_true, hstrB_iff, Nat.beq_eq] at h1
      have h1' : (k * j ≤ 2 * certN * mMult ∧ 2 * certN * mMult ≤ k * (j + 1)) ∧ mMult % 2 = 0 := h1
      have := hstr.2
      rw [if_pos h1'] at this
      rw [div_self hMpos.ne']
      exact this
    · have h1' : ¬ ((k * j ≤ 2 * certN * mMult ∧ 2 * certN * mMult ≤ k * (j + 1)) ∧ mMult % 2 = 0) := by
        intro hc
        apply h1
        rw [Bool.and_eq_true, hstrB_iff, Nat.beq_eq]
        exact hc
      have := hstr.2
      rw [if_neg h1'] at this
      exact this.trans hbaseHi
  split_ifs with ha
  · have ha0 : (0 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ((intLe_iff _ _).mp ha)
    have hmul := mul_le_mul_of_nonneg_left ((div_le_iff₀ hMpos).mp hloC) ha0
    push_cast
    linarith
  · have ha0 : (a : ℝ) ≤ 0 := by
      have : ¬ (0 ≤ a) := fun h1 => ha ((intLe_iff _ _).mpr h1)
      exact_mod_cast (by omega : a ≤ 0)
    have hmul := mul_le_mul_of_nonpos_left ((le_div_iff₀ hMpos).mp hhiC) ha0
    push_cast
    linarith

private lemma cellSum_le (j : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc ((j : ℝ) / (4 * 80)) (((j : ℝ) + 1) / (4 * 80))) :
    ∀ (xs : List ℤ) (k₀ : ℕ), 1 ≤ k₀ → k₀ + xs.length ≤ 2 * certN →
      ((cellSum j k₀ xs : ℤ) : ℝ) ≤
        (certMcos : ℝ) * ∑ idx ∈ Finset.range xs.length,
          (listGetZ xs idx : ℝ) * Real.cos (2 * Real.pi * ((k₀ + idx : ℕ) : ℝ) * x) := by
  intro xs
  induction xs with
  | nil =>
    intro k₀ _ _
    simp [cellSum]
  | cons a rest ih =>
    intro k₀ hk0 hlen
    simp only [List.length_cons] at hlen ⊢
    dsimp [cellSum]
    rw [Finset.sum_range_succ']
    have hterm := cellTerm_le hk0 (by omega) hx a
    have hrest := ih (k₀ + 1) (by omega) (by omega)
    have hsum_eq : ∑ idx ∈ Finset.range rest.length,
        (listGetZ (a :: rest) (idx + 1) : ℝ) *
          Real.cos (2 * Real.pi * ((k₀ + (idx + 1) : ℕ) : ℝ) * x) =
        ∑ idx ∈ Finset.range rest.length,
          (listGetZ rest idx : ℝ) *
            Real.cos (2 * Real.pi * ((k₀ + 1 + idx : ℕ) : ℝ) * x) := by
      refine Finset.sum_congr rfl fun idx _ => ?_
      simp only [listGetZ, Nat.add_assoc, Nat.add_comm 1 idx]
    rw [hsum_eq]
    simp only [listGetZ, Nat.add_zero]
    have hadd : ((cellTerm j k₀ a + cellSum j (k₀ + 1) rest : ℤ) : ℝ) =
        ((cellTerm j k₀ a : ℤ) : ℝ) + ((cellSum j (k₀ + 1) rest : ℤ) : ℝ) :=
      Int.cast_add _ _
    rw [hadd, mul_add]
    linarith [hterm, hrest]

theorem cert80_cell_bound_exact :
    ∀ (j : ℕ), j < 80 → ∀ x ∈ Set.Icc ((j : ℝ) / (4 * 80)) (((j : ℝ) + 1) / (4 * 80)),
      (4055172655215574821001279 : ℝ) / 3125000000000000000000000 ≤
        (certNumConst : ℝ) / (2 * (100000 : ℝ) ^ 5) +
          (∑ k ∈ Finset.Icc 1 66, (alphaFn k : ℝ) * Real.cos (2 * Real.pi * (k : ℝ) * x)) /
            (2 * (100000 : ℝ) ^ 4) := by
  have hcells : ∀ j < 80, certMinCellNum ≤ cellSum j 1 certAlphas := by
    intro j hj
    rcases lt_or_ge j 20 with h1 | h1
    · exact checkCellRange_sound 0 20 cells_0_ok j (by omega) h1
    · rcases lt_or_ge j 40 with h2 | h2
      · exact checkCellRange_sound 20 20 cells_1_ok j h1 h2
      · rcases lt_or_ge j 60 with h3 | h3
        · exact checkCellRange_sound 40 20 cells_2_ok j h2 h3
        · exact checkCellRange_sound 60 20 cells_3_ok j h3 hj
  have halphas_and : checkAlphaTail (certK + 1) = true ∧
      checkAlphaListMatch 1 certAlphas = true ∧ checkConstEq = true := by
    have h := alphas_ok
    rw [Bool.and_eq_true, Bool.and_eq_true] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  have halphas_match := checkAlphaListMatch_sound certAlphas 1 halphas_and.2.1
  intro j hj x hx
  have hcell_int : ((certMinCellNum : ℤ) : ℝ) ≤ ((cellSum j 1 certAlphas : ℤ) : ℝ) :=
    Int.cast_le.mpr (hcells j hj)
  have hcs := cellSum_le j hx certAlphas 1 (by omega)
    (by rw [alphas_len_ok]; norm_num [certN])
  rw [alphas_len_ok] at hcs
  have hsum_eq : ∑ idx ∈ Finset.range 66,
      (listGetZ certAlphas idx : ℝ) * Real.cos (2 * Real.pi * ((1 + idx : ℕ) : ℝ) * x) =
      ∑ k ∈ Finset.Icc 1 66, (alphaFn k : ℝ) * Real.cos (2 * Real.pi * (k : ℝ) * x) := by
    refine Finset.sum_bij (fun idx _ => idx + 1) ?_ ?_ ?_ ?_
    · intro idx hidx
      simp only [Finset.mem_range] at hidx
      simp only [Finset.mem_Icc]
      omega
    · intro a₁ _ a₂ _ h; omega
    · intro k hk
      simp only [Finset.mem_Icc] at hk
      refine ⟨k - 1, Finset.mem_range.mpr (by omega), by omega⟩
    · intro idx hidx
      have hidx' : idx < certAlphas.length := by rw [alphas_len_ok]; exact Finset.mem_range.mp hidx
      rw [halphas_match idx hidx', Nat.add_comm 1 idx]
  rw [hsum_eq] at hcs
  have hcombined : ((certMinCellNum : ℤ) : ℝ) ≤
      (certMcos : ℝ) * ∑ k ∈ Finset.Icc 1 66, (alphaFn k : ℝ) * Real.cos (2 * Real.pi * (k : ℝ) * x) :=
    hcell_int.trans hcs
  dsimp [certMinCellNum, certMcos, certNumConst] at hcombined ⊢
  norm_num at hcombined
  linarith

theorem cert80_cell_bound :
    ∀ (j : ℕ), j < 80 → ∀ x ∈ Set.Icc ((j : ℝ) / (4 * 80)) (((j : ℝ) + 1) / (4 * 80)),
      (12976 : ℝ) / 10000 ≤
        (certNumConst : ℝ) / (2 * (100000 : ℝ) ^ 5) +
          (∑ k ∈ Finset.Icc 1 66, (alphaFn k : ℝ) * Real.cos (2 * Real.pi * (k : ℝ) * x)) /
            (2 * (100000 : ℝ) ^ 4) := by
  intro j hj x hx
  have hexact := cert80_cell_bound_exact j hj x hx
  linarith

/- ### 4. Packaged Certificate Hypotheses for Part 1 Merge -/

theorem cert80_vf_length : ∀ row ∈ cert_vf, row.length = 65 + 1 := by
  have h := vf_len_ok
  rw [List.all_eq_true] at h
  intro row hrow
  exact Nat.beq_eq.mp (h row hrow)

theorem cert80_vnu_length : ∀ row ∈ cert_vnu, row.length = 65 + 1 := by
  have h := vnu_len_ok
  rw [List.all_eq_true] at h
  intro row hrow
  exact Nat.beq_eq.mp (h row hrow)

theorem cert80_vg_length : ∀ row ∈ cert_vg, row.length = 65 + 1 := by
  have h := vg_len_ok
  rw [List.all_eq_true] at h
  intro row hrow
  exact Nat.beq_eq.mp (h row hrow)

private lemma band_all_65 (rows : List (List ℤ)) (fn : ℕ → ℤ)
    (h0 : checkBandRange rows fn 0 22 = true)
    (h1 : checkBandRange rows fn 22 22 = true)
    (h2 : checkBandRange rows fn 44 22 = true) :
    ∀ k ≤ 65, bandSumRows k rows = fn k := by
  intro k hk
  rcases lt_or_ge k 22 with hk0 | hk0
  · exact checkBandRange_sound rows fn 0 22 h0 k (by omega) hk0
  · rcases lt_or_ge k 44 with hk1 | hk1
    · exact checkBandRange_sound rows fn 22 22 h1 k hk0 hk1
    · exact checkBandRange_sound rows fn 44 22 h2 k hk1 (by omega)

theorem cert80_sf_eq : ∀ k ≤ 65, bandSumRows k cert_vf = sfFn k :=
  band_all_65 cert_vf sfFn sf_0_ok sf_1_ok sf_2_ok

theorem cert80_snu_eq : ∀ k ≤ 65, bandSumRows k cert_vnu = snuFn k :=
  band_all_65 cert_vnu snuFn snu_0_ok snu_1_ok snu_2_ok

theorem cert80_sg_eq : ∀ k ≤ 65, bandSumRows k cert_vg = sgFn k :=
  band_all_65 cert_vg sgFn sg_0_ok sg_1_ok sg_2_ok

private lemma alphas_ok_parts :
    checkAlphaTail (certK + 1) = true ∧ checkAlphaListMatch 1 certAlphas = true ∧
      checkConstEq = true := by
  have h := alphas_ok
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem cert80_mu_nonneg : 0 ≤ certD ^ 2 - sgFn 0 := by
  have h := alphas_ok_parts.2.2
  dsimp [checkConstEq] at h
  rw [Bool.and_eq_true, intLe_iff] at h
  simpa [sq] using h.1

theorem cert80_A_nonneg :
    ∀ k, 1 ≤ k → k ≤ 65 →
      0 ≤ 4 * (certD ^ 2 - sgFn 0) * rFn k + certD * sgFn k := by
  intro k hk1 hk2
  have hent := checkAlphaTail_sound (certK + 1) alphas_ok_parts.1 k hk1
    (by dsimp [certK]; omega)
  dsimp [checkAlphaEntry] at hent
  have hble : Nat.ble k certK = true := Nat.ble_eq.mpr (by dsimp [certK]; exact hk2)
  rw [hble] at hent
  simp only [↓reduceIte, Bool.and_eq_true, intLe_iff] at hent
  simpa [sq] using hent.1

theorem cert80_alpha_le :
    ∀ k, 1 ≤ k → k ≤ 65 →
      alphaFn k = 4 * (4 * (certD ^ 2 - sgFn 0) * rFn k + certD * sgFn k) * mFn k -
        2 * certD ^ 2 * sfFn k -
        (if k = 1 then 2 * certD ^ 2 * snuFn 0 + certD ^ 2 * snuFn 2
         else if k ≤ 65 - 1 then certD ^ 2 * (snuFn (k - 1) + snuFn (k + 1))
         else certD ^ 2 * snuFn (65 - 1)) := by
  intro k hk1 hk2
  have hent := checkAlphaTail_sound (certK + 1) alphas_ok_parts.1 k hk1
    (by dsimp [certK]; omega)
  dsimp [checkAlphaEntry] at hent
  have hble : Nat.ble k certK = true := Nat.ble_eq.mpr (by dsimp [certK]; exact hk2)
  rw [hble] at hent
  simp only [↓reduceIte, Bool.and_eq_true, intEq_iff] at hent
  have heq := hent.2
  by_cases hk_1 : k = 1
  · subst hk_1
    rw [if_pos rfl]
    simp only [nat_beq_self, ↓reduceIte] at heq
    rw [heq]; ring
  · have hb1 : Nat.beq k 1 = false := nat_beq_false hk_1
    rw [if_neg hk_1]
    by_cases hk_64 : k ≤ 65 - 1
    · have hb2 : Nat.ble k (certK - 1) = true := Nat.ble_eq.mpr (by dsimp [certK]; exact hk_64)
      rw [if_pos hk_64]
      rw [hb1, hb2] at heq
      simp only [Bool.false_eq_true, ↓reduceIte] at heq
      rw [heq]; ring
    · have hb2 : Nat.ble k (certK - 1) = false := nat_ble_false (by dsimp [certK]; exact hk_64)
      rw [if_neg hk_64]
      rw [hb1, hb2] at heq
      simp only [Bool.false_eq_true, ↓reduceIte] at heq
      dsimp only [certK] at heq
      rw [heq]; ring

theorem cert80_alpha_top :
    alphaFn (65 + 1) = -(certD ^ 2 * snuFn 65) := by
  have hent := checkAlphaTail_sound (certK + 1) alphas_ok_parts.1 66 (by omega) (by decide)
  dsimp [checkAlphaEntry] at hent
  have hble : Nat.ble 66 certK = false := by decide
  rw [hble] at hent
  simp only [Bool.false_eq_true, ↓reduceIte, intEq_iff] at hent
  dsimp only [certK] at hent
  rw [show (65 + 1 : ℕ) = 66 by rfl, hent]
  ring

theorem cert80_numConst_eq :
    certNumConst =
      2 * certD ^ 5 -
        4 * certD * (certD ^ 2 - sgFn 0) * (∑ k ∈ Finset.Icc 1 65, (rFn k) ^ 2) -
        2 * (∑ k ∈ Finset.Icc 1 65,
          (4 * (certD ^ 2 - sgFn 0) * rFn k + certD * sgFn k) * (mFn k) ^ 2) +
        2 * certD ^ 2 * (∑ k ∈ Finset.Icc 1 65,
          min (4 * (certD ^ 2 - sgFn 0) * rFn k - certD * sgFn k) 0) -
        2 * certD ^ 3 * sfFn 0 - certD ^ 3 * snuFn 1 := by
  have h := alphas_ok_parts.2.2
  dsimp [checkConstEq] at h
  rw [sumTermsAux_eq] at h
  dsimp only [certK] at h
  rw [Bool.and_eq_true, intEq_iff] at h
  have heq := h.2
  simp only [zero_add] at heq
  rw [heq]
  ring

structure Cert80Hypotheses : Prop where
  vf_len : ∀ row ∈ cert_vf, row.length = 65 + 1
  vnu_len : ∀ row ∈ cert_vnu, row.length = 65 + 1
  vg_len : ∀ row ∈ cert_vg, row.length = 65 + 1
  sf_eq : ∀ k ≤ 65, bandSumRows k cert_vf = sfFn k
  snu_eq : ∀ k ≤ 65, bandSumRows k cert_vnu = snuFn k
  sg_eq : ∀ k ≤ 65, bandSumRows k cert_vg = sgFn k
  mu_nonneg : 0 ≤ certD ^ 2 - sgFn 0
  A_nonneg : ∀ k, 1 ≤ k → k ≤ 65 → 0 ≤ 4 * (certD ^ 2 - sgFn 0) * rFn k + certD * sgFn k
  alpha_le : ∀ k, 1 ≤ k → k ≤ 65 →
    alphaFn k = 4 * (4 * (certD ^ 2 - sgFn 0) * rFn k + certD * sgFn k) * mFn k -
      2 * certD ^ 2 * sfFn k -
      (if k = 1 then 2 * certD ^ 2 * snuFn 0 + certD ^ 2 * snuFn 2
       else if k ≤ 65 - 1 then certD ^ 2 * (snuFn (k - 1) + snuFn (k + 1))
       else certD ^ 2 * snuFn (65 - 1))
  alpha_top : alphaFn (65 + 1) = -(certD ^ 2 * snuFn 65)
  numConst_eq : certNumConst =
    2 * certD ^ 5 -
      4 * certD * (certD ^ 2 - sgFn 0) * (∑ k ∈ Finset.Icc 1 65, (rFn k) ^ 2) -
      2 * (∑ k ∈ Finset.Icc 1 65,
        (4 * (certD ^ 2 - sgFn 0) * rFn k + certD * sgFn k) * (mFn k) ^ 2) +
      2 * certD ^ 2 * (∑ k ∈ Finset.Icc 1 65,
        min (4 * (certD ^ 2 - sgFn 0) * rFn k - certD * sgFn k) 0) -
      2 * certD ^ 3 * sfFn 0 - certD ^ 3 * snuFn 1
  cell_bound : ∀ (j : ℕ), j < 80 → ∀ x ∈ Set.Icc ((j : ℝ) / (4 * (80 : ℕ))) (((j : ℝ) + 1) / (4 * (80 : ℕ))),
    (12976 : ℝ) / 10000 ≤
      (certNumConst : ℝ) / (2 * (certD : ℝ) ^ 5) +
        (∑ k ∈ Finset.Icc 1 (65 + 1), (alphaFn k : ℝ) * Real.cos (2 * Real.pi * (k : ℝ) * x)) /
          (2 * (certD : ℝ) ^ 4)

theorem cert80_hypotheses : Cert80Hypotheses :=
  { vf_len := cert80_vf_length
    vnu_len := cert80_vnu_length
    vg_len := cert80_vg_length
    sf_eq := cert80_sf_eq
    snu_eq := cert80_snu_eq
    sg_eq := cert80_sg_eq
    mu_nonneg := cert80_mu_nonneg
    A_nonneg := cert80_A_nonneg
    alpha_le := cert80_alpha_le
    alpha_top := cert80_alpha_top
    numConst_eq := cert80_numConst_eq
    cell_bound := fun j hj x hx => by
      dsimp only [certD]
      simpa using cert80_cell_bound j hj x (by simpa using hx) }

theorem c1a_ge_cert80_exact :
    (4055172655215574821001279 / 3125000000000000000000000 : ℝ) ≤ C1a :=
  c1a_ge_of_sos_certificate
    65 80 (by omega) (by omega)
    certD 4055172655215574821001279 3125000000000000000000000 certNumConst
    (by decide) (by decide) (by decide)
    cert_vf cert_vnu cert_vg
    sfFn snuFn sgFn rFn mFn alphaFn
    cert80_vf_length cert80_vnu_length cert80_vg_length
    cert80_sf_eq cert80_snu_eq cert80_sg_eq
    cert80_mu_nonneg cert80_A_nonneg cert80_alpha_le cert80_alpha_top cert80_numConst_eq
    (fun j hj x hx => by
      dsimp only [certD]
      simpa using cert80_cell_bound_exact j hj x (by simpa using hx))

theorem c1a_ge_12976 : (12976 / 10000 : ℝ) ≤ C1a := by
  linarith [c1a_ge_cert80_exact]

theorem c1a_lower_bound : (1.2748 : ℝ) ≤ C1a := by
  linarith [c1a_ge_12976]

theorem mem_Ioc_c1a : mem_Ioc_c1a_answer ∈ Set.Ioc 1.292 C1a := by
  dsimp [mem_Ioc_c1a_answer]
  exact ⟨by norm_num, c1a_ge_12976⟩

end CertSoundness

section AnalyticAndSidon

open MeasureTheory Set
open scoped BigOperators ENNReal

/- ### 5. Unified WideCell Convolution, Step-50 Upper Bound & Sidon Bridge -/

noncomputable def wideCell (h i x : ℝ) : ℝ :=
  (Set.Icc i (i + h)).indicator (fun _ => (1 : ℝ)) x

lemma wideCell_nonneg (h i x : ℝ) : 0 ≤ wideCell h i x := by
  classical
  by_cases hx : x ∈ Set.Icc i (i + h) <;> simp [wideCell, hx]

lemma integrable_wideCell (h i : ℝ) : Integrable (wideCell h i) :=
  (integrableOn_const (C := (1 : ℝ)) (by simp [Real.volume_Icc])).integrable_indicator
    measurableSet_Icc

lemma integral_wideCell (h i : ℝ) (hh : 0 ≤ h) : (∫ x, wideCell h i x) = h := by
  change (∫ x, (Set.Icc i (i + h)).indicator (fun _ => (1 : ℝ)) x) = h
  rw [integral_indicator_const _ measurableSet_Icc, smul_eq_mul, mul_one,
    Real.volume_real_Icc_of_le (by linarith)]
  ring

lemma memLp_wideCell (h i : ℝ) (p : ℝ≥0∞) : MemLp (wideCell h i) p :=
  memLp_indicator_const p measurableSet_Icc 1 (Or.inr (by simp [Real.volume_Icc]))

lemma intervalIntegral_wideCell (h i a b : ℝ) (hh : 0 ≤ h)
    (ha : a ≤ i) (hb : i + h ≤ b) : (∫ x in a..b, wideCell h i x) = h := by
  have hab : a ≤ b := ha.trans ((le_add_of_nonneg_right hh).trans hb)
  rw [intervalIntegral.integral_of_le hab, ← integral_indicator measurableSet_Ioc]
  calc
    (∫ x, (Set.Ioc a b).indicator (wideCell h i) x) = ∫ x, wideCell h i x := by
      apply integral_congr_ae
      filter_upwards [(volume : Measure ℝ).ae_ne a] with x hxa
      by_cases hx : x ∈ Set.Icc i (i + h)
      · have hx' : x ∈ Set.Ioc a b :=
          ⟨lt_of_le_of_ne (ha.trans hx.1) hxa.symm, hx.2.trans hb⟩
        simp [hx']
      · simp [wideCell, hx, Set.indicator_apply]
    _ = h := integral_wideCell h i hh

private theorem wideCell_product (h T i j : ℝ) :
    (fun x => wideCell h i (T - x) * wideCell h j x) =
      (Set.Icc (max (T - (i + h)) j) (min (T - i) (j + h))).indicator
        (fun _ => (1 : ℝ)) := by
  classical
  funext x
  have hx : x ∈ Set.Icc (max (T - (i + h)) j) (min (T - i) (j + h)) ↔
      T - x ∈ Set.Icc i (i + h) ∧ x ∈ Set.Icc j (j + h) := by
    simp only [Set.mem_Icc, max_le_iff, le_min_iff]
    constructor
    · rintro ⟨⟨h₁, h₂⟩, h₃, h₄⟩
      exact ⟨⟨by linarith, by linarith⟩, h₂, h₄⟩
    · rintro ⟨⟨h₁, h₂⟩, h₃, h₄⟩
      exact ⟨⟨by linarith, h₃⟩, by linarith, h₄⟩
  by_cases h₁ : T - x ∈ Set.Icc i (i + h) <;>
    by_cases h₂ : x ∈ Set.Icc j (j + h) <;> simp [wideCell, hx, h₁, h₂]

lemma integrable_wideCell_product (h T i j : ℝ) :
    Integrable (fun x => wideCell h i (T - x) * wideCell h j x) := by
  rw [wideCell_product]
  exact (integrableOn_const (C := (1 : ℝ)) (by simp [Real.volume_Icc])).integrable_indicator
    measurableSet_Icc

lemma integral_wideCell_product (h T i j : ℝ) :
    (∫ x, wideCell h i (T - x) * wideCell h j x) = max 0 (h - |T - (i + j + h)|) := by
  change (∫ x, (fun x => wideCell h i (T - x) * wideCell h j x) x) = _
  rw [wideCell_product, integral_indicator_const _ measurableSet_Icc, smul_eq_mul, mul_one,
    Real.volume_real_Icc, max_comm]
  congr 1
  rcases le_total T (i + j + h) with hT | hT
  · rw [abs_of_nonpos (by linarith : T - (i + j + h) ≤ 0),
      min_eq_left (by linarith : T - i ≤ j + h),
      max_eq_right (by linarith : T - (i + h) ≤ j)]
    ring
  · rw [abs_of_nonneg (by linarith : 0 ≤ T - (i + j + h)),
      min_eq_right (by linarith : j + h ≤ T - i),
      max_eq_left (by linarith : j ≤ T - (i + h))]
    ring

lemma integral_gridCell_product (a h T i j : ℝ) (hh : 0 < h) :
    (∫ x, wideCell h (a + h * i) (T - x) * wideCell h (a + h * j) x) =
      h * max 0 (1 - |(T - 2 * a) / h - (i + j + 1)|) := by
  rw [integral_wideCell_product, mul_max_of_nonneg _ _ hh.le, mul_zero]
  have he : T - (a + h * i + (a + h * j) + h) =
      h * ((T - 2 * a) / h - (i + j + 1)) := by
    field_simp [hh.ne']
    ring
  rw [he, abs_mul, abs_of_nonneg hh.le, mul_sub, mul_one]

lemma triangle_grid (i j k : ℤ) (θ : ℝ) (h₀ : 0 ≤ θ) (h₁ : θ ≤ 1) :
    max 0 (1 - |(k : ℝ) + θ - ((i : ℝ) + (j : ℝ) + 1)|) =
      (if i + j = k then θ else 0) + (if i + j = k - 1 then 1 - θ else 0) := by
  by_cases he : i + j = k
  · have hc : (i : ℝ) + (j : ℝ) = (k : ℝ) := by exact_mod_cast he
    rw [if_pos he, if_neg (by omega), add_zero, hc]
    rw [abs_of_nonpos (by linarith : (k : ℝ) + θ - ((k : ℝ) + 1) ≤ 0),
      max_eq_right (by linarith)]
    ring
  · by_cases he' : i + j = k - 1
    · have hc : (i : ℝ) + (j : ℝ) = (k : ℝ) - 1 := by exact_mod_cast he'
      rw [if_neg he, if_pos he', zero_add, hc]
      rw [abs_of_nonneg (by linarith : 0 ≤ (k : ℝ) + θ - ((k : ℝ) - 1 + 1)),
        max_eq_right (by linarith)]
      ring
    · rw [if_neg he, if_neg he', add_zero]
      apply max_eq_left
      rcases le_total (i + j) k with h | h
      · have hc : (i : ℝ) + (j : ℝ) + 2 ≤ (k : ℝ) := by
          exact_mod_cast (show i + j + 2 ≤ k by omega)
        rw [abs_of_nonneg (by linarith : 0 ≤ (k : ℝ) + θ - ((i : ℝ) + j + 1))]
        linarith
      · have hc : (k : ℝ) + 1 ≤ (i : ℝ) + (j : ℝ) := by
          exact_mod_cast (show k + 1 ≤ i + j by omega)
        rw [abs_of_nonpos (by linarith : (k : ℝ) + θ - ((i : ℝ) + j + 1) ≤ 0)]
        linarith

def discCoeff (n : ℕ) (w : ℕ → ℕ) (k : ℤ) : ℕ :=
  ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, if (i : ℤ) + j = k then w i * w j else 0

noncomputable def weightedCells (n : ℕ) (w : ℕ → ℕ) (a h x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, (w i : ℝ) * wideCell h (a + h * i) x

lemma weightedCells_convolution_le (n : ℕ) (w : ℕ → ℕ) (a h : ℝ) (hh : 0 < h) (U : ℝ)
    (hU : ∀ k : ℤ, (discCoeff n w k : ℝ) ≤ U) (T : ℝ) :
    (∫ x, weightedCells n w a h (T - x) * weightedCells n w a h x) ≤ h * U := by
  let f (i j : ℕ) (x : ℝ) :=
    (w i : ℝ) * (w j : ℝ) *
      (wideCell h (a + h * i) (T - x) * wideCell h (a + h * j) x)
  have hfi (i j : ℕ) : Integrable (f i j) :=
    (integrable_wideCell_product h T (a + h * i) (a + h * j)).const_mul _
  have hsum (i : ℕ) : Integrable (fun x => ∑ j ∈ Finset.range n, f i j x) :=
    integrable_finsetSum _ (fun j _ => hfi i j)
  let Y := (T - 2 * a) / h
  let k : ℤ := ⌊Y⌋
  let θ := Y - (k : ℝ)
  have hθ₀ : 0 ≤ θ := sub_nonneg.mpr (Int.floor_le Y)
  have hθ₁ : θ ≤ 1 := (Int.fract_lt_one Y).le
  have hY : (T - 2 * a) / h = (k : ℝ) + θ := by dsimp [θ, Y]; ring
  let g (k : ℤ) (i j : ℕ) : ℝ := if (i : ℤ) + j = k then (w i : ℝ) * (w j : ℝ) else 0
  have hCoeff (k : ℤ) : (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, g k i j) =
      (discCoeff n w k : ℝ) := by
    simp [discCoeff, g]
  have hterm (i j : ℕ) :
      (∫ x, f i j x) = h * (g k i j * θ + g (k - 1) i j * (1 - θ)) := by
    dsimp only [f]
    rw [integral_const_mul, integral_gridCell_product a h T (i : ℝ) (j : ℝ) hh, hY]
    rw [show (i : ℝ) = ((i : ℤ) : ℝ) by norm_cast,
      show (j : ℝ) = ((j : ℤ) : ℝ) by norm_cast, triangle_grid _ _ _ θ hθ₀ hθ₁]
    dsimp only [g]
    split_ifs <;> ring
  calc
    (∫ x, weightedCells n w a h (T - x) * weightedCells n w a h x) =
        ∫ x, ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, f i j x := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      simp only [weightedCells, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      dsimp [f]
      ring
    _ = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, ∫ x, f i j x := by
      rw [integral_finsetSum _ (fun i _ => hsum i)]
      exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ (fun j _ => hfi i j)
    _ = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        h * (g k i j * θ + g (k - 1) i j * (1 - θ)) := by
      simp_rw [hterm]
    _ = h * ((discCoeff n w k : ℝ) * θ + (discCoeff n w (k - 1) : ℝ) * (1 - θ)) := by
      simp only [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul, hCoeff]
    _ ≤ h * U := by
      apply mul_le_mul_of_nonneg_left _ hh.le
      calc
        _ ≤ U * θ + U * (1 - θ) :=
          add_le_add (mul_le_mul_of_nonneg_right (hU k) hθ₀)
            (mul_le_mul_of_nonneg_right (hU (k - 1)) (sub_nonneg.mpr hθ₁))
        _ = U := by ring

theorem c1a_mul_sum_sq_le_two_mul_conv (n : ℕ) (hn : 1 ≤ n) (w : ℕ → ℕ) (U : ℕ)
    (hU : ∀ k : ℤ, discCoeff n w k ≤ U) :
    C1a * (∑ i ∈ Finset.range n, (w i : ℝ)) ^ 2 ≤ 2 * (n : ℝ) * (U : ℝ) := by
  by_cases hS0 : (∑ i ∈ Finset.range n, w i) = 0
  · have hSr : (∑ i ∈ Finset.range n, (w i : ℝ)) = 0 := by exact_mod_cast hS0
    rw [hSr]
    norm_num
    positivity
  have hSpos : 0 < ∑ i ∈ Finset.range n, (w i : ℝ) := by
    have h1 : 0 < ∑ i ∈ Finset.range n, w i := Nat.pos_of_ne_zero hS0
    exact_mod_cast h1
  let h : ℝ := 1 / (2 * (n : ℝ))
  have hh : 0 < h := by dsimp [h]; positivity
  let f : ℝ → ℝ := weightedCells n w (-1 / 4) h
  have hf_nonneg : 0 ≤ f := by
    intro x
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (Nat.cast_nonneg _) (wideCell_nonneg h _ x)
  have hf_memLp : MemLp f 2 :=
    memLp_finsetSum _ fun i _ => (memLp_wideCell h _ 2).const_mul _
  have hf_mass : (∫ x in (-1 / 4 : ℝ)..(1 / 4), f x) =
      h * ∑ i ∈ Finset.range n, (w i : ℝ) := by
    dsimp [f, weightedCells]
    rw [intervalIntegral.integral_finsetSum]
    · calc
        (∑ i ∈ Finset.range n, ∫ x in (-1 / 4 : ℝ)..(1 / 4),
            (w i : ℝ) * wideCell h (-1 / 4 + h * i) x)
          = ∑ i ∈ Finset.range n, (w i : ℝ) * h := by
            refine Finset.sum_congr rfl fun i hi => ?_
            have hi' : i < n := Finset.mem_range.mp hi
            rw [intervalIntegral.integral_const_mul, intervalIntegral_wideCell]
            · exact hh.le
            · have : 0 ≤ h * (i : ℝ) := mul_nonneg hh.le (Nat.cast_nonneg i)
              linarith
            · have hi1 : (i : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hi'
              have hn0 : (n : ℝ) ≠ 0 := by positivity
              have hle : h * (i : ℝ) + h ≤ 1 / 2 := by
                have heq : h * (i : ℝ) + h = ((i : ℝ) + 1) / (2 * (n : ℝ)) := by
                  dsimp [h]; field_simp [hn0]
                rw [heq, div_le_iff₀ (by positivity)]
                linarith
              linarith
        _ = h * ∑ i ∈ Finset.range n, (w i : ℝ) := by
            rw [← Finset.sum_mul, mul_comm]
    · intro i _
      exact ((integrable_wideCell h _).const_mul _).intervalIntegrable
  have hf_conv : ∀ t : ℝ, (∫ x, f (t - x) * f x) ≤ h * (U : ℝ) := fun t =>
    weightedCells_convolution_le n w (-1 / 4) h hh (U : ℝ) (fun k => by exact_mod_cast hU k) t
  have hSup : sSup {∫ x, f (t - x) * f x | t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2)} ≤ h * (U : ℝ) := by
    refine csSup_le ⟨_, ⟨0, by norm_num, rfl⟩⟩ ?_
    rintro _ ⟨t, _, rfl⟩
    exact hf_conv t
  have hS_nonempty : {C : ℝ | ∀ ⦃F : ℝ → ℝ⦄, 0 ≤ F → MemLp F 2 →
      C * (∫ x in (-1 / 4)..(1 / 4), F x) ^ 2 ≤
        sSup {∫ x, F (t - x) * F x | t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2)}}.Nonempty := by
    refine ⟨0, fun F hF _ => ?_⟩
    rw [zero_mul]
    apply Real.sSup_nonneg
    rintro _ ⟨t, _, rfl⟩
    exact integral_nonneg fun x => mul_nonneg (hF (t - x)) (hF x)
  set Sw := ∑ i ∈ Finset.range n, (w i : ℝ)
  have hC_bound : C1a ≤ 2 * (n : ℝ) * (U : ℝ) / Sw ^ 2 := by
    unfold C1a
    refine csSup_le hS_nonempty ?_
    intro C hC
    have h1 := (hC hf_nonneg hf_memLp).trans hSup
    rw [hf_mass] at h1
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have hhn : h * (2 * (n : ℝ)) = 1 := by
      dsimp [h]
      field_simp [hn0]
    have h2 : C * Sw ^ 2 ≤ 2 * (n : ℝ) * (U : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_right h1 (by positivity : 0 ≤ (2 * (n : ℝ)) ^ 2)
      calc
        C * Sw ^ 2 = C * ((h * (2 * (n : ℝ))) * Sw) ^ 2 := by rw [hhn, one_mul]
        _ = C * (h * Sw) ^ 2 * (2 * (n : ℝ)) ^ 2 := by ring
        _ ≤ (h * (U : ℝ)) * (2 * (n : ℝ)) ^ 2 := hmul
        _ = (h * (2 * (n : ℝ))) * (2 * (n : ℝ) * (U : ℝ)) := by ring
        _ = 2 * (n : ℝ) * (U : ℝ) := by rw [hhn, one_mul]
    exact (le_div_iff₀ (sq_pos_of_pos hSpos)).mpr h2
  exact (le_div_iff₀ (sq_pos_of_pos hSpos)).mp hC_bound

def listAtNat : List ℕ → ℕ → ℕ
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, n + 1 => listAtNat xs n

def step50List : List ℕ :=
  [4546, 25, 3766, 1542, 3993, 1798, 3609, 1858, 3437, 1441,
   4868, 2485, 3514, 2195, 4648, 1599, 1582, 5439, 2175, 1825,
   401, 5, 6, 4, 520, 568, 586, 3647, 4997, 2538,
   2520, 2, 1231, 3193, 751, 1370, 1758, 1214, 5, 285,
   667, 5, 21, 22, 52, 3, 1109, 2221, 7412, 6544]

def step50W (i : ℕ) : ℕ := listAtNat step50List i

def fastConv (n : ℕ) (w : ℕ → ℕ) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, if i ≤ k ∧ k - i < n then w i * w (k - i) else 0

def convLoop (w : ℕ → ℕ) (n k : ℕ) : ℕ → ℕ → ℕ
  | 0, acc => acc
  | m + 1, acc =>
    let term := if m ≤ k ∧ k - m < n then w m * w (k - m) else 0
    convLoop w n k m (acc + term)

lemma convLoop_eq (w : ℕ → ℕ) (n k : ℕ) :
    ∀ m acc, convLoop w n k m acc =
      acc + ∑ i ∈ Finset.range m, if i ≤ k ∧ k - i < n then w i * w (k - i) else 0 := by
  intro m
  induction m with
  | zero => intro acc; simp [convLoop]
  | succ m ih =>
    intro acc
    dsimp [convLoop]
    rw [ih, Finset.sum_range_succ]
    omega

lemma discCoeff_nat_eq_fastConv (n : ℕ) (w : ℕ → ℕ) (k : ℕ) :
    discCoeff n w (k : ℤ) = fastConv n w k := by
  dsimp [discCoeff, fastConv]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hin : i < n := Finset.mem_range.mp hi
  by_cases h : i ≤ k ∧ k - i < n
  · rw [if_pos h]
    rw [Finset.sum_eq_single (k - i)]
    · rw [if_pos (by omega)]
    · intro j _ hj; rw [if_neg (by omega)]
    · intro hmem; exact absurd (Finset.mem_range.mpr h.2) hmem
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun j hj => ?_
    have hjn : j < n := Finset.mem_range.mp hj
    rw [if_neg (by omega)]

def checkConvRange (w : ℕ → ℕ) (n U : ℕ) : ℕ → Bool
  | 0 => true
  | k + 1 => if Nat.ble (convLoop w n k n 0) U then checkConvRange w n U k else false

lemma checkConvRange_sound (w : ℕ → ℕ) (n U : ℕ) :
    ∀ K, checkConvRange w n U K = true → ∀ k < K, convLoop w n k n 0 ≤ U := by
  intro K
  induction K with
  | zero => intro _ k hk; omega
  | succ K ih =>
    intro h k hk
    dsimp [checkConvRange] at h
    split_ifs at h with hle
    by_cases heq : k = K
    · subst heq; exact Nat.ble_eq.mp hle
    · exact ih h k (by omega)

def sumNatLoop (w : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, acc => acc
  | m + 1, acc => sumNatLoop w m (acc + w m)

lemma sumNatLoop_eq (w : ℕ → ℕ) :
    ∀ m acc, sumNatLoop w m acc = acc + ∑ i ∈ Finset.range m, w i := by
  intro m
  induction m with
  | zero => intro acc; simp [sumNatLoop]
  | succ m ih =>
    intro acc
    dsimp [sumNatLoop]
    rw [ih, Finset.sum_range_succ]
    omega

private theorem step50_sum_ok : sumNatLoop step50W 50 0 = 100002 := by decide

private theorem step50_conv_ok : checkConvRange step50W 50 152050474 99 = true := by decide

theorem c1a_le_step50 : C1a ≤ 3801261850 / 2500100001 := by
  have hsum : (∑ i ∈ Finset.range 50, (step50W i : ℝ)) = 100002 := by
    have hnat : ∑ i ∈ Finset.range 50, step50W i = 100002 := by
      have := sumNatLoop_eq step50W 50 0
      rw [step50_sum_ok, zero_add] at this
      exact this.symm
    exact_mod_cast hnat
  have hU : ∀ k : ℤ, discCoeff 50 step50W k ≤ 152050474 := by
    intro k
    by_cases hk0 : k < 0
    · have : discCoeff 50 step50W k = 0 := by
        dsimp [discCoeff]
        refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
        rw [if_neg (by omega)]
      omega
    · by_cases hk99 : (99 : ℤ) ≤ k
      · have : discCoeff 50 step50W k = 0 := by
          dsimp [discCoeff]
          refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => ?_
          have hi' := Finset.mem_range.mp hi
          have hj' := Finset.mem_range.mp hj
          rw [if_neg (by omega)]
        omega
      · have hk_nonneg : 0 ≤ k := not_lt.mp hk0
        obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk_nonneg
        have hm : m < 99 := by omega
        rw [discCoeff_nat_eq_fastConv]
        have hconv := convLoop_eq step50W 50 m 50 0
        rw [zero_add] at hconv
        change fastConv 50 step50W m ≤ 152050474
        dsimp [fastConv]
        rw [← hconv]
        exact checkConvRange_sound step50W 50 152050474 99 step50_conv_ok m hm
  have hmain := c1a_mul_sum_sq_le_two_mul_conv 50 (by omega) step50W 152050474 hU
  rw [hsum] at hmain
  norm_num at hmain
  linarith

theorem c1a_le_1521 : C1a ≤ 1521 / 1000 := by
  linarith [c1a_le_step50]

theorem c1a_lt_pi_div_two : C1a < Real.pi / 2 := by
  linarith [c1a_le_1521, Real.pi_gt_d4]

/- ### 6. Discrete-to-Continuous B2[g]-Sidon Set Bridge -/

def IsGSidon (g : ℕ) (A : Finset ℕ) : Prop :=
  ∀ s : ℕ, ((A ×ˢ A).filter (fun ab => ab.1 + ab.2 = s)).card ≤ g

def IsSidonFinset (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A, a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

instance instDecidableIsSidonFinset (A : Finset ℕ) : Decidable (IsSidonFinset A) := by
  unfold IsSidonFinset
  infer_instance

theorem IsSidonFinset.isGSidon_two {A : Finset ℕ} (hA : IsSidonFinset A) : IsGSidon 2 A := by
  intro s
  set S := (A ×ˢ A).filter (fun ab => ab.1 + ab.2 = s)
  rcases S.eq_empty_or_nonempty with hemp | ⟨⟨a, b⟩, hab⟩
  · simp [hemp]
  have hab_mem := Finset.mem_filter.mp hab
  have haA : a ∈ A := (Finset.mem_product.mp hab_mem.1).1
  have hbA : b ∈ A := (Finset.mem_product.mp hab_mem.1).2
  have hab_sum : a + b = s := hab_mem.2
  have hsub : S ⊆ {(a, b), (b, a)} := by
    rintro ⟨c, d⟩ hcd
    have hcd_mem := Finset.mem_filter.mp hcd
    have hcA : c ∈ A := (Finset.mem_product.mp hcd_mem.1).1
    have hdA : d ∈ A := (Finset.mem_product.mp hcd_mem.1).2
    have hcd_sum : c + d = s := hcd_mem.2
    rcases hA a haA b hbA c hcA d hdA (by omega) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp
    · simp
  exact (Finset.card_le_card hsub).trans Finset.card_le_two

theorem c1a_mul_card_sq_le_two_mul_g_sidon {N g : ℕ} {A : Finset ℕ}
    (hA_sub : ∀ a ∈ A, a < N) (hA_sidon : IsGSidon g A) :
    C1a * (A.card : ℝ) ^ 2 ≤ 2 * (g : ℝ) * (N : ℝ) := by
  by_cases hN0 : N = 0
  · subst hN0
    have hA_empty : A = ∅ := by
      ext a
      simp only [Finset.notMem_empty, iff_false]
      intro ha
      exact absurd (hA_sub a ha) (Nat.not_lt_zero a)
    simp [hA_empty]
  · have hN : 1 ≤ N := Nat.pos_of_ne_zero hN0
    let w : ℕ → ℕ := fun i => if i ∈ A then 1 else 0
    have hA_range : A ⊆ Finset.range N := fun a ha => Finset.mem_range.mpr (hA_sub a ha)
    have hsum : (∑ i ∈ Finset.range N, (w i : ℝ)) = (A.card : ℝ) := by
      have hnat : ∑ i ∈ Finset.range N, w i = A.card := by
        dsimp [w]
        rw [← Finset.sum_filter]
        have hflt : (Finset.range N).filter (fun i => i ∈ A) = A := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_range]
          exact ⟨fun h => h.2, fun h => ⟨hA_sub i h, h⟩⟩
        rw [hflt]
        simp
      exact_mod_cast hnat
    have hU : ∀ k : ℤ, discCoeff N w k ≤ g := by
      intro k
      by_cases hk0 : k < 0
      · have : discCoeff N w k = 0 := by
          dsimp [discCoeff]
          refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
          rw [if_neg (by omega)]
        omega
      · obtain ⟨s, rfl⟩ := Int.eq_ofNat_of_zero_le (not_lt.mp hk0)
        have hEq : discCoeff N w (s : ℤ) =
            ((A ×ˢ A).filter (fun ab => ab.1 + ab.2 = s)).card := by
          dsimp [discCoeff, w]
          rw [Finset.card_filter, Finset.sum_product]
          rw [← Finset.sum_subset hA_range]
          · refine Finset.sum_congr rfl fun i hi => ?_
            rw [← Finset.sum_subset hA_range]
            · refine Finset.sum_congr rfl fun j hj => ?_
              simp only [if_pos hi, if_pos hj, mul_one]
              by_cases hij : i + j = s
              · rw [if_pos (by exact_mod_cast hij), if_pos hij]
              · rw [if_neg (by omega), if_neg hij]
            · intro j _ hjA
              simp only [if_neg hjA, mul_zero, ite_self]
          · intro i _ hiA
            refine Finset.sum_eq_zero fun j _ => ?_
            simp only [if_neg hiA, zero_mul, ite_self]
        rw [hEq]
        exact hA_sidon s
    have hmain := c1a_mul_sum_sq_le_two_mul_conv N hN w g hU
    rw [hsum] at hmain
    linarith

theorem isSidonFinset_card_sq_le {N : ℕ} {A : Finset ℕ}
    (hA_sub : ∀ a ∈ A, a < N) (hA_sidon : IsSidonFinset A) :
    (A.card : ℝ) ^ 2 ≤ (2500 / 811 : ℝ) * (N : ℝ) := by
  have h := c1a_mul_card_sq_le_two_mul_g_sidon hA_sub hA_sidon.isGSidon_two
  have h1 : (12976 / 10000 : ℝ) * (A.card : ℝ) ^ 2 ≤ C1a * (A.card : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_right c1a_ge_12976 (sq_nonneg _)
  norm_num at h
  linarith

end AnalyticAndSidon

section NonVacuityExamples

/- ### 7. Non-Vacuity Sanity Checks on Concrete Witnesses -/

/-- Headline rational, benchmark, and Schinzel–Schmidt bounds on `C1a`. -/
example :
    (4055172655215574821001279 / 3125000000000000000000000 : ℝ) ≤ C1a ∧
    (12976 / 10000 : ℝ) ≤ C1a ∧
    (1.2748 : ℝ) ≤ C1a ∧
    mem_Ioc_c1a_answer ∈ Set.Ioc 1.292 C1a ∧
    C1a ≤ 3801261850 / 2500100001 ∧
    C1a ≤ 1521 / 1000 ∧
    C1a < Real.pi / 2 ∧
    1 ≤ C1a ∧ C1a ≤ 2 :=
  ⟨c1a_ge_cert80_exact, c1a_ge_12976, c1a_lower_bound, mem_Ioc_c1a,
   c1a_le_step50, c1a_le_1521, c1a_lt_pi_div_two, one_le_c1a, c1a_le_two⟩

/-- Concrete check of `bandSumRows` and `trigSqSum_eq_bandSum` on `[[3, -2, 1]]` (`K = 2`). -/
example :
    bandSumRows 0 [[3, -2, 1]] = 14 ∧
    bandSumRows 1 [[3, -2, 1]] = -16 ∧
    bandSumRows 2 [[3, -2, 1]] = 6 ∧
    0 ≤ trigSqSum 2 [[3, -2, 1]] (1 / 7) ∧
    trigSqSum 2 [[3, -2, 1]] (1 / 7) =
      14 + ∑ k ∈ Finset.Icc (1 : ℕ) 2,
        (bandSumRows k [[3, -2, 1]] : ℝ) * Real.cos (2 * Real.pi * (k : ℝ) * (1 / 7)) := by
  refine ⟨by decide, by decide, by decide, trigSqSum_nonneg 2 [[3, -2, 1]] (1 / 7), ?_⟩
  have h := trigSqSum_eq_bandSum 2 [[3, -2, 1]] (by simp) (1 / 7)
  have hb0 : (bandSumRows 0 [[3, -2, 1]] : ℝ) = 14 := by norm_cast
  rw [hb0] at h
  exact h

/-- Concrete evaluation of alternating Taylor brackets at `t = 1 / 2` and `pi_bounds_8d`. -/
example :
    1 - (1 / 2 : ℝ) ^ 2 / 2 + (1 / 2 : ℝ) ^ 4 / 24 - (1 / 2 : ℝ) ^ 6 / 720 ≤ Real.cos (1 / 2) ∧
    Real.cos (1 / 2) ≤
      1 - (1 / 2 : ℝ) ^ 2 / 2 + (1 / 2 : ℝ) ^ 4 / 24 - (1 / 2 : ℝ) ^ 6 / 720 +
        (1 / 2 : ℝ) ^ 8 / 40320 ∧
    (1 / 2 : ℝ) - (1 / 2 : ℝ) ^ 3 / 6 + (1 / 2 : ℝ) ^ 5 / 120 - (1 / 2 : ℝ) ^ 7 / 5040 ≤
      Real.sin (1 / 2) ∧
    Real.sin (1 / 2) ≤
      (1 / 2 : ℝ) - (1 / 2 : ℝ) ^ 3 / 6 + (1 / 2 : ℝ) ^ 5 / 120 - (1 / 2 : ℝ) ^ 7 / 5040 +
        (1 / 2 : ℝ) ^ 9 / 362880 ∧
    (314159265 : ℝ) / 100000000 < Real.pi ∧ Real.pi < (314159266 : ℝ) / 100000000 :=
  ⟨cos_taylor_deg6_le (by norm_num), cos_le_taylor_deg8 (by norm_num),
   sin_taylor_deg7_le (by norm_num), sin_le_taylor_deg9 (by norm_num),
   pi_bounds_8d.1, pi_bounds_8d.2⟩

/-- Concrete check of `cert80_cos_table_bounds` at `r = 20` (`π / 8`) and `cert80_cell_bound_exact`
at the tightest cell `j = 1`, `x = 1 / 200 ∈ [1 / 320, 2 / 320]`. -/
example :
    (9238795 : ℝ) / 10000000 ≤ Real.cos (Real.pi / 8) ∧
    Real.cos (Real.pi / 8) ≤ (9238796 : ℝ) / 10000000 ∧
    (4055172655215574821001279 : ℝ) / 3125000000000000000000000 ≤
      (certNumConst : ℝ) / (2 * (100000 : ℝ) ^ 5) +
        (∑ k ∈ Finset.Icc (1 : ℕ) 66,
          (alphaFn k : ℝ) * Real.cos (2 * Real.pi * (k : ℝ) * (1 / 200))) /
          (2 * (100000 : ℝ) ^ 4) := by
  have hcos := cert80_cos_table_bounds 20 (by decide)
  have hlo : cosLoFn 20 = 9238795 := by decide
  have hhi : cosHiFn 20 = 9238796 := by decide
  rw [hlo, hhi] at hcos
  dsimp [certMcos, certN] at hcos
  have harg : Real.pi * (20 : ℝ) / (2 * (80 : ℝ)) = Real.pi / 8 := by ring
  rw [harg] at hcos
  exact ⟨hcos.1, hcos.2, cert80_cell_bound_exact 1 (by omega) (1 / 200) (by norm_num)⟩

/-- Normalized indicator witness `f₀ = 2 · 1_{[-1/4, 1/4]}` exercising `autoconvValues_bddAbove`,
`autoconv_integral_Icc_eq_one`, `autoconv_fourier_cos`, `autoconv_fourier_sin`,
`finite_bessel_autoconv`, `gram_f_nonneg`, `gram_nu_nonneg`, and `gram_g_le`. -/
example :
    let f₀ : ℝ → ℝ := (Set.Icc (-1 / 4 : ℝ) (1 / 4)).indicator (fun _ => (2 : ℝ))
    BddAbove {∫ x, f₀ (t - x) * f₀ x | t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2)} ∧
    (∫ t in (-1 / 2 : ℝ)..(1 / 2), (∫ x, f₀ (t - x) * f₀ x)) = 1 ∧
    (∫ t in (-1 / 2 : ℝ)..(1 / 2), (∫ x, f₀ (t - x) * f₀ x) * Real.cos (2 * Real.pi * (1 : ℝ) * t)) =
      (∫ x, f₀ x * Real.cos (2 * Real.pi * (1 : ℝ) * x)) ^ 2 -
        (∫ x, f₀ x * Real.sin (2 * Real.pi * (1 : ℝ) * x)) ^ 2 ∧
    (∫ t in (-1 / 2 : ℝ)..(1 / 2), (∫ x, f₀ (t - x) * f₀ x) * Real.sin (2 * Real.pi * (1 : ℝ) * t)) =
      2 * (∫ x, f₀ x * Real.cos (2 * Real.pi * (1 : ℝ) * x)) *
        (∫ x, f₀ x * Real.sin (2 * Real.pi * (1 : ℝ) * x)) ∧
    2 * ∑ k ∈ Finset.Icc (1 : ℕ) 2,
      ((∫ x, f₀ x * Real.cos (2 * Real.pi * (k : ℝ) * x)) ^ 2 +
        (∫ x, f₀ x * Real.sin (2 * Real.pi * (k : ℝ) * x)) ^ 2) ^ 2 ≤ 2 - 1 ∧
    0 ≤ (bandSumRows 0 [[1, 1, 1]] : ℝ) +
      ∑ k ∈ Finset.Icc (1 : ℕ) 2,
        (bandSumRows k [[1, 1, 1]] : ℝ) * (∫ x, f₀ x * Real.cos (2 * Real.pi * (k : ℝ) * x)) ∧
    (∑ k ∈ Finset.Icc (1 : ℕ) 2, (bandSumRows k [[1, 1, 1]] : ℝ) *
      ((∫ x, f₀ x * Real.cos (2 * Real.pi * (k : ℝ) * x)) ^ 2 -
       (∫ x, f₀ x * Real.sin (2 * Real.pi * (k : ℝ) * x)) ^ 2)) ≤
      (bandSumRows 0 [[1, 1, 1]] : ℝ) * (2 - 1) := by
  intro f₀
  have hf0 : 0 ≤ f₀ := fun x => Set.indicator_nonneg (fun _ _ => by norm_num) x
  have hfm : MemLp f₀ 2 :=
    memLp_indicator_const 2 measurableSet_Icc (2 : ℝ) (Or.inr (by simp [Real.volume_Icc]))
  have hsupp : ∀ x ∉ Set.Icc (-1 / 4 : ℝ) (1 / 4), f₀ x = 0 :=
    fun x hx => Set.indicator_of_notMem hx _
  have hmass : ∫ x in Set.Icc (-1 / 4 : ℝ) (1 / 4), f₀ x = 1 := by
    dsimp [f₀]
    rw [setIntegral_indicator measurableSet_Icc, Set.inter_self, setIntegral_const, smul_eq_mul]
    simp [Measure.real, Real.volume_Icc]
    norm_num
  have hfint : Integrable f₀ := by
    have hIfin : IsFiniteMeasure (volume.restrict (Set.Icc (-1 / 4 : ℝ) (1 / 4))) :=
      ⟨by simp [Real.volume_Icc]⟩
    have hIint : IntegrableOn f₀ (Set.Icc (-1 / 4 : ℝ) (1 / 4)) :=
      (hfm.restrict (Set.Icc (-1 / 4 : ℝ) (1 / 4))).integrable (by norm_num)
    have hind : (Set.Icc (-1 / 4 : ℝ) (1 / 4)).indicator f₀ = f₀ := by
      ext x; simp [f₀]
    rw [← hind]
    exact (integrable_indicator_iff measurableSet_Icc).mpr hIint
  have hΩ : ∀ t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2), (∫ x, f₀ (t - x) * f₀ x) ≤ 2 := by
    intro t _
    have htm : MemLp (fun x => f₀ (t - x)) 2 :=
      hfm.comp_measurePreserving (volume.measurePreserving_sub_left t)
    calc
      ∫ x, f₀ (t - x) * f₀ x ≤ ∫ x, 2 * f₀ x := by
        apply integral_mono (htm.integrable_mul hfm) (hfint.const_mul 2)
        intro x
        have hle2 : f₀ (t - x) ≤ 2 :=
          Set.indicator_le' (fun _ _ => le_rfl) (fun _ _ => by norm_num) _
        exact mul_le_mul_of_nonneg_right hle2 (hf0 x)
      _ = 2 * ∫ x, f₀ x := integral_const_mul 2 f₀
      _ = 2 * ∫ x in Set.Icc (-1 / 4 : ℝ) (1 / 4), f₀ x := by
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero hsupp]
      _ = 2 := by rw [hmass]; norm_num
  have hcos1 := autoconv_fourier_cos f₀ hfm hsupp 1
  have hsin1 := autoconv_fourier_sin f₀ hfm hsupp 1
  simp only [Nat.cast_one] at hcos1 hsin1
  have _hnu := gram_nu_nonneg f₀ hf0 hfm hsupp hmass 2 (by omega) [[1, 1, 1]] (by simp)
  refine ⟨autoconvValues_bddAbove hfm,
    autoconv_integral_Icc_eq_one f₀ hfm hsupp hmass,
    hcos1, hsin1,
    finite_bessel_autoconv f₀ hf0 hfm hsupp hmass 2 hΩ,
    gram_f_nonneg f₀ hf0 hfm hsupp hmass 2 [[1, 1, 1]] (by simp),
    gram_g_le f₀ hfm hsupp hmass 2 hΩ [[1, 1, 1]] (by simp)⟩

/-- Positive Singer Sidon witnesses `{0, 1, 4, 6} ⊆ {0..6}` and `{0, 1, 3, 7, 12, 20} ⊆ {0..20}`,
negative non-Sidon check `{0, 1, 2}`, genuine `B_2[3]` non-Sidon witness `{0, 1, 2, 4} ⊆ {0..4}`,
and explicit instantiations of `c1a_mul_card_sq_le_two_mul_g_sidon` and `isSidonFinset_card_sq_le`. -/
example :
    IsSidonFinset ({0, 1, 4, 6} : Finset ℕ) ∧
    IsGSidon 2 ({0, 1, 4, 6} : Finset ℕ) ∧
    IsSidonFinset ({0, 1, 3, 7, 12, 20} : Finset ℕ) ∧
    ¬ IsSidonFinset ({0, 1, 2} : Finset ℕ) ∧
    ¬ IsGSidon 2 ({0, 1, 2, 4} : Finset ℕ) ∧
    IsGSidon 3 ({0, 1, 2, 4} : Finset ℕ) ∧
    C1a * (4 : ℝ) ^ 2 ≤ 2 * 2 * 7 ∧
    C1a * (4 : ℝ) ^ 2 ≤ 2 * 3 * 5 ∧
    (6 : ℝ) ^ 2 ≤ (2500 / 811 : ℝ) * 21 := by
  have hs7 : IsSidonFinset ({0, 1, 4, 6} : Finset ℕ) := by decide
  have hs21 : IsSidonFinset ({0, 1, 3, 7, 12, 20} : Finset ℕ) := by decide
  have hns : ¬ IsSidonFinset ({0, 1, 2} : Finset ℕ) := by decide
  have hnot_g2 : ¬ IsGSidon 2 ({0, 1, 2, 4} : Finset ℕ) := by
    intro hg
    have h2 := hg 2
    have hc : ((({0, 1, 2, 4} : Finset ℕ) ×ˢ ({0, 1, 2, 4} : Finset ℕ)).filter
        (fun ab => ab.1 + ab.2 = 2)).card = 3 := by decide
    omega
  have hg3 : IsGSidon 3 ({0, 1, 2, 4} : Finset ℕ) := by
    intro s
    by_cases hs : s < 9
    · have hall : ∀ m ∈ Finset.range 9,
          ((({0, 1, 2, 4} : Finset ℕ) ×ˢ ({0, 1, 2, 4} : Finset ℕ)).filter
            (fun ab => ab.1 + ab.2 = m)).card ≤ 3 := by decide
      exact hall s (Finset.mem_range.mpr hs)
    · have hemp : (({0, 1, 2, 4} : Finset ℕ) ×ˢ ({0, 1, 2, 4} : Finset ℕ)).filter
          (fun ab => ab.1 + ab.2 = s) = ∅ := by
        ext ⟨a, b⟩
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_insert,
          Finset.mem_singleton, Finset.notMem_empty, iff_false]
        rintro ⟨⟨rfl | rfl | rfl | rfl, rfl | rfl | rfl | rfl⟩, hab⟩ <;> omega
      simp [hemp]
  have hb7 := c1a_mul_card_sq_le_two_mul_g_sidon (N := 7) (A := {0, 1, 4, 6})
    (by decide) hs7.isGSidon_two
  have hb5 := c1a_mul_card_sq_le_two_mul_g_sidon (N := 5) (A := {0, 1, 2, 4})
    (by decide) hg3
  have hc21 := isSidonFinset_card_sq_le (N := 21) (A := {0, 1, 3, 7, 12, 20})
    (by decide) hs21
  have hcard4 : (({0, 1, 4, 6} : Finset ℕ).card : ℝ) = 4 := by norm_cast
  have hcard4' : (({0, 1, 2, 4} : Finset ℕ).card : ℝ) = 4 := by norm_cast
  have hcard6 : (({0, 1, 3, 7, 12, 20} : Finset ℕ).card : ℝ) = 6 := by norm_cast
  rw [hcard4] at hb7
  rw [hcard4'] at hb5
  rw [hcard6] at hc21
  exact ⟨hs7, hs7.isGSidon_two, hs21, hns, hnot_g2, hg3,
    by simpa using hb7, by simpa using hb5, by simpa using hc21⟩

end NonVacuityExamples

end Constant1aProof
