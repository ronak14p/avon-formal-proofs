import Mathlib

/-!
# Ben Green's Open Problem 19 (solved: C = 4, Mandache; Fox–Sah–Sawhney–Stoner–Zhao): Popular Corners in `𝔽₂ n × 𝔽₂ n` and Triforce Densities

Standalone Lean 4 formalization (`import Mathlib` only) proving `Green19.green_19 : C = 4`,
`Green19.green_19.lower : C >= 3.13`, `Green19.green_19.upper : C <= 4`, and the exact exponent
characterization `validExponent_iff : ValidExponent c ↔ 4 ≤ c`:

1. **Finite Weighted Triforce Inequality:** Proves `weightedTriforce_ge_div_256` and upgrades via
   tensor-squaring to the sharp bound `weightedTriforce_ge_pow_four` (`T_{p,q,r}(f) ≥ μ(f)^4`)
   purely over finite product probability spaces (`0` measure-theory overhead).
2. **Two-Energy Walsh–Fourier Boxing Regularity & Triangle Counting (`ValidExponent 4`):**
   Formalizes Matei Mandache's two-energy regularity lemma on `𝔽₂ n`, 3-partite linear-slicing
   triangle counting, and `popular_corner_f2_pow_four`, establishing `validExponent_four` and
   `validExponent_of_ge_four`.
3. **Behrend Sphere, Ruzsa–Szemerédi Triforce Hypergraph, and Finite-Product Concentration
   (`∀ c < 4, ¬ ValidExponent c`):** Formalizes Mandache's explicit `2 × 2 × 2` kernel (`13 / 32`),
   Behrend's constructive 3-AP-free sphere set (`behrend_ap3_free`), the Fox–Sah–Sawhney–Stoner–Zhao
   tripartite triforce hypergraph identity (`ruzsa_szemeredi_triforce_density`), and transversal
   Hoeffding sampling on `𝔽₂ n × 𝔽₂ n` (`mandache_random_corner_upper`), refuting `ValidExponent c`
   for every `c < 4` and concluding `C = 4`.
-/

open Finset Real
open scoped BigOperators

abbrev 𝔽 (p n : ℕ) := Fin n → ZMod p
abbrev 𝔽₂ (n : ℕ) := 𝔽 2 n

namespace Green19

section GroupDefs
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- A corner in $A$ with common difference $d$. -/
def IsCorner (A : Finset (G × G)) (x y d : G) : Prop :=
  (x, y) ∈ A ∧ (x + d, y) ∈ A ∧ (x, y + d) ∈ A

/-- Set of corners of size $d$ in $A$. -/
noncomputable def S (d : G) (A : Finset (G × G)) : Finset (G × G) :=
  open scoped Classical in
  univ.filter (fun p => IsCorner A p.1 p.2 d)

end GroupDefs

/-- True if the given exponent satisfies Green's conditions. -/
def ValidExponent (c : ℝ) : Prop :=
  ∃ K > 0,
    ∀ α, 0 < α → α < 1 →
      ∀ᶠ n in Filter.atTop,
        ∀ A : Finset (𝔽₂ n × 𝔽₂ n),
          let N : ℝ := (Fintype.card (𝔽₂ n) : ℝ)
          (A.card : ℝ) ≥ α * N^2 →
          ∃ d : 𝔽₂ n, d ≠ 0 ∧ ((S d A).card : ℝ) ≥ K * α^c * N^2

/-- The infimum of all valid exponents. -/
noncomputable def C : ℝ := sInf {c | ValidExponent c}

/-- Finite weighted triforce functional on a product of three finite probability spaces. -/
def weightedTriforce {ι₁ ι₂ ι₃ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    (p : ι₁ → ℝ) (q : ι₂ → ℝ) (r : ι₃ → ℝ) (f : ι₁ → ι₂ → ι₃ → ℝ) : ℝ :=
  ∑ i : ι₁, ∑ j : ι₂, ∑ k : ι₃,
    p i * q j * r k *
      (∑ i' : ι₁, p i' * f i' j k) *
      (∑ j' : ι₂, q j' * f i j' k) *
      (∑ k' : ι₃, r k' * f i j k')

/-
## Section 1: Finite Weighted Triforce Inequality
-/

private lemma weightedTriforce_nonneg {ι₁ ι₂ ι₃ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    (p : ι₁ → ℝ) (q : ι₂ → ℝ) (r : ι₃ → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ j, 0 ≤ q j) (hr : ∀ k, 0 ≤ r k)
    (f : ι₁ → ι₂ → ι₃ → ℝ) (hf0 : ∀ i j k, 0 ≤ f i j k) :
    0 ≤ weightedTriforce p q r f := by
  refine sum_nonneg fun i _ => sum_nonneg fun j _ => sum_nonneg fun k _ => ?_
  refine mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) ?_
  · exact mul_nonneg (mul_nonneg (hp i) (hq j)) (hr k)
  · exact sum_nonneg fun i' _ => mul_nonneg (hp i') (hf0 i' j k)
  · exact sum_nonneg fun j' _ => mul_nonneg (hq j') (hf0 i j' k)
  · exact sum_nonneg fun k' _ => mul_nonneg (hr k') (hf0 i j k')

/-- Mandache's $\alpha^4 / 256$ lower bound for the finite weighted triforce functional. -/
theorem weightedTriforce_ge_div_256 {ι₁ ι₂ ι₃ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    (p : ι₁ → ℝ) (q : ι₂ → ℝ) (r : ι₃ → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ j, 0 ≤ q j) (hr : ∀ k, 0 ≤ r k)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ j, q j = 1) (hr1 : ∑ k, r k = 1)
    (f : ι₁ → ι₂ → ι₃ → ℝ) (hf0 : ∀ i j k, 0 ≤ f i j k) (hf1 : ∀ i j k, f i j k ≤ 1) :
    (∑ i, ∑ j, ∑ k, p i * q j * r k * f i j k) ^ 4 / 256 ≤ weightedTriforce p q r f := by
  classical
  let α : ℝ := ∑ i, ∑ j, ∑ k, p i * q j * r k * f i j k
  have hα : 0 ≤ α := sum_nonneg fun i _ => sum_nonneg fun j _ => sum_nonneg fun k _ =>
    mul_nonneg (mul_nonneg (mul_nonneg (hp i) (hq j)) (hr k)) (hf0 i j k)
  let f₁ : ι₂ → ι₃ → ℝ := fun j k => ∑ i, p i * f i j k
  let f₂ : ι₁ → ι₃ → ℝ := fun i k => ∑ j, q j * f i j k
  let f₃ : ι₁ → ι₂ → ℝ := fun i j => ∑ k, r k * f i j k
  have hf₁0 : ∀ j k, 0 ≤ f₁ j k := fun j k => sum_nonneg fun i _ => mul_nonneg (hp i) (hf0 i j k)
  have hf₂0 : ∀ i k, 0 ≤ f₂ i k := fun i k => sum_nonneg fun j _ => mul_nonneg (hq j) (hf0 i j k)
  have hf₃0 : ∀ i j, 0 ≤ f₃ i j := fun i j => sum_nonneg fun k _ => mul_nonneg (hr k) (hf0 i j k)
  have hbad₁ : (∑ i, ∑ j, ∑ k, if f₁ j k < α / 4 then p i * q j * r k * f i j k else 0) ≤
      α / 4 := by
    calc (∑ i, ∑ j, ∑ k, if f₁ j k < α / 4 then p i * q j * r k * f i j k else 0)
        = ∑ j, ∑ k, ∑ i, if f₁ j k < α / 4 then p i * q j * r k * f i j k else 0 := by
            rw [sum_comm]; refine sum_congr rfl fun j _ => sum_comm
      _ ≤ ∑ j, ∑ k, q j * r k * (α / 4) := by
          refine sum_le_sum fun j _ => sum_le_sum fun k _ => ?_
          by_cases h : f₁ j k < α / 4
          · simp only [h, ↓reduceIte]
            have hsum : (∑ i, p i * q j * r k * f i j k) = q j * r k * f₁ j k := by
              simp only [f₁, mul_sum]
              refine sum_congr rfl fun i _ => by ring
            rw [hsum]
            exact mul_le_mul_of_nonneg_left h.le (mul_nonneg (hq j) (hr k))
          · simp only [h, ↓reduceIte, sum_const_zero]
            exact mul_nonneg (mul_nonneg (hq j) (hr k)) (by positivity)
      _ = ((∑ j, q j) * (∑ k, r k)) * (α / 4) := by
          simp_rw [← sum_mul]
          congr 1
          rw [sum_mul]
          refine sum_congr rfl fun j _ => ?_
          rw [mul_sum]
      _ = α / 4 := by rw [hq1, hr1]; ring
  have hbad₂ : (∑ i, ∑ j, ∑ k, if f₂ i k < α / 4 then p i * q j * r k * f i j k else 0) ≤
      α / 4 := by
    calc (∑ i, ∑ j, ∑ k, if f₂ i k < α / 4 then p i * q j * r k * f i j k else 0)
        = ∑ i, ∑ k, ∑ j, if f₂ i k < α / 4 then p i * q j * r k * f i j k else 0 := by
            refine sum_congr rfl fun i _ => sum_comm
      _ ≤ ∑ i, ∑ k, p i * r k * (α / 4) := by
          refine sum_le_sum fun i _ => sum_le_sum fun k _ => ?_
          by_cases h : f₂ i k < α / 4
          · simp only [h, ↓reduceIte]
            have hsum : (∑ j, p i * q j * r k * f i j k) = p i * r k * f₂ i k := by
              simp only [f₂, mul_sum]
              refine sum_congr rfl fun j _ => by ring
            rw [hsum]
            exact mul_le_mul_of_nonneg_left h.le (mul_nonneg (hp i) (hr k))
          · simp only [h, ↓reduceIte, sum_const_zero]
            exact mul_nonneg (mul_nonneg (hp i) (hr k)) (by positivity)
      _ = ((∑ i, p i) * (∑ k, r k)) * (α / 4) := by
          simp_rw [← sum_mul]
          congr 1
          rw [sum_mul]
          refine sum_congr rfl fun i _ => ?_
          rw [mul_sum]
      _ = α / 4 := by rw [hp1, hr1]; ring
  have hbad₃ : (∑ i, ∑ j, ∑ k, if f₃ i j < α / 4 then p i * q j * r k * f i j k else 0) ≤
      α / 4 := by
    calc (∑ i, ∑ j, ∑ k, if f₃ i j < α / 4 then p i * q j * r k * f i j k else 0)
        ≤ ∑ i, ∑ j, p i * q j * (α / 4) := by
          refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
          by_cases h : f₃ i j < α / 4
          · simp only [h, ↓reduceIte]
            have hsum : (∑ k, p i * q j * r k * f i j k) = p i * q j * f₃ i j := by
              simp only [f₃, mul_sum]
              refine sum_congr rfl fun k _ => by ring
            rw [hsum]
            exact mul_le_mul_of_nonneg_left h.le (mul_nonneg (hp i) (hq j))
          · simp only [h, ↓reduceIte, sum_const_zero]
            exact mul_nonneg (mul_nonneg (hp i) (hq j)) (by positivity)
      _ = ((∑ i, p i) * (∑ j, q j)) * (α / 4) := by
          simp_rw [← sum_mul]
          congr 1
          rw [sum_mul]
          refine sum_congr rfl fun i _ => ?_
          rw [mul_sum]
      _ = α / 4 := by rw [hp1, hq1]; ring
  let good : ι₁ → ι₂ → ι₃ → Prop := fun i j k => α / 4 ≤ f₁ j k ∧ α / 4 ≤ f₂ i k ∧ α / 4 ≤ f₃ i j
  have hpoint : ∀ i j k,
      p i * q j * r k * f i j k ≤
        (if good i j k then p i * q j * r k else 0) +
        (if f₁ j k < α / 4 then p i * q j * r k * f i j k else 0) +
        (if f₂ i k < α / 4 then p i * q j * r k * f i j k else 0) +
        (if f₃ i j < α / 4 then p i * q j * r k * f i j k else 0) := by
    intro i j k
    have hw : 0 ≤ p i * q j * r k := mul_nonneg (mul_nonneg (hp i) (hq j)) (hr k)
    have hwf : 0 ≤ p i * q j * r k * f i j k := mul_nonneg hw (hf0 i j k)
    have hwf1 : p i * q j * r k * f i j k ≤ p i * q j * r k := by
      simpa using mul_le_mul_of_nonneg_left (hf1 i j k) hw
    by_cases hg : good i j k
    · have h1 : ¬ (f₁ j k < α / 4) := not_lt.mpr hg.1
      have h2 : ¬ (f₂ i k < α / 4) := not_lt.mpr hg.2.1
      have h3 : ¬ (f₃ i j < α / 4) := not_lt.mpr hg.2.2
      simp [hg, h1, h2, h3, hwf1]
    · have hg0 : 0 ≤ if good i j k then p i * q j * r k else 0 := by simp [hg]
      have hb1 : 0 ≤ if f₁ j k < α / 4 then p i * q j * r k * f i j k else 0 := by
        split_ifs <;> linarith
      have hb2 : 0 ≤ if f₂ i k < α / 4 then p i * q j * r k * f i j k else 0 := by
        split_ifs <;> linarith
      have hb3 : 0 ≤ if f₃ i j < α / 4 then p i * q j * r k * f i j k else 0 := by
        split_ifs <;> linarith
      by_cases h1 : f₁ j k < α / 4
      · simp only [h1, ↓reduceIte]; linarith
      · by_cases h2 : f₂ i k < α / 4
        · simp only [h2, ↓reduceIte]; linarith
        · by_cases h3 : f₃ i j < α / 4
          · simp only [h3, ↓reduceIte]; linarith
          · exfalso; exact hg ⟨not_lt.mp h1, not_lt.mp h2, not_lt.mp h3⟩
  have hsum_good : α / 4 ≤ ∑ i, ∑ j, ∑ k, if good i j k then p i * q j * r k else 0 := by
    have hle : α ≤ (∑ i, ∑ j, ∑ k, if good i j k then p i * q j * r k else 0) +
        (∑ i, ∑ j, ∑ k, if f₁ j k < α / 4 then p i * q j * r k * f i j k else 0) +
        (∑ i, ∑ j, ∑ k, if f₂ i k < α / 4 then p i * q j * r k * f i j k else 0) +
        (∑ i, ∑ j, ∑ k, if f₃ i j < α / 4 then p i * q j * r k * f i j k else 0) := by
      calc α = ∑ i, ∑ j, ∑ k, p i * q j * r k * f i j k := rfl
        _ ≤ ∑ i, ∑ j, ∑ k,
              ((if good i j k then p i * q j * r k else 0) +
              (if f₁ j k < α / 4 then p i * q j * r k * f i j k else 0) +
              (if f₂ i k < α / 4 then p i * q j * r k * f i j k else 0) +
              (if f₃ i j < α / 4 then p i * q j * r k * f i j k else 0)) :=
            sum_le_sum fun i _ => sum_le_sum fun j _ => sum_le_sum fun k _ => hpoint i j k
        _ = _ := by simp only [sum_add_distrib]
    linarith
  have hterm : ∀ i j k,
      (if good i j k then p i * q j * r k else 0) * (α / 4) ^ 3 ≤
        p i * q j * r k * f₁ j k * f₂ i k * f₃ i j := by
    intro i j k
    have hw : 0 ≤ p i * q j * r k := mul_nonneg (mul_nonneg (hp i) (hq j)) (hr k)
    by_cases hg : good i j k
    · simp only [hg, ↓reduceIte]
      have hprod : (α / 4) ^ 3 ≤ f₁ j k * f₂ i k * f₃ i j := by
        rcases hg with ⟨h1, h2, h3⟩
        have ha : 0 ≤ α / 4 := by positivity
        calc (α / 4) ^ 3 = (α / 4) * (α / 4) * (α / 4) := by ring
          _ ≤ f₁ j k * f₂ i k * f₃ i j :=
            mul_le_mul (mul_le_mul h1 h2 ha (hf₁0 j k)) h3 ha (mul_nonneg (hf₁0 j k) (hf₂0 i k))
      calc p i * q j * r k * (α / 4) ^ 3
          ≤ p i * q j * r k * (f₁ j k * f₂ i k * f₃ i j) := mul_le_mul_of_nonneg_left hprod hw
        _ = p i * q j * r k * f₁ j k * f₂ i k * f₃ i j := by ring
    · simp only [hg, ↓reduceIte, zero_mul]
      exact mul_nonneg (mul_nonneg (mul_nonneg hw (hf₁0 j k)) (hf₂0 i k)) (hf₃0 i j)
  calc α ^ 4 / 256 = (α / 4) * (α / 4) ^ 3 := by ring
    _ ≤ (∑ i, ∑ j, ∑ k, if good i j k then p i * q j * r k else 0) * (α / 4) ^ 3 :=
        mul_le_mul_of_nonneg_right hsum_good (by positivity)
    _ = ∑ i, ∑ j, ∑ k, (if good i j k then p i * q j * r k else 0) * (α / 4) ^ 3 := by
        simp only [sum_mul]
    _ ≤ weightedTriforce p q r f := by
        unfold weightedTriforce
        exact sum_le_sum fun i _ => sum_le_sum fun j _ => sum_le_sum fun k _ => hterm i j k

private lemma weightedTriforce_tensor_sq {ι₁ ι₂ ι₃ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    (p : ι₁ → ℝ) (q : ι₂ → ℝ) (r : ι₃ → ℝ) (f : ι₁ → ι₂ → ι₃ → ℝ) :
    let p2 : ι₁ × ι₁ → ℝ := fun a => p a.1 * p a.2
    let q2 : ι₂ × ι₂ → ℝ := fun b => q b.1 * q b.2
    let r2 : ι₃ × ι₃ → ℝ := fun c => r c.1 * r c.2
    let f2 : ι₁ × ι₁ → ι₂ × ι₂ → ι₃ × ι₃ → ℝ := fun a b c => f a.1 b.1 c.1 * f a.2 b.2 c.2
    (∑ a, ∑ b, ∑ c, p2 a * q2 b * r2 c * f2 a b c =
      (∑ i, ∑ j, ∑ k, p i * q j * r k * f i j k) ^ 2) ∧
    (weightedTriforce p2 q2 r2 f2 = (weightedTriforce p q r f) ^ 2) := by
  intro p2 q2 r2 f2
  constructor
  · have hsum_split :
        (∑ a : ι₁ × ι₁, ∑ b : ι₂ × ι₂, ∑ c : ι₃ × ι₃, p2 a * q2 b * r2 c * f2 a b c) =
          ∑ i₁, ∑ j₁, ∑ k₁, ∑ i₂, ∑ j₂, ∑ k₂,
            (p i₁ * q j₁ * r k₁ * f i₁ j₁ k₁) * (p i₂ * q j₂ * r k₂ * f i₂ j₂ k₂) := by
      simp only [Fintype.sum_prod_type]
      refine sum_congr rfl fun i₁ _ => ?_
      calc (∑ i₂, ∑ j₁, ∑ j₂, ∑ k₁, ∑ k₂,
              p2 (i₁, i₂) * q2 (j₁, j₂) * r2 (k₁, k₂) * f2 (i₁, i₂) (j₁, j₂) (k₁, k₂))
          = ∑ i₂, ∑ j₁, ∑ k₁, ∑ j₂, ∑ k₂,
              p2 (i₁, i₂) * q2 (j₁, j₂) * r2 (k₁, k₂) * f2 (i₁, i₂) (j₁, j₂) (k₁, k₂) :=
            sum_congr rfl fun i₂ _ => sum_congr rfl fun j₁ _ => sum_comm
        _ = ∑ j₁, ∑ i₂, ∑ k₁, ∑ j₂, ∑ k₂,
              p2 (i₁, i₂) * q2 (j₁, j₂) * r2 (k₁, k₂) * f2 (i₁, i₂) (j₁, j₂) (k₁, k₂) :=
            sum_comm
        _ = ∑ j₁, ∑ k₁, ∑ i₂, ∑ j₂, ∑ k₂,
              (p i₁ * q j₁ * r k₁ * f i₁ j₁ k₁) * (p i₂ * q j₂ * r k₂ * f i₂ j₂ k₂) := by
            refine sum_congr rfl fun j₁ _ => ?_
            rw [sum_comm]
            refine sum_congr rfl fun k₁ _ => sum_congr rfl fun i₂ _ =>
              sum_congr rfl fun j₂ _ => sum_congr rfl fun k₂ _ => ?_
            simp only [p2, q2, r2, f2]; ring
    rw [hsum_split, sq]
    simp_rw [← mul_sum]
    simp_rw [← sum_mul]
  · unfold weightedTriforce
    have hmarg₁ : ∀ (j₁ j₂ : ι₂) (k₁ k₂ : ι₃),
        (∑ a' : ι₁ × ι₁, p2 a' * f2 a' (j₁, j₂) (k₁, k₂)) =
          (∑ i' : ι₁, p i' * f i' j₁ k₁) * (∑ i'' : ι₁, p i'' * f i'' j₂ k₂) := by
      intro j₁ j₂ k₁ k₂
      rw [Fintype.sum_prod_type]
      calc ∑ i₁, ∑ i₂, p2 (i₁, i₂) * f2 (i₁, i₂) (j₁, j₂) (k₁, k₂)
          = ∑ i₁, ∑ i₂, (p i₁ * f i₁ j₁ k₁) * (p i₂ * f i₂ j₂ k₂) :=
              sum_congr rfl fun i₁ _ => sum_congr rfl fun i₂ _ => by simp only [p2, f2]; ring
        _ = (∑ i₁, p i₁ * f i₁ j₁ k₁) * (∑ i₂, p i₂ * f i₂ j₂ k₂) := by
              simp_rw [← mul_sum, ← sum_mul]
    have hmarg₂ : ∀ (i₁ i₂ : ι₁) (k₁ k₂ : ι₃),
        (∑ b' : ι₂ × ι₂, q2 b' * f2 (i₁, i₂) b' (k₁, k₂)) =
          (∑ j' : ι₂, q j' * f i₁ j' k₁) * (∑ j'' : ι₂, q j'' * f i₂ j'' k₂) := by
      intro i₁ i₂ k₁ k₂
      rw [Fintype.sum_prod_type]
      calc ∑ j₁, ∑ j₂, q2 (j₁, j₂) * f2 (i₁, i₂) (j₁, j₂) (k₁, k₂)
          = ∑ j₁, ∑ j₂, (q j₁ * f i₁ j₁ k₁) * (q j₂ * f i₂ j₂ k₂) :=
              sum_congr rfl fun j₁ _ => sum_congr rfl fun j₂ _ => by simp only [q2, f2]; ring
        _ = (∑ j₁, q j₁ * f i₁ j₁ k₁) * (∑ j₂, q j₂ * f i₂ j₂ k₂) := by
              simp_rw [← mul_sum, ← sum_mul]
    have hmarg₃ : ∀ (i₁ i₂ : ι₁) (j₁ j₂ : ι₂),
        (∑ c' : ι₃ × ι₃, r2 c' * f2 (i₁, i₂) (j₁, j₂) c') =
          (∑ k' : ι₃, r k' * f i₁ j₁ k') * (∑ k'' : ι₃, r k'' * f i₂ j₂ k'') := by
      intro i₁ i₂ j₁ j₂
      rw [Fintype.sum_prod_type]
      calc ∑ k₁, ∑ k₂, r2 (k₁, k₂) * f2 (i₁, i₂) (j₁, j₂) (k₁, k₂)
          = ∑ k₁, ∑ k₂, (r k₁ * f i₁ j₁ k₁) * (r k₂ * f i₂ j₂ k₂) :=
              sum_congr rfl fun k₁ _ => sum_congr rfl fun k₂ _ => by simp only [r2, f2]; ring
        _ = (∑ k₁, r k₁ * f i₁ j₁ k₁) * (∑ k₂, r k₂ * f i₂ j₂ k₂) := by
              simp_rw [← mul_sum, ← sum_mul]
    have hexp :
        (∑ i : ι₁ × ι₁, ∑ j : ι₂ × ι₂, ∑ k : ι₃ × ι₃,
          p2 i * q2 j * r2 k *
            (∑ i', p2 i' * f2 i' j k) *
            (∑ j', q2 j' * f2 i j' k) *
            (∑ k', r2 k' * f2 i j k')) =
        ∑ i₁, ∑ i₂, ∑ j₁, ∑ j₂, ∑ k₁, ∑ k₂,
          p2 (i₁, i₂) * q2 (j₁, j₂) * r2 (k₁, k₂) *
            ((∑ i', p i' * f i' j₁ k₁) * (∑ i'', p i'' * f i'' j₂ k₂)) *
            ((∑ j', q j' * f i₁ j' k₁) * (∑ j'', q j'' * f i₂ j'' k₂)) *
            ((∑ k', r k' * f i₁ j₁ k') * (∑ k'', r k'' * f i₂ j₂ k'')) := by
      rw [Fintype.sum_prod_type]
      refine sum_congr rfl fun i₁ _ => sum_congr rfl fun i₂ _ => ?_
      rw [Fintype.sum_prod_type]
      refine sum_congr rfl fun j₁ _ => sum_congr rfl fun j₂ _ => ?_
      rw [Fintype.sum_prod_type]
      refine sum_congr rfl fun k₁ _ => sum_congr rfl fun k₂ _ => ?_
      rw [hmarg₁, hmarg₂, hmarg₃]
    have hreord :
        (∑ i₁, ∑ i₂, ∑ j₁, ∑ j₂, ∑ k₁, ∑ k₂,
          p2 (i₁, i₂) * q2 (j₁, j₂) * r2 (k₁, k₂) *
            ((∑ i', p i' * f i' j₁ k₁) * (∑ i'', p i'' * f i'' j₂ k₂)) *
            ((∑ j', q j' * f i₁ j' k₁) * (∑ j'', q j'' * f i₂ j'' k₂)) *
            ((∑ k', r k' * f i₁ j₁ k') * (∑ k'', r k'' * f i₂ j₂ k''))) =
        ∑ i₁, ∑ j₁, ∑ k₁, ∑ i₂, ∑ j₂, ∑ k₂,
          (p i₁ * q j₁ * r k₁ *
            (∑ i', p i' * f i' j₁ k₁) *
            (∑ j', q j' * f i₁ j' k₁) *
            (∑ k', r k' * f i₁ j₁ k')) *
          (p i₂ * q j₂ * r k₂ *
            (∑ i'', p i'' * f i'' j₂ k₂) *
            (∑ j'', q j'' * f i₂ j'' k₂) *
            (∑ k'', r k'' * f i₂ j₂ k'')) := by
      refine sum_congr rfl fun i₁ _ => ?_
      calc (∑ i₂, ∑ j₁, ∑ j₂, ∑ k₁, ∑ k₂, _)
          = ∑ i₂, ∑ j₁, ∑ k₁, ∑ j₂, ∑ k₂, _ :=
            sum_congr rfl fun i₂ _ => sum_congr rfl fun j₁ _ => sum_comm
        _ = ∑ j₁, ∑ i₂, ∑ k₁, ∑ j₂, ∑ k₂, _ := sum_comm
        _ = ∑ j₁, ∑ k₁, ∑ i₂, ∑ j₂, ∑ k₂, _ := by
            refine sum_congr rfl fun j₁ _ => ?_
            rw [sum_comm]
            refine sum_congr rfl fun k₁ _ => sum_congr rfl fun i₂ _ =>
              sum_congr rfl fun j₂ _ => sum_congr rfl fun k₂ _ => ?_
            simp only [p2, q2, r2]; ring
    rw [hexp, hreord, sq]
    simp_rw [← mul_sum]
    simp_rw [← sum_mul]

private lemma weightedTriforce_pow_two_pow : ∀ (t : ℕ)
    {ι₁ : Type*} {ι₂ : Type*} {ι₃ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    (p : ι₁ → ℝ) (q : ι₂ → ℝ) (r : ι₃ → ℝ),
    (∀ i, 0 ≤ p i) → (∀ j, 0 ≤ q j) → (∀ k, 0 ≤ r k) →
    (∑ i, p i = 1) → (∑ j, q j = 1) → (∑ k, r k = 1) →
    ∀ (f : ι₁ → ι₂ → ι₃ → ℝ), (∀ i j k, 0 ≤ f i j k) → (∀ i j k, f i j k ≤ 1) →
    ((∑ i, ∑ j, ∑ k, p i * q j * r k * f i j k) ^ 4) ^ (2 ^ t) / 256 ≤
      (weightedTriforce p q r f) ^ (2 ^ t) := by
  intro t
  induction t with
  | zero =>
      intro ι₁ ι₂ ι₃ _ _ _ p q r hp hq hr hp1 hq1 hr1 f hf0 hf1
      simpa using weightedTriforce_ge_div_256 p q r hp hq hr hp1 hq1 hr1 f hf0 hf1
  | succ t ih =>
      intro ι₁ ι₂ ι₃ _ _ _ p q r hp hq hr hp1 hq1 hr1 f hf0 hf1
      let p2 : ι₁ × ι₁ → ℝ := fun a => p a.1 * p a.2
      let q2 : ι₂ × ι₂ → ℝ := fun b => q b.1 * q b.2
      let r2 : ι₃ × ι₃ → ℝ := fun c => r c.1 * r c.2
      let f2 : ι₁ × ι₁ → ι₂ × ι₂ → ι₃ × ι₃ → ℝ := fun a b c => f a.1 b.1 c.1 * f a.2 b.2 c.2
      have hp2 : ∀ a, 0 ≤ p2 a := fun a => mul_nonneg (hp a.1) (hp a.2)
      have hq2 : ∀ b, 0 ≤ q2 b := fun b => mul_nonneg (hq b.1) (hq b.2)
      have hr2 : ∀ c, 0 ≤ r2 c := fun c => mul_nonneg (hr c.1) (hr c.2)
      have hp2_1 : ∑ a, p2 a = 1 := by
        simp only [p2, Fintype.sum_prod_type, ← mul_sum, hp1, mul_one]
      have hq2_1 : ∑ b, q2 b = 1 := by
        simp only [q2, Fintype.sum_prod_type, ← mul_sum, hq1, mul_one]
      have hr2_1 : ∑ c, r2 c = 1 := by
        simp only [r2, Fintype.sum_prod_type, ← mul_sum, hr1, mul_one]
      have hf2_0 : ∀ a b c, 0 ≤ f2 a b c := fun a b c => mul_nonneg (hf0 a.1 b.1 c.1) (hf0 a.2 b.2 c.2)
      have hf2_1 : ∀ a b c, f2 a b c ≤ 1 := fun a b c =>
        mul_le_one₀ (hf1 a.1 b.1 c.1) (hf0 a.2 b.2 c.2) (hf1 a.2 b.2 c.2)
      have hih := ih p2 q2 r2 hp2 hq2 hr2 hp2_1 hq2_1 hr2_1 f2 hf2_0 hf2_1
      rcases weightedTriforce_tensor_sq p q r f with ⟨hmean, htri⟩
      rw [hmean, htri] at hih
      have hl : (((∑ i, ∑ j, ∑ k, p i * q j * r k * f i j k) ^ 2) ^ 4) ^ (2 ^ t) =
          ((∑ i, ∑ j, ∑ k, p i * q j * r k * f i j k) ^ 4) ^ (2 ^ (t + 1)) := by
        rw [← pow_mul, ← pow_mul, ← pow_mul]
        congr 1
        rw [pow_succ']
        ring
      have hrpow : (weightedTriforce p q r f ^ 2) ^ (2 ^ t) =
          weightedTriforce p q r f ^ (2 ^ (t + 1)) := by
        rw [← pow_mul, pow_succ']
      rw [hl, hrpow] at hih
      exact hih

/-- Sharp finite weighted triforce lower bound: $T_{p,q,r}(f) \ge \alpha^4$. -/
theorem weightedTriforce_ge_pow_four {ι₁ ι₂ ι₃ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    (p : ι₁ → ℝ) (q : ι₂ → ℝ) (r : ι₃ → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ j, 0 ≤ q j) (hr : ∀ k, 0 ≤ r k)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ j, q j = 1) (hr1 : ∑ k, r k = 1)
    (f : ι₁ → ι₂ → ι₃ → ℝ) (hf0 : ∀ i j k, 0 ≤ f i j k) (hf1 : ∀ i j k, f i j k ≤ 1) :
    (∑ i, ∑ j, ∑ k, p i * q j * r k * f i j k) ^ 4 ≤ weightedTriforce p q r f := by
  by_contra hlt
  push Not at hlt
  let α : ℝ := ∑ i, ∑ j, ∑ k, p i * q j * r k * f i j k
  let T : ℝ := weightedTriforce p q r f
  have hT0 : 0 ≤ T := weightedTriforce_nonneg p q r hp hq hr f hf0
  have hα4_pos : 0 < α ^ 4 := lt_of_le_of_lt hT0 hlt
  have hratio_nonneg : 0 ≤ T / α ^ 4 := div_nonneg hT0 hα4_pos.le
  have hratio_lt : T / α ^ 4 < 1 := (div_lt_one hα4_pos).mpr hlt
  obtain ⟨t, ht⟩ := exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 1 / 256) hratio_lt
  have ht_pow : (T / α ^ 4) ^ (2 ^ t) ≤ (T / α ^ 4) ^ t :=
    pow_le_pow_of_le_one hratio_nonneg hratio_lt.le Nat.lt_two_pow_self.le
  have hbound := weightedTriforce_pow_two_pow t p q r hp hq hr hp1 hq1 hr1 f hf0 hf1
  have hpow_pos : 0 < (α ^ 4) ^ (2 ^ t) := pow_pos hα4_pos (2 ^ t)
  have h1 : 1 / 256 ≤ (T / α ^ 4) ^ (2 ^ t) := by
    rw [div_pow, le_div_iff₀ hpow_pos]
    linarith
  linarith

/-
## Section 2: `𝔽₂ n` Arithmetic, Projections, and Walsh–Fourier Analysis
-/

section F2LinearAlgebra

private lemma zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide

private lemma f2_add_self {n : ℕ} (x : 𝔽₂ n) : x + x = 0 := by
  ext i
  exact zmod2_add_self (x i)

private lemma f2_two_smul {n : ℕ} (x : 𝔽₂ n) : 2 • x = 0 := by
  rw [two_nsmul, f2_add_self]

private lemma f2_card (n : ℕ) : Fintype.card (𝔽₂ n) = 2 ^ n := by
  simp [𝔽₂, 𝔽, ZMod.card]

private lemma four_pow_eq (r : ℕ) : (2 ^ r) ^ 2 = 4 ^ r := by
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num

private lemma four_pow_eq_real (r : ℕ) : ((2 ^ r : ℝ)) ^ 2 = (4 ^ r : ℝ) := by
  exact_mod_cast four_pow_eq r

private noncomputable instance instFintypeF2Submodule {n : ℕ}
    (W : Submodule (ZMod 2) (𝔽₂ n)) : Fintype W := by
  classical
  exact Fintype.ofFinite W

private def fiber {n r : ℕ} (proj : 𝔽₂ n →ₗ[ZMod 2] 𝔽₂ r) (u : 𝔽₂ r) : Finset (𝔽₂ n) :=
  univ.filter (fun x => proj x = u)

private lemma mem_fiber {n r : ℕ} {proj : 𝔽₂ n →ₗ[ZMod 2] 𝔽₂ r} {u : 𝔽₂ r} {x : 𝔽₂ n} :
    x ∈ fiber proj u ↔ proj x = u := by
  simp [fiber]

private lemma fiber_nonempty {n r : ℕ} (proj : 𝔽₂ n →ₗ[ZMod 2] 𝔽₂ r)
    (hsurj : Function.Surjective proj) (u : 𝔽₂ r) : (fiber proj u).Nonempty := by
  obtain ⟨x, hx⟩ := hsurj u
  exact ⟨x, mem_fiber.mpr hx⟩

private lemma fiber_card_eq_zero {n r : ℕ} (proj : 𝔽₂ n →ₗ[ZMod 2] 𝔽₂ r)
    (hsurj : Function.Surjective proj) (u : 𝔽₂ r) :
    (fiber proj u).card = (fiber proj 0).card := by
  obtain ⟨x₀, hx₀⟩ := hsurj u
  refine Finset.card_bij (fun x _ => x + x₀) ?_ ?_ ?_
  · intro x hx
    rw [mem_fiber] at hx ⊢
    rw [map_add, hx, hx₀, f2_add_self]
  · intro x₁ _ x₂ _ h
    exact add_right_cancel h
  · intro y hy
    rw [mem_fiber] at hy
    refine ⟨y + x₀, mem_fiber.mpr ?_, ?_⟩
    · rw [map_add, hy, hx₀, zero_add]
    · rw [add_assoc, f2_add_self, add_zero]

private lemma codim_le {n r : ℕ} (proj : 𝔽₂ n →ₗ[ZMod 2] 𝔽₂ r)
    (hsurj : Function.Surjective proj) : r ≤ n := by
  have hpart : (univ : Finset (𝔽₂ n)) = univ.biUnion (fun u : 𝔽₂ r => fiber proj u) := by
    ext x
    simp [mem_fiber]
  have hdisj : ((univ : Finset (𝔽₂ r)) : Set (𝔽₂ r)).PairwiseDisjoint (fun u => fiber proj u) := by
    intro u _ v _ huv
    refine Finset.disjoint_left.mpr fun x hxu hxv => ?_
    rw [mem_fiber] at hxu hxv
    exact huv (hxu.symm.trans hxv)
  have hsum : Fintype.card (𝔽₂ n) = Fintype.card (𝔽₂ r) * (fiber proj 0).card := by
    calc Fintype.card (𝔽₂ n)
        = (univ : Finset (𝔽₂ n)).card := (card_univ).symm
      _ = ∑ u : 𝔽₂ r, (fiber proj u).card := by
          rw [hpart, card_biUnion hdisj]
      _ = ∑ _u : 𝔽₂ r, (fiber proj 0).card :=
          sum_congr rfl fun u _ => fiber_card_eq_zero proj hsurj u
      _ = Fintype.card (𝔽₂ r) * (fiber proj 0).card := by simp
  have hpos : 0 < (fiber proj 0).card :=
    Finset.card_pos.mpr ⟨0, mem_fiber.mpr (map_zero proj)⟩
  have hle : 2 ^ r ≤ 2 ^ n := by
    rw [← f2_card r, ← f2_card n, hsum]
    exact Nat.le_mul_of_pos_right _ hpos
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle

private lemma fiber_card {n r : ℕ} (proj : 𝔽₂ n →ₗ[ZMod 2] 𝔽₂ r)
    (hsurj : Function.Surjective proj) (u : 𝔽₂ r) :
    (fiber proj u).card = 2 ^ (n - r) := by
  have hle := codim_le proj hsurj
  have hpart : (univ : Finset (𝔽₂ n)) = univ.biUnion (fun v : 𝔽₂ r => fiber proj v) := by
    ext x
    simp [mem_fiber]
  have hdisj : ((univ : Finset (𝔽₂ r)) : Set (𝔽₂ r)).PairwiseDisjoint (fun v => fiber proj v) := by
    intro u₁ _ u₂ _ h
    refine Finset.disjoint_left.mpr fun x hx₁ hx₂ => ?_
    rw [mem_fiber] at hx₁ hx₂
    exact h (hx₁.symm.trans hx₂)
  have hsum : 2 ^ n = 2 ^ r * (fiber proj 0).card := by
    calc 2 ^ n = Fintype.card (𝔽₂ n) := (f2_card n).symm
      _ = (univ : Finset (𝔽₂ n)).card := (card_univ).symm
      _ = ∑ v : 𝔽₂ r, (fiber proj v).card := by
          rw [hpart, card_biUnion hdisj]
      _ = ∑ _v : 𝔽₂ r, (fiber proj 0).card :=
          sum_congr rfl fun v _ => fiber_card_eq_zero proj hsurj v
      _ = 2 ^ r * (fiber proj 0).card := by simp
  have hpow : 2 ^ r * 2 ^ (n - r) = 2 ^ r * (fiber proj 0).card := by
    rw [← pow_add, Nat.add_sub_of_le hle, hsum]
  have h0 : (fiber proj 0).card = 2 ^ (n - r) :=
    (Nat.mul_left_cancel (pow_pos (by norm_num) r) hpow).symm
  rw [fiber_card_eq_zero proj hsurj u, h0]

private lemma card_ker_eq {n r : ℕ} (proj : 𝔽₂ n →ₗ[ZMod 2] 𝔽₂ r)
    (hsurj : Function.Surjective proj) :
    Fintype.card (LinearMap.ker proj) = 2 ^ (n - r) := by
  classical
  have heq : (univ.filter (fun x : 𝔽₂ n => x ∈ LinearMap.ker proj)) = fiber proj 0 := by
    ext x
    simp [fiber, LinearMap.mem_ker]
  rw [Fintype.card_subtype, heq, fiber_card proj hsurj 0]

private lemma refineByList {n : ℕ} :
    ∀ (L : List (𝔽₂ n →ₗ[ZMod 2] ZMod 2)) (r : ℕ) (proj : 𝔽₂ n →ₗ[ZMod 2] 𝔽₂ r),
      Function.Surjective proj →
      ∃ (r' : ℕ) (proj' : 𝔽₂ n →ₗ[ZMod 2] 𝔽₂ r'),
        Function.Surjective proj' ∧
        r' ≤ r + L.length ∧
        LinearMap.ker proj' ≤ LinearMap.ker proj ∧
        ∀ φ ∈ L, ∀ x ∈ LinearMap.ker proj', φ x = 0 := by
  intro L
  induction L with
  | nil =>
      intro r proj hsurj
      exact ⟨r, proj, hsurj, le_rfl, le_rfl, fun _ h => by simp at h⟩
  | cons φ L ih =>
      intro r proj hsurj
      by_cases hall : ∀ x ∈ LinearMap.ker proj, φ x = 0
      · obtain ⟨r', proj', hsurj', hr', hker', hvan⟩ := ih r proj hsurj
        refine ⟨r', proj', hsurj', le_trans hr' (by simp), hker', ?_⟩
        intro ψ hψ x hx
        simp only [List.mem_cons] at hψ
        rcases hψ with rfl | hψ
        · exact hall x (hker' hx)
        · exact hvan ψ hψ x hx
      · push Not at hall
        obtain ⟨w₀, hw₀ker, hw₀ne⟩ := hall
        have hw₀one : φ w₀ = 1 := by
          rcases zmod2_eq_zero_or_one (φ w₀) with h | h
          · exact absurd h hw₀ne
          · exact h
        let proj₁ : 𝔽₂ n →ₗ[ZMod 2] 𝔽₂ (r + 1) :=
          { toFun := fun x => Fin.snoc (proj x) (φ x)
            map_add' := fun x y => by
              ext i
              refine Fin.lastCases ?_ ?_ i
              · simp [Fin.snoc_last, map_add]
              · intro j
                simp [Fin.snoc_castSucc, map_add]
            map_smul' := fun c x => by
              ext i
              refine Fin.lastCases ?_ ?_ i
              · simp [Fin.snoc_last, map_smul]
              · intro j
                simp [Fin.snoc_castSucc, map_smul] }
        have hsurj₁ : Function.Surjective proj₁ := by
          intro v
          obtain ⟨x, hx⟩ := hsurj (Fin.init v)
          by_cases hφ : φ x = v (Fin.last r)
          · refine ⟨x, ?_⟩
            ext i
            refine Fin.lastCases ?_ ?_ i
            · simp [proj₁, Fin.snoc_last, hφ]
            · intro j
              simpa [proj₁, Fin.snoc_castSucc, Fin.init] using congrFun hx j
          · refine ⟨x + w₀, ?_⟩
            ext i
            refine Fin.lastCases ?_ ?_ i
            · change (Fin.snoc (proj (x + w₀)) (φ (x + w₀)) : 𝔽₂ (r + 1)) (Fin.last r) = v (Fin.last r)
              rw [Fin.snoc_last, map_add, hw₀one]
              rcases zmod2_eq_zero_or_one (φ x) with ha | ha <;>
                rcases zmod2_eq_zero_or_one (v (Fin.last r)) with hb | hb
              · exact absurd (ha.trans hb.symm) hφ
              · rw [ha, hb, zero_add]
              · rw [ha, hb, zmod2_add_self]
              · exact absurd (ha.trans hb.symm) hφ
            · intro j
              have hw0j : proj w₀ j = 0 := by
                have := congrFun (LinearMap.mem_ker.mp hw₀ker) j
                simpa using this
              have hxj : proj x j = v j.castSucc := congrFun hx j
              simp [proj₁, Fin.snoc_castSucc, map_add, hxj, hw0j]
        have hker₁ : LinearMap.ker proj₁ ≤ LinearMap.ker proj := by
          intro x hx
          rw [LinearMap.mem_ker] at hx ⊢
          ext j
          have := congrFun hx j.castSucc
          simpa [proj₁, Fin.snoc_castSucc] using this
        have hvan₁ : ∀ x ∈ LinearMap.ker proj₁, φ x = 0 := by
          intro x hx
          rw [LinearMap.mem_ker] at hx
          have := congrFun hx (Fin.last r)
          simpa [proj₁, Fin.snoc_last] using this
        obtain ⟨r', proj', hsurj', hr', hker', hvan⟩ := ih (r + 1) proj₁ hsurj₁
        refine ⟨r', proj', hsurj', ?_, le_trans hker' hker₁, ?_⟩
        · simp only [List.length_cons]
          omega
        · intro ψ hψ x hx
          simp only [List.mem_cons] at hψ
          rcases hψ with rfl | hψ
          · exact hvan₁ x (hker' hx)
          · exact hvan ψ hψ x hx

private lemma factor_through_ker {n r r' : ℕ}
    (proj : 𝔽₂ n →ₗ[ZMod 2] 𝔽₂ r) (proj' : 𝔽₂ n →ₗ[ZMod 2] 𝔽₂ r')
    (hsurj : Function.Surjective proj) (hsurj' : Function.Surjective proj')
    (hker : LinearMap.ker proj' ≤ LinearMap.ker proj) :
    ∃ q : 𝔽₂ r' →ₗ[ZMod 2] 𝔽₂ r,
      Function.Surjective q ∧ (∀ x : 𝔽₂ n, q (proj' x) = proj x) := by
  classical
  let σ : 𝔽₂ r' → 𝔽₂ n := fun u' => Classical.choose (hsurj' u')
  have hσ : ∀ u', proj' (σ u') = u' := fun u' => Classical.choose_spec (hsurj' u')
  have hwell : ∀ x y : 𝔽₂ n, proj' x = proj' y → proj x = proj y := by
    intro x y hxy
    have hmem : x - y ∈ LinearMap.ker proj' := by
      rw [LinearMap.mem_ker, map_sub, hxy, sub_self]
    have hmem2 := hker hmem
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at hmem2
    exact hmem2
  let q : 𝔽₂ r' →ₗ[ZMod 2] 𝔽₂ r :=
    { toFun := fun u' => proj (σ u')
      map_add' := fun u' v' => by
        have := hwell (σ (u' + v')) (σ u' + σ v') (by rw [map_add, hσ, hσ, hσ])
        rw [this, map_add]
      map_smul' := fun c u' => by
        have := hwell (σ (c • u')) (c • σ u') (by rw [map_smul, hσ, hσ])
        rw [this, map_smul, RingHom.id_apply] }
  refine ⟨q, ?_, ?_⟩
  · intro u
    obtain ⟨x, hx⟩ := hsurj u
    refine ⟨proj' x, ?_⟩
    have := hwell (σ (proj' x)) x (hσ (proj' x))
    simpa [q, hx] using this
  · intro x
    exact hwell (σ (proj' x)) x (hσ (proj' x))

end F2LinearAlgebra

section WalshFourier

private def walshChar {n : ℕ} {W : Submodule (ZMod 2) (𝔽₂ n)}
    (ξ : W →ₗ[ZMod 2] ZMod 2) (w : W) : ℝ :=
  if ξ w = 0 then 1 else -1

private lemma walshChar_zero_left {n : ℕ} {W : Submodule (ZMod 2) (𝔽₂ n)} (w : W) :
    walshChar (0 : W →ₗ[ZMod 2] ZMod 2) w = 1 := by
  simp [walshChar]

private lemma walshChar_zero_right {n : ℕ} {W : Submodule (ZMod 2) (𝔽₂ n)}
    (ξ : W →ₗ[ZMod 2] ZMod 2) :
    walshChar ξ 0 = 1 := by
  simp [walshChar]

private lemma abs_walshChar {n : ℕ} {W : Submodule (ZMod 2) (𝔽₂ n)}
    (ξ : W →ₗ[ZMod 2] ZMod 2) (w : W) :
    |walshChar ξ w| = 1 := by
  unfold walshChar
  split_ifs <;> norm_num

private lemma walshChar_add_right {n : ℕ} {W : Submodule (ZMod 2) (𝔽₂ n)}
    (ξ : W →ₗ[ZMod 2] ZMod 2) (w₁ w₂ : W) :
    walshChar ξ (w₁ + w₂) = walshChar ξ w₁ * walshChar ξ w₂ := by
  unfold walshChar
  rw [map_add]
  rcases zmod2_eq_zero_or_one (ξ w₁) with h₁ | h₁ <;>
    rcases zmod2_eq_zero_or_one (ξ w₂) with h₂ | h₂ <;>
    rw [h₁, h₂]
  · simp
  · simp
  · simp
  · have h : (1 + 1 : ZMod 2) = 0 := zmod2_add_self 1
    simp [h]

private lemma walshChar_add_left {n : ℕ} {W : Submodule (ZMod 2) (𝔽₂ n)}
    (ξ₁ ξ₂ : W →ₗ[ZMod 2] ZMod 2) (w : W) :
    walshChar (ξ₁ + ξ₂) w = walshChar ξ₁ w * walshChar ξ₂ w := by
  unfold walshChar
  rw [LinearMap.add_apply]
  rcases zmod2_eq_zero_or_one (ξ₁ w) with h₁ | h₁ <;>
    rcases zmod2_eq_zero_or_one (ξ₂ w) with h₂ | h₂ <;>
    rw [h₁, h₂]
  · simp
  · simp
  · simp
  · have h : (1 + 1 : ZMod 2) = 0 := zmod2_add_self 1
    simp [h]

private noncomputable instance instFintypeWDual {n : ℕ} (W : Submodule (ZMod 2) (𝔽₂ n)) :
    Fintype (W →ₗ[ZMod 2] ZMod 2) := by
  classical
  haveI : Finite (W →ₗ[ZMod 2] ZMod 2) :=
    Finite.of_injective (fun (ξ : W →ₗ[ZMod 2] ZMod 2) => (ξ : W → ZMod 2))
      DFunLike.coe_injective
  exact Fintype.ofFinite (W →ₗ[ZMod 2] ZMod 2)

private lemma sum_walshChar_right {n : ℕ} {W : Submodule (ZMod 2) (𝔽₂ n)}
    (ξ : W →ₗ[ZMod 2] ZMod 2) :
    ∑ w : W, walshChar ξ w = if ξ = 0 then (Fintype.card W : ℝ) else 0 := by
  by_cases hξ : ξ = 0
  · subst hξ
    simp [walshChar_zero_left]
  · simp only [hξ, ↓reduceIte]
    have hne : ∃ w₀ : W, ξ w₀ ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hξ (LinearMap.ext hall)
    obtain ⟨w₀, hw₀⟩ := hne
    have hchar : walshChar ξ w₀ = -1 := by simp [walshChar, hw₀]
    have hinv : ∑ w : W, walshChar ξ w = ∑ w : W, walshChar ξ (w + w₀) :=
      (Equiv.sum_comp (Equiv.addRight w₀) (fun w => walshChar ξ w)).symm
    have hneg : ∑ w : W, walshChar ξ w = - ∑ w : W, walshChar ξ w := by
      calc ∑ w : W, walshChar ξ w
          = ∑ w : W, walshChar ξ (w + w₀) := hinv
        _ = ∑ w : W, walshChar ξ w * walshChar ξ w₀ := by
            simp_rw [walshChar_add_right]
        _ = ∑ w : W, walshChar ξ w * (-1) := by simp_rw [hchar]
        _ = - ∑ w : W, walshChar ξ w := by simp
    linarith

private lemma exists_dual_ne_zero {n : ℕ} {W : Submodule (ZMod 2) (𝔽₂ n)}
    {w : W} (hw : w ≠ 0) : ∃ ξ : W →ₗ[ZMod 2] ZMod 2, ξ w ≠ 0 := by
  have hval : (w : 𝔽₂ n) ≠ 0 := fun h => hw (Subtype.ext h)
  have hcoord : ∃ i : Fin n, (w : 𝔽₂ n) i ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hval (funext hall)
  obtain ⟨i, hi⟩ := hcoord
  refine ⟨(LinearMap.proj i).comp W.subtype, ?_⟩
  simpa using hi

private lemma sum_walshChar_left {n : ℕ} {W : Submodule (ZMod 2) (𝔽₂ n)}
    (w : W) :
    ∑ ξ : (W →ₗ[ZMod 2] ZMod 2), walshChar ξ w =
      if w = 0 then (Fintype.card (W →ₗ[ZMod 2] ZMod 2) : ℝ) else 0 := by
  by_cases hw : w = 0
  · subst hw
    simp [walshChar_zero_right]
  · simp only [hw, ↓reduceIte]
    obtain ⟨ξ₀, hξ₀⟩ := exists_dual_ne_zero hw
    have hchar : walshChar ξ₀ w = -1 := by simp [walshChar, hξ₀]
    have hinv :
        ∑ ξ : (W →ₗ[ZMod 2] ZMod 2), walshChar ξ w =
          ∑ ξ : (W →ₗ[ZMod 2] ZMod 2), walshChar (ξ + ξ₀) w :=
      (Equiv.sum_comp (Equiv.addRight ξ₀) (fun ξ => walshChar ξ w)).symm
    have hneg :
        ∑ ξ : (W →ₗ[ZMod 2] ZMod 2), walshChar ξ w =
          - ∑ ξ : (W →ₗ[ZMod 2] ZMod 2), walshChar ξ w := by
      calc ∑ ξ : (W →ₗ[ZMod 2] ZMod 2), walshChar ξ w
          = ∑ ξ : (W →ₗ[ZMod 2] ZMod 2), walshChar (ξ + ξ₀) w := hinv
        _ = ∑ ξ : (W →ₗ[ZMod 2] ZMod 2), walshChar ξ w * walshChar ξ₀ w := by
            simp_rw [walshChar_add_left]
        _ = ∑ ξ : (W →ₗ[ZMod 2] ZMod 2), walshChar ξ w * (-1) := by simp_rw [hchar]
        _ = - ∑ ξ : (W →ₗ[ZMod 2] ZMod 2), walshChar ξ w := by simp
    linarith

private lemma card_dual_eq {n : ℕ} (W : Submodule (ZMod 2) (𝔽₂ n)) :
    (Fintype.card (W →ₗ[ZMod 2] ZMod 2) : ℝ) = (Fintype.card W : ℝ) := by
  classical
  calc (Fintype.card (W →ₗ[ZMod 2] ZMod 2) : ℝ)
      = ∑ w : W, (if w = 0 then (Fintype.card (W →ₗ[ZMod 2] ZMod 2) : ℝ) else 0) := by
          simp
    _ = ∑ w : W, ∑ ξ : (W →ₗ[ZMod 2] ZMod 2), walshChar ξ w := by
          refine sum_congr rfl fun w _ => (sum_walshChar_left w).symm
    _ = ∑ ξ : (W →ₗ[ZMod 2] ZMod 2), ∑ w : W, walshChar ξ w := sum_comm
    _ = ∑ ξ : (W →ₗ[ZMod 2] ZMod 2), (if ξ = 0 then (Fintype.card W : ℝ) else 0) := by
          refine sum_congr rfl fun ξ _ => sum_walshChar_right ξ
    _ = (Fintype.card W : ℝ) := by simp

private noncomputable def fourierCoeff {n : ℕ} (W : Submodule (ZMod 2) (𝔽₂ n))
    (S : Finset W) (ξ : W →ₗ[ZMod 2] ZMod 2) : ℝ :=
  (∑ w ∈ S, walshChar ξ w) / (Fintype.card W : ℝ)

private lemma fourierCoeff_zero {n : ℕ} (W : Submodule (ZMod 2) (𝔽₂ n))
    (S : Finset W) :
    fourierCoeff W S 0 = (S.card : ℝ) / (Fintype.card W : ℝ) := by
  simp [fourierCoeff, walshChar_zero_left]

private lemma w_add_self {n : ℕ} {W : Submodule (ZMod 2) (𝔽₂ n)} (w : W) : w + w = 0 :=
  Subtype.ext (f2_add_self (w : 𝔽₂ n))

private lemma w_add_eq_zero_iff {n : ℕ} {W : Submodule (ZMod 2) (𝔽₂ n)} (w₁ w₂ : W) :
    w₁ + w₂ = 0 ↔ w₁ = w₂ := by
  constructor
  · intro h
    calc w₁ = w₁ + (w₂ + w₂) := by rw [w_add_self, add_zero]
      _ = (w₁ + w₂) + w₂ := by rw [add_assoc]
      _ = w₂ := by rw [h, zero_add]
  · rintro rfl
    exact w_add_self w₁

private lemma parseval_walsh {n : ℕ} (W : Submodule (ZMod 2) (𝔽₂ n))
    (S : Finset W) :
    ∑ ξ : (W →ₗ[ZMod 2] ZMod 2), fourierCoeff W S ξ ^ 2 = (S.card : ℝ) / (Fintype.card W : ℝ) := by
  classical
  have hW_pos : (0 : ℝ) < Fintype.card W :=
    Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨0⟩)
  have hsum :
      (∑ ξ : (W →ₗ[ZMod 2] ZMod 2), (∑ w ∈ S, walshChar ξ w) ^ 2) =
        (S.card : ℝ) * (Fintype.card W : ℝ) := by
    calc (∑ ξ : (W →ₗ[ZMod 2] ZMod 2), (∑ w ∈ S, walshChar ξ w) ^ 2)
        = ∑ ξ : (W →ₗ[ZMod 2] ZMod 2), ∑ w₁ ∈ S, ∑ w₂ ∈ S, walshChar ξ (w₁ + w₂) := by
            refine sum_congr rfl fun ξ _ => ?_
            rw [sq, sum_mul]
            refine sum_congr rfl fun w₁ _ => ?_
            rw [mul_sum]
            refine sum_congr rfl fun w₂ _ => (walshChar_add_right ξ w₁ w₂).symm
      _ = ∑ w₁ ∈ S, ∑ w₂ ∈ S, ∑ ξ : (W →ₗ[ZMod 2] ZMod 2), walshChar ξ (w₁ + w₂) := by
            rw [sum_comm]
            refine sum_congr rfl fun w₁ _ => sum_comm
      _ = ∑ w₁ ∈ S, ∑ w₂ ∈ S,
            (if w₁ + w₂ = 0 then (Fintype.card (W →ₗ[ZMod 2] ZMod 2) : ℝ) else 0) := by
            refine sum_congr rfl fun w₁ _ => sum_congr rfl fun w₂ _ => sum_walshChar_left (w₁ + w₂)
      _ = ∑ w₁ ∈ S, ∑ w₂ ∈ S, (if w₁ = w₂ then (Fintype.card W : ℝ) else 0) := by
            refine sum_congr rfl fun w₁ _ => sum_congr rfl fun w₂ _ => ?_
            simp_rw [w_add_eq_zero_iff, card_dual_eq W]
      _ = ∑ w₁ ∈ S, (Fintype.card W : ℝ) := by
            refine sum_congr rfl fun w₁ hw₁ => ?_
            simp [hw₁]
      _ = (S.card : ℝ) * (Fintype.card W : ℝ) := by simp
  calc ∑ ξ : (W →ₗ[ZMod 2] ZMod 2), fourierCoeff W S ξ ^ 2
      = (∑ ξ : (W →ₗ[ZMod 2] ZMod 2), (∑ w ∈ S, walshChar ξ w) ^ 2) / (Fintype.card W : ℝ) ^ 2 := by
          simp [fourierCoeff, div_pow, ← sum_div]
    _ = ((S.card : ℝ) * (Fintype.card W : ℝ)) / (Fintype.card W : ℝ) ^ 2 := by rw [hsum]
    _ = (S.card : ℝ) / (Fintype.card W : ℝ) := by
          field_simp [hW_pos.ne']

private lemma triple_count_via_fourier {n : ℕ} (W : Submodule (ZMod 2) (𝔽₂ n))
    (S₁ S₂ S₃ : Finset W) (w₀ : W) :
    (((S₁ ×ˢ (S₂ ×ˢ S₃)).filter (fun p => p.1 + p.2.1 + p.2.2 = w₀)).card : ℝ) =
      (Fintype.card W : ℝ) ^ 2 *
        ∑ ξ : (W →ₗ[ZMod 2] ZMod 2),
          walshChar ξ w₀ * fourierCoeff W S₁ ξ * fourierCoeff W S₂ ξ * fourierCoeff W S₃ ξ := by
  classical
  have hW_pos : (0 : ℝ) < Fintype.card W := Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨0⟩)
  have hstep :
      (((S₁ ×ˢ (S₂ ×ˢ S₃)).filter (fun p => p.1 + p.2.1 + p.2.2 = w₀)).card : ℝ) *
        (Fintype.card W : ℝ) =
        (Fintype.card W : ℝ) ^ 3 *
          ∑ ξ : (W →ₗ[ZMod 2] ZMod 2),
            walshChar ξ w₀ * fourierCoeff W S₁ ξ * fourierCoeff W S₂ ξ * fourierCoeff W S₃ ξ := by
    have heq : ∀ p : W × W × W,
        (p.1 + p.2.1 + p.2.2 = w₀ ↔ p.1 + p.2.1 + p.2.2 + w₀ = 0) := fun p => by
      simpa using (w_add_eq_zero_iff (p.1 + p.2.1 + p.2.2) w₀).symm
    calc (((S₁ ×ˢ (S₂ ×ˢ S₃)).filter (fun p => p.1 + p.2.1 + p.2.2 = w₀)).card : ℝ) *
          (Fintype.card W : ℝ)
        = ∑ p ∈ S₁ ×ˢ (S₂ ×ˢ S₃),
            if p.1 + p.2.1 + p.2.2 + w₀ = 0 then (Fintype.card W : ℝ) else 0 := by
            rw [card_filter, Nat.cast_sum, sum_mul]
            refine sum_congr rfl fun p _ => ?_
            simp_rw [← heq p]
            split_ifs <;> simp
      _ = ∑ p ∈ S₁ ×ˢ (S₂ ×ˢ S₃),
            ∑ ξ : (W →ₗ[ZMod 2] ZMod 2), walshChar ξ (p.1 + p.2.1 + p.2.2 + w₀) := by
            refine sum_congr rfl fun p _ => ?_
            rw [sum_walshChar_left, card_dual_eq W]
      _ = ∑ ξ : (W →ₗ[ZMod 2] ZMod 2), ∑ p ∈ S₁ ×ˢ (S₂ ×ˢ S₃),
            walshChar ξ (p.1 + p.2.1 + p.2.2 + w₀) := sum_comm
      _ = ∑ ξ : (W →ₗ[ZMod 2] ZMod 2),
            walshChar ξ w₀ * (∑ w₁ ∈ S₁, walshChar ξ w₁) *
              (∑ w₂ ∈ S₂, walshChar ξ w₂) * (∑ w₃ ∈ S₃, walshChar ξ w₃) := by
            refine sum_congr rfl fun ξ _ => ?_
            rw [sum_product]
            simp_rw [sum_product, walshChar_add_right]
            trans ∑ w₁ ∈ S₁, (walshChar ξ w₀ * walshChar ξ w₁) *
                ((∑ w₂ ∈ S₂, walshChar ξ w₂) * (∑ w₃ ∈ S₃, walshChar ξ w₃))
            · refine sum_congr rfl fun w₁ _ => ?_
              rw [sum_mul, mul_sum]
              refine sum_congr rfl fun w₂ _ => ?_
              rw [← mul_assoc, mul_sum]
              refine sum_congr rfl fun w₃ _ => by ring
            · rw [← sum_mul, ← mul_sum]
              ring
      _ = (Fintype.card W : ℝ) ^ 3 *
            ∑ ξ : (W →ₗ[ZMod 2] ZMod 2),
              walshChar ξ w₀ * fourierCoeff W S₁ ξ * fourierCoeff W S₂ ξ * fourierCoeff W S₃ ξ := by
            rw [mul_sum]
            refine sum_congr rfl fun ξ _ => ?_
            simp only [fourierCoeff]
            field_simp [hW_pos.ne']
  apply mul_right_cancel₀ hW_pos.ne'
  rw [hstep]
  ring

private lemma triple_count_bound {n : ℕ} (W : Submodule (ZMod 2) (𝔽₂ n))
    (S₁ S₂ S₃ : Finset W) (w₀ : W) {η : ℝ} (hη : 0 ≤ η)
    (hunif : ∀ ξ : W →ₗ[ZMod 2] ZMod 2, ξ ≠ 0 → |fourierCoeff W S₁ ξ| ≤ η) :
    (((S₁ ×ˢ (S₂ ×ˢ S₃)).filter (fun p => p.1 + p.2.1 + p.2.2 = w₀)).card : ℝ) ≤
      (Fintype.card W : ℝ) ^ 2 *
        ((S₁.card : ℝ) / (Fintype.card W : ℝ) *
          ((S₂.card : ℝ) / (Fintype.card W : ℝ)) *
          ((S₃.card : ℝ) / (Fintype.card W : ℝ)) + η) := by
  classical
  rw [triple_count_via_fourier W S₁ S₂ S₃ w₀]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  have hsplit :
      (∑ ξ : (W →ₗ[ZMod 2] ZMod 2),
        walshChar ξ w₀ * fourierCoeff W S₁ ξ * fourierCoeff W S₂ ξ * fourierCoeff W S₃ ξ) =
      (S₁.card : ℝ) / (Fintype.card W : ℝ) *
        ((S₂.card : ℝ) / (Fintype.card W : ℝ)) *
        ((S₃.card : ℝ) / (Fintype.card W : ℝ)) +
      ∑ ξ ∈ (univ : Finset (W →ₗ[ZMod 2] ZMod 2)).erase 0,
        walshChar ξ w₀ * fourierCoeff W S₁ ξ * fourierCoeff W S₂ ξ * fourierCoeff W S₃ ξ := by
    rw [← add_sum_erase (univ : Finset (W →ₗ[ZMod 2] ZMod 2)) _ (mem_univ 0)]
    simp [walshChar_zero_left, fourierCoeff_zero]
  rw [hsplit]
  gcongr
  have hterm : ∀ ξ ∈ (univ : Finset (W →ₗ[ZMod 2] ZMod 2)).erase 0,
      walshChar ξ w₀ * fourierCoeff W S₁ ξ * fourierCoeff W S₂ ξ * fourierCoeff W S₃ ξ ≤
        η * (|fourierCoeff W S₂ ξ| * |fourierCoeff W S₃ ξ|) := by
    intro ξ hξ
    have hξ0 : ξ ≠ 0 := (mem_erase.mp hξ).1
    calc walshChar ξ w₀ * fourierCoeff W S₁ ξ * fourierCoeff W S₂ ξ * fourierCoeff W S₃ ξ
        ≤ |walshChar ξ w₀ * fourierCoeff W S₁ ξ * fourierCoeff W S₂ ξ * fourierCoeff W S₃ ξ| :=
            le_abs_self _
      _ = |walshChar ξ w₀| * |fourierCoeff W S₁ ξ| * |fourierCoeff W S₂ ξ| * |fourierCoeff W S₃ ξ| := by
            simp [abs_mul]
      _ = |fourierCoeff W S₁ ξ| * (|fourierCoeff W S₂ ξ| * |fourierCoeff W S₃ ξ|) := by
            rw [abs_walshChar, one_mul, mul_assoc]
      _ ≤ η * (|fourierCoeff W S₂ ξ| * |fourierCoeff W S₃ ξ|) :=
            mul_le_mul_of_nonneg_right (hunif ξ hξ0) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hcs_sq :
      (∑ ξ : (W →ₗ[ZMod 2] ZMod 2), |fourierCoeff W S₂ ξ| * |fourierCoeff W S₃ ξ|) ^ 2 ≤ 1 := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset (W →ₗ[ZMod 2] ZMod 2))
      (fun ξ => |fourierCoeff W S₂ ξ|) (fun ξ => |fourierCoeff W S₃ ξ|)
    have hp₂ : ∑ ξ : (W →ₗ[ZMod 2] ZMod 2), |fourierCoeff W S₂ ξ| ^ 2 ≤ 1 := by
      simp_rw [sq_abs]
      rw [parseval_walsh]
      have hcard_le : (S₂.card : ℝ) ≤ (Fintype.card W : ℝ) := by
        exact_mod_cast Finset.card_le_univ S₂
      have hW_pos : (0 : ℝ) < Fintype.card W := Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨0⟩)
      exact (div_le_one hW_pos).mpr hcard_le
    have hp₃ : ∑ ξ : (W →ₗ[ZMod 2] ZMod 2), |fourierCoeff W S₃ ξ| ^ 2 ≤ 1 := by
      simp_rw [sq_abs]
      rw [parseval_walsh]
      have hcard_le : (S₃.card : ℝ) ≤ (Fintype.card W : ℝ) := by
        exact_mod_cast Finset.card_le_univ S₃
      have hW_pos : (0 : ℝ) < Fintype.card W := Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨0⟩)
      exact (div_le_one hW_pos).mpr hcard_le
    have hp₂0 : 0 ≤ ∑ ξ : (W →ₗ[ZMod 2] ZMod 2), |fourierCoeff W S₂ ξ| ^ 2 :=
      sum_nonneg fun _ _ => sq_nonneg _
    have hp₃0 : 0 ≤ ∑ ξ : (W →ₗ[ZMod 2] ZMod 2), |fourierCoeff W S₃ ξ| ^ 2 :=
      sum_nonneg fun _ _ => sq_nonneg _
    exact hcs.trans (mul_le_one₀ hp₂ hp₃0 hp₃)
  have hcs :
      (∑ ξ : (W →ₗ[ZMod 2] ZMod 2), |fourierCoeff W S₂ ξ| * |fourierCoeff W S₃ ξ|) ≤ 1 := by
    nlinarith [sum_nonneg (fun ξ (_ : ξ ∈ univ) =>
      mul_nonneg (abs_nonneg (fourierCoeff W S₂ ξ)) (abs_nonneg (fourierCoeff W S₃ ξ)))]
  calc ∑ ξ ∈ (univ : Finset (W →ₗ[ZMod 2] ZMod 2)).erase 0,
          walshChar ξ w₀ * fourierCoeff W S₁ ξ * fourierCoeff W S₂ ξ * fourierCoeff W S₃ ξ
      ≤ ∑ ξ ∈ (univ : Finset (W →ₗ[ZMod 2] ZMod 2)).erase 0,
          η * (|fourierCoeff W S₂ ξ| * |fourierCoeff W S₃ ξ|) := sum_le_sum hterm
    _ ≤ ∑ ξ : (W →ₗ[ZMod 2] ZMod 2),
          η * (|fourierCoeff W S₂ ξ| * |fourierCoeff W S₃ ξ|) :=
          sum_le_univ_sum_of_nonneg fun ξ =>
            mul_nonneg hη (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = η * ∑ ξ : (W →ₗ[ZMod 2] ZMod 2), |fourierCoeff W S₂ ξ| * |fourierCoeff W S₃ ξ| := by
          rw [mul_sum]
    _ ≤ η * 1 := mul_le_mul_of_nonneg_left hcs hη
    _ = η := mul_one η

end WalshFourier

/-
## Section 3: Partition Variance, Two-Energy Regularity, and Bounded Termination
-/

section PartitionVariance

private noncomputable def setDens {α : Type*} [DecidableEq α] (M S : Finset α) : ℝ :=
  if S.card = 0 then 0 else ((M ∩ S).card : ℝ) / (S.card : ℝ)

private lemma setDens_nonneg {α : Type*} [DecidableEq α] (M S : Finset α) :
    0 ≤ setDens M S := by
  unfold setDens
  split_ifs <;> positivity

private lemma setDens_le_one {α : Type*} [DecidableEq α] (M S : Finset α) :
    setDens M S ≤ 1 := by
  unfold setDens
  split_ifs with h
  · norm_num
  · rw [div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h))]
    exact_mod_cast Finset.card_le_card inter_subset_right

private lemma card_mul_setDens {α : Type*} [DecidableEq α] (M S : Finset α) :
    (S.card : ℝ) * setDens M S = ((M ∩ S).card : ℝ) := by
  unfold setDens
  split_ifs with h
  · have hS : S = ∅ := Finset.card_eq_zero.mp h
    simp [hS]
  · have hpos : (S.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h
    field_simp [hpos]

private lemma sum_card_parts_eq {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (s : Finset ι) (parts : ι → Finset α) (S : Finset α)
    (hcover : s.biUnion parts = S)
    (hdisj : (s : Set ι).PairwiseDisjoint parts) :
    ∑ t ∈ s, ((parts t).card : ℝ) = (S.card : ℝ) := by
  exact_mod_cast (by rw [← hcover, card_biUnion hdisj] : ∑ t ∈ s, (parts t).card = S.card)

private lemma sum_card_mul_setDens_eq {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (s : Finset ι) (parts : ι → Finset α) (S M : Finset α)
    (hcover : s.biUnion parts = S)
    (hdisj : (s : Set ι).PairwiseDisjoint parts) :
    ∑ t ∈ s, ((parts t).card : ℝ) * setDens M (parts t) = (S.card : ℝ) * setDens M S := by
  simp_rw [card_mul_setDens, ← Nat.cast_sum]
  congr 1
  have hinter : M ∩ S = s.biUnion (fun t => M ∩ parts t) := by
    rw [← hcover, inter_biUnion]
  have hdisjM : (s : Set ι).PairwiseDisjoint (fun t => M ∩ parts t) :=
    fun a ha b hb hab => (hdisj ha hb hab).mono inter_subset_right inter_subset_right
  rw [hinter, card_biUnion hdisjM]

private lemma sum_card_mul_setDens_sub_sq {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (s : Finset ι) (parts : ι → Finset α) (S M : Finset α)
    (hcover : s.biUnion parts = S)
    (hdisj : (s : Set ι).PairwiseDisjoint parts) (c : ℝ) :
    ∑ t ∈ s, ((parts t).card : ℝ) * (setDens M (parts t) - c) ^ 2 =
      (∑ t ∈ s, ((parts t).card : ℝ) * setDens M (parts t) ^ 2) -
        2 * c * ((S.card : ℝ) * setDens M S) + c ^ 2 * (S.card : ℝ) := by
  have h1 := sum_card_mul_setDens_eq s parts S M hcover hdisj
  have h2 := sum_card_parts_eq s parts S hcover hdisj
  calc ∑ t ∈ s, ((parts t).card : ℝ) * (setDens M (parts t) - c) ^ 2
      = ∑ t ∈ s, (((parts t).card : ℝ) * setDens M (parts t) ^ 2 -
          2 * c * (((parts t).card : ℝ) * setDens M (parts t)) +
          c ^ 2 * ((parts t).card : ℝ)) := by
          refine sum_congr rfl fun t _ => by ring
    _ = (∑ t ∈ s, ((parts t).card : ℝ) * setDens M (parts t) ^ 2) -
          2 * c * (∑ t ∈ s, ((parts t).card : ℝ) * setDens M (parts t)) +
          c ^ 2 * (∑ t ∈ s, ((parts t).card : ℝ)) := by
          simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum]
    _ = _ := by rw [h1, h2]

private lemma sum_card_mul_setDens_sq_ge {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (s : Finset ι) (parts : ι → Finset α) (S M : Finset α)
    (hcover : s.biUnion parts = S)
    (hdisj : (s : Set ι).PairwiseDisjoint parts) :
    (S.card : ℝ) * setDens M S ^ 2 ≤
      ∑ t ∈ s, ((parts t).card : ℝ) * setDens M (parts t) ^ 2 := by
  have hvar := sum_card_mul_setDens_sub_sq s parts S M hcover hdisj (setDens M S)
  have hnn : 0 ≤ ∑ t ∈ s, ((parts t).card : ℝ) * (setDens M (parts t) - setDens M S) ^ 2 :=
    sum_nonneg fun t _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  linarith

private lemma sum_card_mul_setDens_sq_ge_add {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (s : Finset ι) (parts : ι → Finset α) (S M U : Finset α)
    (hcover : s.biUnion parts = S)
    (hdisj : (s : Set ι).PairwiseDisjoint parts)
    (hUS : U ⊆ S)
    (hrefine : ∀ t ∈ s, parts t ⊆ U ∨ Disjoint (parts t) U) :
    (S.card : ℝ) * setDens M S ^ 2 +
        (U.card : ℝ) * (setDens M U - setDens M S) ^ 2 ≤
      ∑ t ∈ s, ((parts t).card : ℝ) * setDens M (parts t) ^ 2 := by
  classical
  let sU : Finset ι := s.filter (fun t => parts t ⊆ U)
  have hcoverU : sU.biUnion parts = U := by
    ext x
    simp only [mem_biUnion, mem_filter, sU]
    constructor
    · rintro ⟨t, ⟨_, hsub⟩, hx⟩
      exact hsub hx
    · intro hxU
      have hxS : x ∈ S := hUS hxU
      rw [← hcover, mem_biUnion] at hxS
      rcases hxS with ⟨t, hts, hxt⟩
      refine ⟨t, ⟨hts, ?_⟩, hxt⟩
      rcases hrefine t hts with hsub | hdis
      · exact hsub
      · exact absurd hxU (Finset.disjoint_left.mp hdis hxt)
  have hdisjU : (sU : Set ι).PairwiseDisjoint parts :=
    hdisj.subset (Finset.coe_subset.mpr (filter_subset _ _))
  have hvarS := sum_card_mul_setDens_sub_sq s parts S M hcover hdisj (setDens M S)
  have hvarU := sum_card_mul_setDens_sub_sq sU parts U M hcoverU hdisjU (setDens M S)
  have hgeU : (U.card : ℝ) * setDens M U ^ 2 ≤
      ∑ t ∈ sU, ((parts t).card : ℝ) * setDens M (parts t) ^ 2 :=
    sum_card_mul_setDens_sq_ge sU parts U M hcoverU hdisjU
  have hsub_le :
      ∑ t ∈ sU, ((parts t).card : ℝ) * (setDens M (parts t) - setDens M S) ^ 2 ≤
        ∑ t ∈ s, ((parts t).card : ℝ) * (setDens M (parts t) - setDens M S) ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ =>
      mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have hquadU : (U.card : ℝ) * (setDens M U - setDens M S) ^ 2 =
      (U.card : ℝ) * setDens M U ^ 2 - 2 * setDens M S * ((U.card : ℝ) * setDens M U) +
        setDens M S ^ 2 * (U.card : ℝ) := by ring
  linarith

private lemma sum_card_mul_setDens_sq_ge_fourier {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (s : Finset ι) (parts : ι → Finset α) (S M : Finset α)
    (hcover : s.biUnion parts = S)
    (hdisj : (s : Set ι).PairwiseDisjoint parts)
    (hMS : M ⊆ S) (σ : α → ℝ)
    (hσsq : ∀ x ∈ S, σ x ^ 2 = 1)
    (hσsum : ∑ x ∈ S, σ x = 0)
    (hσconst : ∀ t ∈ s, ∃ v : ℝ, ∀ x ∈ parts t, σ x = v) :
    (∑ x ∈ M, σ x) ^ 2 ≤
      (S.card : ℝ) *
        ((∑ t ∈ s, ((parts t).card : ℝ) * setDens M (parts t) ^ 2) -
          (S.card : ℝ) * setDens M S ^ 2) := by
  classical
  let g : α → ℝ := fun x => ∑ t ∈ s, if x ∈ parts t then setDens M (parts t) - setDens M S else 0
  have hg_on : ∀ t ∈ s, ∀ x ∈ parts t, g x = setDens M (parts t) - setDens M S := by
    intro t ht x hx
    simp only [g]
    rw [← add_sum_erase s _ ht]
    have hrest : ∑ t' ∈ s.erase t, (if x ∈ parts t' then setDens M (parts t') - setDens M S else 0) = 0 := by
      refine sum_eq_zero fun t' ht' => ?_
      have hne : t ≠ t' := (mem_erase.mp ht').1.symm
      have hdis : Disjoint (parts t) (parts t') := hdisj ht (mem_erase.mp ht').2 hne
      have hx' : x ∉ parts t' := Finset.disjoint_left.mp hdis hx
      simp [hx']
    simp [hx, hrest]
  have hsum_gσ : ∑ x ∈ S, g x * σ x = ∑ x ∈ M, σ x := by
    have hsplit : ∑ x ∈ S, g x * σ x = ∑ t ∈ s, ∑ x ∈ parts t, g x * σ x := by
      rw [← hcover, sum_biUnion hdisj]
    rw [hsplit]
    have hterm : ∀ t ∈ s, ∑ x ∈ parts t, g x * σ x =
        (∑ x ∈ M ∩ parts t, σ x) - setDens M S * ∑ x ∈ parts t, σ x := by
      intro t ht
      obtain ⟨v, hv⟩ := hσconst t ht
      have h1 : ∑ x ∈ parts t, g x * σ x =
          ((parts t).card : ℝ) * (setDens M (parts t) - setDens M S) * v := by
        calc ∑ x ∈ parts t, g x * σ x
            = ∑ x ∈ parts t, (setDens M (parts t) - setDens M S) * v := by
                refine sum_congr rfl fun x hx => ?_
                rw [hg_on t ht x hx, hv x hx]
          _ = ((parts t).card : ℝ) * (setDens M (parts t) - setDens M S) * v := by
                simp [mul_assoc]
      have h2 : ∑ x ∈ M ∩ parts t, σ x = ((M ∩ parts t).card : ℝ) * v := by
        calc ∑ x ∈ M ∩ parts t, σ x
            = ∑ _x ∈ M ∩ parts t, v := sum_congr rfl fun x hx => hv x (inter_subset_right hx)
          _ = ((M ∩ parts t).card : ℝ) * v := by simp
      have h3 : ∑ x ∈ parts t, σ x = ((parts t).card : ℝ) * v := by
        calc ∑ x ∈ parts t, σ x
            = ∑ _x ∈ parts t, v := sum_congr rfl fun x hx => hv x hx
          _ = ((parts t).card : ℝ) * v := by simp
      rw [h1, h2, h3, ← card_mul_setDens M (parts t)]
      ring
    calc ∑ t ∈ s, ∑ x ∈ parts t, g x * σ x
        = ∑ t ∈ s, ((∑ x ∈ M ∩ parts t, σ x) - setDens M S * ∑ x ∈ parts t, σ x) :=
            sum_congr rfl hterm
      _ = (∑ t ∈ s, ∑ x ∈ M ∩ parts t, σ x) - setDens M S * ∑ t ∈ s, ∑ x ∈ parts t, σ x := by
            simp only [sum_sub_distrib, ← mul_sum]
      _ = (∑ x ∈ M, σ x) - setDens M S * ∑ x ∈ S, σ x := by
            have hM : M = s.biUnion (fun t => M ∩ parts t) := by
              rw [← inter_biUnion, hcover, inter_eq_left.mpr hMS]
            have hdisjM : (s : Set ι).PairwiseDisjoint (fun t => M ∩ parts t) :=
              fun a ha b hb hab => (hdisj ha hb hab).mono inter_subset_right inter_subset_right
            rw [← sum_biUnion hdisjM, ← hM, ← sum_biUnion hdisj, hcover]
      _ = ∑ x ∈ M, σ x := by rw [hσsum, mul_zero, sub_zero]
  have hsum_gsq : ∑ x ∈ S, g x ^ 2 =
      (∑ t ∈ s, ((parts t).card : ℝ) * setDens M (parts t) ^ 2) -
        (S.card : ℝ) * setDens M S ^ 2 := by
    calc ∑ x ∈ S, g x ^ 2
        = ∑ t ∈ s, ∑ x ∈ parts t, g x ^ 2 := by rw [← hcover, sum_biUnion hdisj]
      _ = ∑ t ∈ s, ((parts t).card : ℝ) * (setDens M (parts t) - setDens M S) ^ 2 := by
            refine sum_congr rfl fun t ht => ?_
            calc ∑ x ∈ parts t, g x ^ 2
                = ∑ _x ∈ parts t, (setDens M (parts t) - setDens M S) ^ 2 :=
                    sum_congr rfl fun x hx => by rw [hg_on t ht x hx]
              _ = ((parts t).card : ℝ) * (setDens M (parts t) - setDens M S) ^ 2 := by simp
      _ = (∑ t ∈ s, ((parts t).card : ℝ) * setDens M (parts t) ^ 2) -
            (S.card : ℝ) * setDens M S ^ 2 := by
            rw [sum_card_mul_setDens_sub_sq s parts S M hcover hdisj (setDens M S)]
            ring
  have hsum_σsq : ∑ x ∈ S, σ x ^ 2 = (S.card : ℝ) := by
    calc ∑ x ∈ S, σ x ^ 2 = ∑ _x ∈ S, (1 : ℝ) := sum_congr rfl hσsq
      _ = (S.card : ℝ) := by simp
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S g σ
  rw [hsum_gσ, hsum_gsq, hsum_σsq, mul_comm _ (S.card : ℝ)] at hcs
  exact hcs

end PartitionVariance

section QuasirandomAndBoxing

private noncomputable def densBip {α β : Type*} [DecidableEq α] [DecidableEq β]
    (E : Finset (α × β)) (X : Finset α) (Y : Finset β) : ℝ :=
  setDens E (X ×ˢ Y)

private lemma densBip_nonneg {α β : Type*} [DecidableEq α] [DecidableEq β]
    (E : Finset (α × β)) (X : Finset α) (Y : Finset β) :
    0 ≤ densBip E X Y :=
  setDens_nonneg E (X ×ˢ Y)

private lemma densBip_le_one {α β : Type*} [DecidableEq α] [DecidableEq β]
    (E : Finset (α × β)) (X : Finset α) (Y : Finset β) :
    densBip E X Y ≤ 1 :=
  setDens_le_one E (X ×ˢ Y)

private lemma card_mul_densBip {α β : Type*} [DecidableEq α] [DecidableEq β]
    (E : Finset (α × β)) (X : Finset α) (Y : Finset β) :
    (X.card : ℝ) * (Y.card : ℝ) * densBip E X Y = ((E ∩ (X ×ˢ Y)).card : ℝ) := by
  unfold densBip
  have h := card_mul_setDens E (X ×ˢ Y)
  rw [card_product, Nat.cast_mul] at h
  exact h

private def IsQuasirandom {α β : Type*} [DecidableEq α] [DecidableEq β]
    (E : Finset (α × β)) (X : Finset α) (Y : Finset β) (ε : ℝ) : Prop :=
  ∀ X' ⊆ X, ∀ Y' ⊆ Y,
    ε * (X.card : ℝ) ≤ (X'.card : ℝ) →
    ε * (Y.card : ℝ) ≤ (Y'.card : ℝ) →
    |densBip E X' Y' - densBip E X Y| ≤ ε

private structure Boxing (n : ℕ) where
  r : ℕ
  proj : 𝔽₂ n →ₗ[ZMod 2] 𝔽₂ r
  hsurj : Function.Surjective proj
  m : ℕ
  hm : 0 < m
  bCol : 𝔽₂ r → 𝔽₂ r → 𝔽₂ n → Fin m
  cCol : 𝔽₂ r → 𝔽₂ r → 𝔽₂ n → Fin m
  dCol : 𝔽₂ r → 𝔽₂ r → 𝔽₂ n → Fin m

private def initialBoxing (n : ℕ) : Boxing n where
  r := 0
  proj := 0
  hsurj := fun _ => ⟨0, Subsingleton.elim _ _⟩
  m := 1
  hm := Nat.one_pos
  bCol := 0
  cCol := 0
  dCol := 0

private def Bpart {n : ℕ} (B : Boxing n) (u v : 𝔽₂ B.r) (i : Fin B.m) : Finset (𝔽₂ n) :=
  (fiber B.proj u).filter (fun x => B.bCol u v x = i)

private def Cpart {n : ℕ} (B : Boxing n) (u v : 𝔽₂ B.r) (j : Fin B.m) : Finset (𝔽₂ n) :=
  (fiber B.proj v).filter (fun y => B.cCol u v y = j)

private def Dpart {n : ℕ} (B : Boxing n) (u v : 𝔽₂ B.r) (k : Fin B.m) : Finset (𝔽₂ n) :=
  (fiber B.proj (u + v)).filter (fun z => B.dCol u v z = k)

private lemma Bpart_cover {n : ℕ} (B : Boxing n) (u v : 𝔽₂ B.r) :
    (univ : Finset (Fin B.m)).biUnion (Bpart B u v) = fiber B.proj u := by
  ext x
  simp [Bpart]

private lemma Bpart_disjoint {n : ℕ} (B : Boxing n) (u v : 𝔽₂ B.r) :
    ((univ : Finset (Fin B.m)) : Set (Fin B.m)).PairwiseDisjoint (Bpart B u v) := by
  intro i _ j _ hij
  refine Finset.disjoint_left.mpr fun x hxi hxj => ?_
  simp only [Bpart, mem_filter] at hxi hxj
  exact hij (hxi.2.symm.trans hxj.2)

private lemma Cpart_cover {n : ℕ} (B : Boxing n) (u v : 𝔽₂ B.r) :
    (univ : Finset (Fin B.m)).biUnion (Cpart B u v) = fiber B.proj v := by
  ext y
  simp [Cpart]

private lemma Cpart_disjoint {n : ℕ} (B : Boxing n) (u v : 𝔽₂ B.r) :
    ((univ : Finset (Fin B.m)) : Set (Fin B.m)).PairwiseDisjoint (Cpart B u v) := by
  intro i _ j _ hij
  refine Finset.disjoint_left.mpr fun y hyi hyj => ?_
  simp only [Cpart, mem_filter] at hyi hyj
  exact hij (hyi.2.symm.trans hyj.2)

private lemma Dpart_cover {n : ℕ} (B : Boxing n) (u v : 𝔽₂ B.r) :
    (univ : Finset (Fin B.m)).biUnion (Dpart B u v) = fiber B.proj (u + v) := by
  ext z
  simp [Dpart]

private lemma Dpart_disjoint {n : ℕ} (B : Boxing n) (u v : 𝔽₂ B.r) :
    ((univ : Finset (Fin B.m)) : Set (Fin B.m)).PairwiseDisjoint (Dpart B u v) := by
  intro i _ j _ hij
  refine Finset.disjoint_left.mpr fun z hzi hzj => ?_
  simp only [Dpart, mem_filter] at hzi hzj
  exact hij (hzi.2.symm.trans hzj.2)

private noncomputable def pB {n : ℕ} (B : Boxing n) (u v : 𝔽₂ B.r) (i : Fin B.m) : ℝ :=
  ((Bpart B u v i).card : ℝ) / (2 ^ (n - B.r) : ℝ)

private noncomputable def pC {n : ℕ} (B : Boxing n) (u v : 𝔽₂ B.r) (j : Fin B.m) : ℝ :=
  ((Cpart B u v j).card : ℝ) / (2 ^ (n - B.r) : ℝ)

private noncomputable def pD {n : ℕ} (B : Boxing n) (u v : 𝔽₂ B.r) (k : Fin B.m) : ℝ :=
  ((Dpart B u v k).card : ℝ) / (2 ^ (n - B.r) : ℝ)

private lemma pB_nonneg {n : ℕ} (B : Boxing n) (u v : 𝔽₂ B.r) (i : Fin B.m) : 0 ≤ pB B u v i := by
  unfold pB; positivity

private lemma pC_nonneg {n : ℕ} (B : Boxing n) (u v : 𝔽₂ B.r) (j : Fin B.m) : 0 ≤ pC B u v j := by
  unfold pC; positivity

private lemma pD_nonneg {n : ℕ} (B : Boxing n) (u v : 𝔽₂ B.r) (k : Fin B.m) : 0 ≤ pD B u v k := by
  unfold pD; positivity

private lemma sum_pB_eq_one {n : ℕ} (B : Boxing n) (u v : 𝔽₂ B.r) :
    ∑ i : Fin B.m, pB B u v i = 1 := by
  have hpow : (2 ^ (n - B.r) : ℝ) ≠ 0 := by positivity
  calc ∑ i : Fin B.m, pB B u v i
      = (∑ i : Fin B.m, ((Bpart B u v i).card : ℝ)) / (2 ^ (n - B.r) : ℝ) := by
          simp [pB, ← sum_div]
    _ = ((fiber B.proj u).card : ℝ) / (2 ^ (n - B.r) : ℝ) := by
          rw [sum_card_parts_eq univ (Bpart B u v) (fiber B.proj u)
            (Bpart_cover B u v) (Bpart_disjoint B u v)]
    _ = 1 := by rw [fiber_card B.proj B.hsurj u]; push_cast; exact div_self hpow

private lemma sum_pC_eq_one {n : ℕ} (B : Boxing n) (u v : 𝔽₂ B.r) :
    ∑ j : Fin B.m, pC B u v j = 1 := by
  have hpow : (2 ^ (n - B.r) : ℝ) ≠ 0 := by positivity
  calc ∑ j : Fin B.m, pC B u v j
      = (∑ j : Fin B.m, ((Cpart B u v j).card : ℝ)) / (2 ^ (n - B.r) : ℝ) := by
          simp [pC, ← sum_div]
    _ = ((fiber B.proj v).card : ℝ) / (2 ^ (n - B.r) : ℝ) := by
          rw [sum_card_parts_eq univ (Cpart B u v) (fiber B.proj v)
            (Cpart_cover B u v) (Cpart_disjoint B u v)]
    _ = 1 := by rw [fiber_card B.proj B.hsurj v]; push_cast; exact div_self hpow

private lemma sum_pD_eq_one {n : ℕ} (B : Boxing n) (u v : 𝔽₂ B.r) :
    ∑ k : Fin B.m, pD B u v k = 1 := by
  have hpow : (2 ^ (n - B.r) : ℝ) ≠ 0 := by positivity
  calc ∑ k : Fin B.m, pD B u v k
      = (∑ k : Fin B.m, ((Dpart B u v k).card : ℝ)) / (2 ^ (n - B.r) : ℝ) := by
          simp [pD, ← sum_div]
    _ = ((fiber B.proj (u + v)).card : ℝ) / (2 ^ (n - B.r) : ℝ) := by
          rw [sum_card_parts_eq univ (Dpart B u v) (fiber B.proj (u + v))
            (Dpart_cover B u v) (Dpart_disjoint B u v)]
    _ = 1 := by rw [fiber_card B.proj B.hsurj (u + v)]; push_cast; exact div_self hpow

private lemma pB_le_one {n : ℕ} (B : Boxing n) (u v : 𝔽₂ B.r) (i : Fin B.m) : pB B u v i ≤ 1 := by
  rw [← sum_pB_eq_one B u v]
  exact single_le_sum (fun i' _ => pB_nonneg B u v i') (mem_univ i)

private lemma pC_le_one {n : ℕ} (B : Boxing n) (u v : 𝔽₂ B.r) (j : Fin B.m) : pC B u v j ≤ 1 := by
  rw [← sum_pC_eq_one B u v]
  exact single_le_sum (fun j' _ => pC_nonneg B u v j') (mem_univ j)

private lemma pD_le_one {n : ℕ} (B : Boxing n) (u v : 𝔽₂ B.r) (k : Fin B.m) : pD B u v k ≤ 1 := by
  rw [← sum_pD_eq_one B u v]
  exact single_le_sum (fun k' _ => pD_nonneg B u v k') (mem_univ k)

private def E_BC {n : ℕ} (A : Finset (𝔽₂ n × 𝔽₂ n)) : Finset (𝔽₂ n × 𝔽₂ n) := A

private def E_BD {n : ℕ} (A : Finset (𝔽₂ n × 𝔽₂ n)) : Finset (𝔽₂ n × 𝔽₂ n) :=
  univ.filter (fun p => (p.1, p.1 + p.2) ∈ A)

private def E_CD {n : ℕ} (A : Finset (𝔽₂ n × 𝔽₂ n)) : Finset (𝔽₂ n × 𝔽₂ n) :=
  univ.filter (fun p => (p.1 + p.2, p.1) ∈ A)

private noncomputable def energyE1 {n : ℕ} (B : Boxing n) : ℝ :=
  (∑ u : 𝔽₂ B.r, ∑ v : 𝔽₂ B.r,
    (∑ i : Fin B.m, pB B u v i ^ 2 +
      ∑ j : Fin B.m, pC B u v j ^ 2 +
      ∑ k : Fin B.m, pD B u v k ^ 2) / 3) / (4 ^ B.r : ℝ)

private noncomputable def energyE2 {n : ℕ} (A : Finset (𝔽₂ n × 𝔽₂ n)) (B : Boxing n) : ℝ :=
  (∑ u : 𝔽₂ B.r, ∑ v : 𝔽₂ B.r,
    (∑ i : Fin B.m, ∑ j : Fin B.m,
        pB B u v i * pC B u v j * densBip (E_BC A) (Bpart B u v i) (Cpart B u v j) ^ 2 +
      ∑ i : Fin B.m, ∑ k : Fin B.m,
        pB B u v i * pD B u v k * densBip (E_BD A) (Bpart B u v i) (Dpart B u v k) ^ 2 +
      ∑ j : Fin B.m, ∑ k : Fin B.m,
        pC B u v j * pD B u v k * densBip (E_CD A) (Cpart B u v j) (Dpart B u v k) ^ 2) / 3) /
    (4 ^ B.r : ℝ)

private lemma energyE1_nonneg {n : ℕ} (B : Boxing n) : 0 ≤ energyE1 B := by
  unfold energyE1
  refine div_nonneg (sum_nonneg fun u _ => sum_nonneg fun v _ => div_nonneg ?_ (by norm_num))
    (by positivity)
  exact add_nonneg (add_nonneg (sum_nonneg fun i _ => sq_nonneg _)
    (sum_nonneg fun j _ => sq_nonneg _)) (sum_nonneg fun k _ => sq_nonneg _)

private lemma energyE1_le_one {n : ℕ} (B : Boxing n) : energyE1 B ≤ 1 := by
  unfold energyE1
  have h4pos : (0 : ℝ) < (4 ^ B.r : ℝ) := by positivity
  rw [div_le_one h4pos]
  have hbox : ∀ u v : 𝔽₂ B.r,
      (∑ i : Fin B.m, pB B u v i ^ 2 +
        ∑ j : Fin B.m, pC B u v j ^ 2 +
        ∑ k : Fin B.m, pD B u v k ^ 2) / 3 ≤ 1 := by
    intro u v
    have h1 : ∑ i : Fin B.m, pB B u v i ^ 2 ≤ 1 := by
      calc ∑ i : Fin B.m, pB B u v i ^ 2
          ≤ ∑ i : Fin B.m, pB B u v i := by
              refine sum_le_sum fun i _ => ?_
              rw [sq]
              exact mul_le_of_le_one_right (pB_nonneg B u v i) (pB_le_one B u v i)
        _ = 1 := sum_pB_eq_one B u v
    have h2 : ∑ j : Fin B.m, pC B u v j ^ 2 ≤ 1 := by
      calc ∑ j : Fin B.m, pC B u v j ^ 2
          ≤ ∑ j : Fin B.m, pC B u v j := by
              refine sum_le_sum fun j _ => ?_
              rw [sq]
              exact mul_le_of_le_one_right (pC_nonneg B u v j) (pC_le_one B u v j)
        _ = 1 := sum_pC_eq_one B u v
    have h3 : ∑ k : Fin B.m, pD B u v k ^ 2 ≤ 1 := by
      calc ∑ k : Fin B.m, pD B u v k ^ 2
          ≤ ∑ k : Fin B.m, pD B u v k := by
              refine sum_le_sum fun k _ => ?_
              rw [sq]
              exact mul_le_of_le_one_right (pD_nonneg B u v k) (pD_le_one B u v k)
        _ = 1 := sum_pD_eq_one B u v
    linarith
  calc ∑ u : 𝔽₂ B.r, ∑ v : 𝔽₂ B.r, _
      ≤ ∑ _u : 𝔽₂ B.r, ∑ _v : 𝔽₂ B.r, (1 : ℝ) :=
        sum_le_sum fun u _ => sum_le_sum fun v _ => hbox u v
    _ = (4 ^ B.r : ℝ) := by
        simp only [sum_const, card_univ, nsmul_eq_mul, mul_one, f2_card, Nat.cast_pow, Nat.cast_ofNat]
        rw [← sq, four_pow_eq_real]

private lemma energyE2_nonneg {n : ℕ} (A : Finset (𝔽₂ n × 𝔽₂ n)) (B : Boxing n) :
    0 ≤ energyE2 A B := by
  unfold energyE2
  refine div_nonneg (sum_nonneg fun u _ => sum_nonneg fun v _ => div_nonneg ?_ (by norm_num))
    (by positivity)
  refine add_nonneg (add_nonneg ?_ ?_) ?_
  · exact sum_nonneg fun i _ => sum_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (pB_nonneg B u v i) (pC_nonneg B u v j)) (sq_nonneg _)
  · exact sum_nonneg fun i _ => sum_nonneg fun k _ =>
      mul_nonneg (mul_nonneg (pB_nonneg B u v i) (pD_nonneg B u v k)) (sq_nonneg _)
  · exact sum_nonneg fun j _ => sum_nonneg fun k _ =>
      mul_nonneg (mul_nonneg (pC_nonneg B u v j) (pD_nonneg B u v k)) (sq_nonneg _)

private lemma energyE2_le_one {n : ℕ} (A : Finset (𝔽₂ n × 𝔽₂ n)) (B : Boxing n) :
    energyE2 A B ≤ 1 := by
  unfold energyE2
  have h4pos : (0 : ℝ) < (4 ^ B.r : ℝ) := by positivity
  rw [div_le_one h4pos]
  have hbox : ∀ u v : 𝔽₂ B.r,
      (∑ i : Fin B.m, ∑ j : Fin B.m,
          pB B u v i * pC B u v j * densBip (E_BC A) (Bpart B u v i) (Cpart B u v j) ^ 2 +
        ∑ i : Fin B.m, ∑ k : Fin B.m,
          pB B u v i * pD B u v k * densBip (E_BD A) (Bpart B u v i) (Dpart B u v k) ^ 2 +
        ∑ j : Fin B.m, ∑ k : Fin B.m,
          pC B u v j * pD B u v k * densBip (E_CD A) (Cpart B u v j) (Dpart B u v k) ^ 2) / 3 ≤ 1 := by
    intro u v
    have h1 : ∑ i : Fin B.m, ∑ j : Fin B.m,
        pB B u v i * pC B u v j * densBip (E_BC A) (Bpart B u v i) (Cpart B u v j) ^ 2 ≤ 1 := by
      calc ∑ i : Fin B.m, ∑ j : Fin B.m,
            pB B u v i * pC B u v j * densBip (E_BC A) (Bpart B u v i) (Cpart B u v j) ^ 2
          ≤ ∑ i : Fin B.m, ∑ j : Fin B.m, pB B u v i * pC B u v j := by
              refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
              have hd0 := densBip_nonneg (E_BC A) (Bpart B u v i) (Cpart B u v j)
              have hd1 := densBip_le_one (E_BC A) (Bpart B u v i) (Cpart B u v j)
              have hsq : densBip (E_BC A) (Bpart B u v i) (Cpart B u v j) ^ 2 ≤ 1 := by nlinarith
              exact mul_le_of_le_one_right (mul_nonneg (pB_nonneg B u v i) (pC_nonneg B u v j)) hsq
        _ = (∑ i, pB B u v i) * (∑ j, pC B u v j) := by simp_rw [← mul_sum, ← sum_mul]
        _ = 1 := by rw [sum_pB_eq_one, sum_pC_eq_one, mul_one]
    have h2 : ∑ i : Fin B.m, ∑ k : Fin B.m,
        pB B u v i * pD B u v k * densBip (E_BD A) (Bpart B u v i) (Dpart B u v k) ^ 2 ≤ 1 := by
      calc ∑ i : Fin B.m, ∑ k : Fin B.m,
            pB B u v i * pD B u v k * densBip (E_BD A) (Bpart B u v i) (Dpart B u v k) ^ 2
          ≤ ∑ i : Fin B.m, ∑ k : Fin B.m, pB B u v i * pD B u v k := by
              refine sum_le_sum fun i _ => sum_le_sum fun k _ => ?_
              have hd0 := densBip_nonneg (E_BD A) (Bpart B u v i) (Dpart B u v k)
              have hd1 := densBip_le_one (E_BD A) (Bpart B u v i) (Dpart B u v k)
              have hsq : densBip (E_BD A) (Bpart B u v i) (Dpart B u v k) ^ 2 ≤ 1 := by nlinarith
              exact mul_le_of_le_one_right (mul_nonneg (pB_nonneg B u v i) (pD_nonneg B u v k)) hsq
        _ = (∑ i, pB B u v i) * (∑ k, pD B u v k) := by simp_rw [← mul_sum, ← sum_mul]
        _ = 1 := by rw [sum_pB_eq_one, sum_pD_eq_one, mul_one]
    have h3 : ∑ j : Fin B.m, ∑ k : Fin B.m,
        pC B u v j * pD B u v k * densBip (E_CD A) (Cpart B u v j) (Dpart B u v k) ^ 2 ≤ 1 := by
      calc ∑ j : Fin B.m, ∑ k : Fin B.m,
            pC B u v j * pD B u v k * densBip (E_CD A) (Cpart B u v j) (Dpart B u v k) ^ 2
          ≤ ∑ j : Fin B.m, ∑ k : Fin B.m, pC B u v j * pD B u v k := by
              refine sum_le_sum fun j _ => sum_le_sum fun k _ => ?_
              have hd0 := densBip_nonneg (E_CD A) (Cpart B u v j) (Dpart B u v k)
              have hd1 := densBip_le_one (E_CD A) (Cpart B u v j) (Dpart B u v k)
              have hsq : densBip (E_CD A) (Cpart B u v j) (Dpart B u v k) ^ 2 ≤ 1 := by nlinarith
              exact mul_le_of_le_one_right (mul_nonneg (pC_nonneg B u v j) (pD_nonneg B u v k)) hsq
        _ = (∑ j, pC B u v j) * (∑ k, pD B u v k) := by simp_rw [← mul_sum, ← sum_mul]
        _ = 1 := by rw [sum_pC_eq_one, sum_pD_eq_one, mul_one]
    linarith
  calc ∑ u : 𝔽₂ B.r, ∑ v : 𝔽₂ B.r, _
      ≤ ∑ _u : 𝔽₂ B.r, ∑ _v : 𝔽₂ B.r, (1 : ℝ) :=
        sum_le_sum fun u _ => sum_le_sum fun v _ => hbox u v
    _ = (4 ^ B.r : ℝ) := by
        simp only [sum_const, card_univ, nsmul_eq_mul, mul_one, f2_card, Nat.cast_pow, Nat.cast_ofNat]
        rw [← sq, four_pow_eq_real]

private noncomputable def shiftSet {n : ℕ} (W : Submodule (ZMod 2) (𝔽₂ n))
    (x₀ : 𝔽₂ n) (S : Finset (𝔽₂ n)) : Finset W :=
  open scoped Classical in
  univ.filter (fun w : W => (w : 𝔽₂ n) + x₀ ∈ S)

private lemma card_shiftSet {n r : ℕ} (proj : 𝔽₂ n →ₗ[ZMod 2] 𝔽₂ r) (u : 𝔽₂ r)
    {x₀ : 𝔽₂ n} (hx₀ : x₀ ∈ fiber proj u) {S : Finset (𝔽₂ n)} (hS : S ⊆ fiber proj u) :
    (shiftSet (LinearMap.ker proj) x₀ S).card = S.card := by
  classical
  refine Finset.card_bij (fun w _ => (w : 𝔽₂ n) + x₀) ?_ ?_ ?_
  · intro w hw
    simpa [shiftSet] using hw
  · intro w₁ _ w₂ _ h
    exact Subtype.ext (add_right_cancel h)
  · intro y hy
    have hyu : y ∈ fiber proj u := hS hy
    rw [mem_fiber] at hx₀ hyu
    have hker : y + x₀ ∈ LinearMap.ker proj := by
      rw [LinearMap.mem_ker, map_add, hyu, hx₀, f2_add_self]
    refine ⟨⟨y + x₀, hker⟩, ?_, ?_⟩
    · simp only [shiftSet, mem_filter, mem_univ, true_and]
      rw [add_assoc, f2_add_self, add_zero]
      exact hy
    · simp [add_assoc, f2_add_self]

private def IsFourierUniform {n r : ℕ} (proj : 𝔽₂ n →ₗ[ZMod 2] 𝔽₂ r) (u : 𝔽₂ r)
    (S : Finset (𝔽₂ n)) (η : ℝ) : Prop :=
  open scoped Classical in
  ∀ x₀ ∈ fiber proj u, ∀ ξ : (LinearMap.ker proj →ₗ[ZMod 2] ZMod 2),
    ξ ≠ 0 → |fourierCoeff (LinearMap.ker proj) (shiftSet (LinearMap.ker proj) x₀ S) ξ| ≤ η

private def OuterBoxReg1 {n : ℕ} (B : Boxing n) (ε : ℝ) (u v : 𝔽₂ B.r) : Prop :=
  (∀ i, IsFourierUniform B.proj u (Bpart B u v i) (ε / (B.m : ℝ) ^ 3)) ∧
  (∀ j, IsFourierUniform B.proj v (Cpart B u v j) (ε / (B.m : ℝ) ^ 3)) ∧
  (∀ k, IsFourierUniform B.proj (u + v) (Dpart B u v k) (ε / (B.m : ℝ) ^ 3))

private def Cond1 {n : ℕ} (B : Boxing n) (ε : ℝ) : Prop :=
  open scoped Classical in
  ((univ.filter (fun p : 𝔽₂ B.r × 𝔽₂ B.r => ¬ OuterBoxReg1 B ε p.1 p.2)).card : ℝ) ≤
    ε * (4 ^ B.r : ℝ)

private noncomputable def badWeightBC {n : ℕ} (A : Finset (𝔽₂ n × 𝔽₂ n)) (B : Boxing n)
    (ε : ℝ) (u v : 𝔽₂ B.r) : ℝ :=
  open scoped Classical in
  ∑ i : Fin B.m, ∑ j : Fin B.m,
    if IsQuasirandom (E_BC A) (Bpart B u v i) (Cpart B u v j) ε then 0 else pB B u v i * pC B u v j

private noncomputable def badWeightBD {n : ℕ} (A : Finset (𝔽₂ n × 𝔽₂ n)) (B : Boxing n)
    (ε : ℝ) (u v : 𝔽₂ B.r) : ℝ :=
  open scoped Classical in
  ∑ i : Fin B.m, ∑ k : Fin B.m,
    if IsQuasirandom (E_BD A) (Bpart B u v i) (Dpart B u v k) ε then 0 else pB B u v i * pD B u v k

private noncomputable def badWeightCD {n : ℕ} (A : Finset (𝔽₂ n × 𝔽₂ n)) (B : Boxing n)
    (ε : ℝ) (u v : 𝔽₂ B.r) : ℝ :=
  open scoped Classical in
  ∑ j : Fin B.m, ∑ k : Fin B.m,
    if IsQuasirandom (E_CD A) (Cpart B u v j) (Dpart B u v k) ε then 0 else pC B u v j * pD B u v k

private def OuterBoxReg2 {n : ℕ} (A : Finset (𝔽₂ n × 𝔽₂ n)) (B : Boxing n)
    (ε : ℝ) (u v : 𝔽₂ B.r) : Prop :=
  badWeightBC A B ε u v ≤ ε ∧ badWeightBD A B ε u v ≤ ε ∧ badWeightCD A B ε u v ≤ ε

private def Cond2 {n : ℕ} (A : Finset (𝔽₂ n × 𝔽₂ n)) (B : Boxing n) (ε : ℝ) : Prop :=
  open scoped Classical in
  ((univ.filter (fun p : 𝔽₂ B.r × 𝔽₂ B.r => ¬ OuterBoxReg2 A B ε p.1 p.2)).card : ℝ) ≤
    ε * (4 ^ B.r : ℝ)

private lemma e2_refine_sub_ge {n r r' : ℕ}
    (E : Finset (𝔽₂ n × 𝔽₂ n)) (X Y : Finset (𝔽₂ n))
    (sU sV : Finset (𝔽₂ r')) (fib : 𝔽₂ r' → Finset (𝔽₂ n))
    (hcovX : sU.biUnion (fun u' => X ∩ fib u') = X)
    (hdisX : (sU : Set (𝔽₂ r')).PairwiseDisjoint (fun u' => X ∩ fib u'))
    (hcovY : sV.biUnion (fun v' => Y ∩ fib v') = Y)
    (hdisY : (sV : Set (𝔽₂ r')).PairwiseDisjoint (fun v' => Y ∩ fib v'))
    (hpow : (2 ^ (n - r) : ℝ) = (2 ^ (r' - r) : ℝ) * (2 ^ (n - r') : ℝ)) :
    (2 ^ (r' - r) : ℝ) ^ 2 *
        (((X.card : ℝ) / (2 ^ (n - r) : ℝ)) * ((Y.card : ℝ) / (2 ^ (n - r) : ℝ)) *
          densBip E X Y ^ 2) ≤
      ∑ u' ∈ sU, ∑ v' ∈ sV,
        (((X ∩ fib u').card : ℝ) / (2 ^ (n - r') : ℝ)) *
          (((Y ∩ fib v').card : ℝ) / (2 ^ (n - r') : ℝ)) *
          densBip E (X ∩ fib u') (Y ∩ fib v') ^ 2 := by
  classical
  have hW_pos : (0 : ℝ) < (2 ^ (n - r) : ℝ) := by positivity
  have hW'_pos : (0 : ℝ) < (2 ^ (n - r') : ℝ) := by positivity
  let parts := fun p : 𝔽₂ r' × 𝔽₂ r' => (X ∩ fib p.1) ×ˢ (Y ∩ fib p.2)
  have hcov : (sU ×ˢ sV).biUnion parts = X ×ˢ Y := by
    rw [← hcovX, ← hcovY]
    ext ⟨x, y⟩
    simp only [parts, mem_biUnion, mem_product]
    constructor
    · rintro ⟨⟨u', v'⟩, ⟨hu', hv'⟩, hx, hy⟩
      exact ⟨⟨u', hu', hx⟩, ⟨v', hv', hy⟩⟩
    · rintro ⟨⟨u', hu', hx⟩, ⟨v', hv', hy⟩⟩
      exact ⟨(u', v'), ⟨hu', hv'⟩, hx, hy⟩
  have hdis : ((sU ×ˢ sV : Finset (𝔽₂ r' × 𝔽₂ r')) : Set (𝔽₂ r' × 𝔽₂ r')).PairwiseDisjoint parts := by
    intro p₁ hp₁ p₂ hp₂ hne
    refine Finset.disjoint_left.mpr ?_
    rintro ⟨x, y⟩ h₁ h₂
    simp only [parts, mem_product] at h₁ h₂
    simp only [mem_coe, mem_product] at hp₁ hp₂
    by_cases h1 : p₁.1 = p₂.1
    · have h2 : p₁.2 ≠ p₂.2 := fun he => hne (Prod.ext h1 he)
      exact Finset.disjoint_left.mp (hdisY hp₁.2 hp₂.2 h2) h₁.2 h₂.2
    · exact Finset.disjoint_left.mp (hdisX hp₁.1 hp₂.1 h1) h₁.1 h₂.1
  have hvar := sum_card_mul_setDens_sq_ge (sU ×ˢ sV) parts (X ×ˢ Y) E hcov hdis
  have hl : ((X ×ˢ Y).card : ℝ) * setDens E (X ×ˢ Y) ^ 2 =
      (2 ^ (n - r') : ℝ) ^ 2 * ((2 ^ (r' - r) : ℝ) ^ 2 *
        (((X.card : ℝ) / (2 ^ (n - r) : ℝ)) * ((Y.card : ℝ) / (2 ^ (n - r) : ℝ)) *
          densBip E X Y ^ 2)) := by
    rw [card_product, Nat.cast_mul, hpow]
    simp only [densBip]
    field_simp [hW'_pos.ne', hW_pos.ne']
  have hr : ∑ p ∈ sU ×ˢ sV, ((parts p).card : ℝ) * setDens E (parts p) ^ 2 =
      (2 ^ (n - r') : ℝ) ^ 2 *
        ∑ u' ∈ sU, ∑ v' ∈ sV,
          (((X ∩ fib u').card : ℝ) / (2 ^ (n - r') : ℝ)) *
            (((Y ∩ fib v').card : ℝ) / (2 ^ (n - r') : ℝ)) *
            densBip E (X ∩ fib u') (Y ∩ fib v') ^ 2 := by
    rw [sum_product, mul_sum]
    refine sum_congr rfl fun u' _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun v' _ => ?_
    simp only [parts, card_product, Nat.cast_mul, densBip]
    field_simp [hW'_pos.ne']
  rw [hl, hr] at hvar
  exact le_of_mul_le_mul_left hvar (sq_pos_of_pos hW'_pos)

private lemma e1_refine_part_ge {n r r' : ℕ}
    (S_box M : Finset (𝔽₂ n)) (sU : Finset (𝔽₂ r')) (fib : 𝔽₂ r' → Finset (𝔽₂ n))
    (hcov : sU.biUnion fib = S_box)
    (hdis : (sU : Set (𝔽₂ r')).PairwiseDisjoint fib)
    (hMS : M ⊆ S_box)
    (hcard_old : (S_box.card : ℝ) = (2 ^ (n - r) : ℝ))
    (hcard_new : ∀ u' ∈ sU, ((fib u').card : ℝ) = (2 ^ (n - r') : ℝ))
    (hpow : (2 ^ (n - r) : ℝ) = (2 ^ (r' - r) : ℝ) * (2 ^ (n - r') : ℝ)) :
    (2 ^ (r' - r) : ℝ) * ((M.card : ℝ) / (2 ^ (n - r) : ℝ)) ^ 2 ≤
      ∑ u' ∈ sU, (((M ∩ fib u').card : ℝ) / (2 ^ (n - r') : ℝ)) ^ 2 := by
  have hW'_pos : (0 : ℝ) < (2 ^ (n - r') : ℝ) := by positivity
  have hW_ne : (2 ^ (n - r) : ℝ) ≠ 0 := by positivity
  have hvar := sum_card_mul_setDens_sq_ge sU fib S_box M hcov hdis
  have hl : (S_box.card : ℝ) * setDens M S_box ^ 2 =
      (2 ^ (n - r') : ℝ) * ((2 ^ (r' - r) : ℝ) * ((M.card : ℝ) / (2 ^ (n - r) : ℝ)) ^ 2) := by
    have hdens : setDens M S_box = (M.card : ℝ) / (2 ^ (n - r) : ℝ) := by
      have hne : S_box.card ≠ 0 := by
        intro h
        exact hW_ne (by simpa [h] using hcard_old.symm)
      simp [setDens, hne, hcard_old, inter_eq_left.mpr hMS]
    rw [hdens, hcard_old, hpow]
    field_simp [hW_ne]
  have hr : ∑ u' ∈ sU, ((fib u').card : ℝ) * setDens M (fib u') ^ 2 =
      (2 ^ (n - r') : ℝ) * ∑ u' ∈ sU, (((M ∩ fib u').card : ℝ) / (2 ^ (n - r') : ℝ)) ^ 2 := by
    rw [mul_sum]
    refine sum_congr rfl fun u' hu' => ?_
    have hcu' := hcard_new u' hu'
    have hne : (fib u').card ≠ 0 := by
      intro h; have : ((fib u').card : ℝ) = 0 := by exact_mod_cast h
      linarith
    simp [setDens, hne, hcu']
  rw [hl, hr] at hvar
  exact le_of_mul_le_mul_left hvar hW'_pos

private lemma e1_refine_part_fourier_inc {n r r' : ℕ}
    (proj : 𝔽₂ n →ₗ[ZMod 2] 𝔽₂ r) (proj' : 𝔽₂ n →ₗ[ZMod 2] 𝔽₂ r')
    (hsurj : Function.Surjective proj) (hsurj' : Function.Surjective proj')
    (q : 𝔽₂ r' →ₗ[ZMod 2] 𝔽₂ r) (hq_comp : ∀ x, q (proj' x) = proj x)
    (u₀ : 𝔽₂ r) (M : Finset (𝔽₂ n)) (hM : M ⊆ fiber proj u₀)
    (x₀ : 𝔽₂ n) (hx₀ : x₀ ∈ fiber proj u₀)
    (ξ : LinearMap.ker proj →ₗ[ZMod 2] ZMod 2) (hξ0 : ξ ≠ 0)
    (extξ : 𝔽₂ n →ₗ[ZMod 2] ZMod 2) (hext : ∀ w : LinearMap.ker proj, extξ (w : 𝔽₂ n) = ξ w)
    (hvan : ∀ x ∈ LinearMap.ker proj', extξ x = 0)
    (hpow : (2 ^ (n - r) : ℝ) = (2 ^ (r' - r) : ℝ) * (2 ^ (n - r') : ℝ)) :
    (2 ^ (r' - r) : ℝ) * ((M.card : ℝ) / (2 ^ (n - r) : ℝ)) ^ 2 +
      (2 ^ (r' - r) : ℝ) *
        fourierCoeff (LinearMap.ker proj) (shiftSet (LinearMap.ker proj) x₀ M) ξ ^ 2 ≤
      ∑ u' ∈ fiber q u₀, (((M ∩ fiber proj' u').card : ℝ) / (2 ^ (n - r') : ℝ)) ^ 2 := by
  classical
  let W := LinearMap.ker proj
  have hW_pos : (0 : ℝ) < (2 ^ (n - r) : ℝ) := by positivity
  have hW'_pos : (0 : ℝ) < (2 ^ (n - r') : ℝ) := by positivity
  have hcov : (fiber q u₀).biUnion (fun u' => fiber proj' u') = fiber proj u₀ := by
    ext x
    simp only [mem_biUnion, mem_fiber]
    exact ⟨fun ⟨_, hqu, hpx⟩ => by rw [← hq_comp x, hpx, hqu],
           fun hx => ⟨proj' x, by rw [hq_comp x, hx], rfl⟩⟩
  have hdis : ((fiber q u₀ : Finset (𝔽₂ r')) : Set (𝔽₂ r')).PairwiseDisjoint (fun u' => fiber proj' u') := by
    intro u₁ _ u₂ _ hne
    refine Finset.disjoint_left.mpr fun x h₁ h₂ => ?_
    rw [mem_fiber] at h₁ h₂
    exact hne (h₁.symm.trans h₂)
  let σ : 𝔽₂ n → ℝ := fun y => if extξ (y + x₀) = 0 then 1 else -1
  have hσsq : ∀ y ∈ fiber proj u₀, σ y ^ 2 = 1 := fun y _ => by
    dsimp only [σ]; split_ifs <;> norm_num
  have hσsum : ∑ y ∈ fiber proj u₀, σ y = 0 := by
    have hx' := mem_fiber.mp hx₀
    have hbij : ∑ y ∈ fiber proj u₀, σ y = ∑ w : W, walshChar ξ w := by
      refine Finset.sum_bij (fun y hy => ⟨y + x₀, by
        rw [LinearMap.mem_ker, map_add, mem_fiber.mp hy, hx', f2_add_self]⟩) ?_ ?_ ?_ ?_
      · intro y _; exact mem_univ _
      · intro y₁ _ y₂ _ h
        exact add_right_cancel (congrArg Subtype.val h)
      · intro w _
        refine ⟨(w : 𝔽₂ n) + x₀, mem_fiber.mpr ?_, ?_⟩
        · have hw : proj (w : 𝔽₂ n) = 0 := LinearMap.mem_ker.mp w.2
          rw [map_add, hw, zero_add, hx']
        · ext i; simp [add_assoc, zmod2_add_self]
      · intro y hy
        have hmem : y + x₀ ∈ W := by
          rw [LinearMap.mem_ker, map_add, mem_fiber.mp hy, hx', f2_add_self]
        have he := hext ⟨y + x₀, hmem⟩
        simp only [σ, walshChar, he]
    rw [hbij, sum_walshChar_right ξ, if_neg hξ0]
  have hσconst : ∀ u' ∈ fiber q u₀, ∃ v : ℝ, ∀ y ∈ fiber proj' u', σ y = v := by
    intro u' _
    obtain ⟨y₀, hy₀⟩ := fiber_nonempty proj' hsurj' u'
    refine ⟨σ y₀, fun y hy => ?_⟩
    rw [mem_fiber] at hy₀ hy
    have hker : y + y₀ ∈ LinearMap.ker proj' := by
      rw [LinearMap.mem_ker, map_add, hy, hy₀, f2_add_self]
    have hv0 : extξ (y + y₀) = 0 := hvan (y + y₀) hker
    have heq : extξ (y + x₀) = extξ (y₀ + x₀) := by
      calc extξ (y + x₀)
          = extξ ((y + y₀) + (y₀ + x₀)) := by
              congr 1; rw [add_assoc, ← add_assoc y₀ y₀ x₀, f2_add_self, zero_add]
        _ = extξ (y + y₀) + extξ (y₀ + x₀) := map_add _ _ _
        _ = extξ (y₀ + x₀) := by rw [hv0, zero_add]
    simp only [σ, heq]
  have hvar := sum_card_mul_setDens_sq_ge_fourier (fiber q u₀) (fun u' => fiber proj' u')
    (fiber proj u₀) M hcov hdis hM σ hσsq hσsum hσconst
  have hM_sum : ∑ y ∈ M, σ y =
      (2 ^ (n - r) : ℝ) * fourierCoeff W (shiftSet W x₀ M) ξ := by
    have hx' := mem_fiber.mp hx₀
    have hbij : ∑ y ∈ M, σ y = ∑ w ∈ shiftSet W x₀ M, walshChar ξ w := by
      refine Finset.sum_bij (fun y hy => ⟨y + x₀, by
        rw [LinearMap.mem_ker, map_add, mem_fiber.mp (hM hy), hx', f2_add_self]⟩) ?_ ?_ ?_ ?_
      · intro y hy
        simp only [shiftSet, mem_filter, mem_univ, true_and]
        rw [add_assoc, f2_add_self, add_zero]
        exact hy
      · intro y₁ _ y₂ _ h
        exact add_right_cancel (congrArg Subtype.val h)
      · intro w hw
        simp only [shiftSet, mem_filter, mem_univ, true_and] at hw
        refine ⟨(w : 𝔽₂ n) + x₀, hw, ?_⟩
        ext i; simp [add_assoc, zmod2_add_self]
      · intro y hy
        have hmem : y + x₀ ∈ W := by
          rw [LinearMap.mem_ker, map_add, mem_fiber.mp (hM hy), hx', f2_add_self]
        have he := hext ⟨y + x₀, hmem⟩
        simp only [σ, walshChar, he]
    rw [hbij]
    have hcardW : (Fintype.card W : ℝ) = (2 ^ (n - r) : ℝ) := by
      dsimp only [W]
      exact_mod_cast card_ker_eq proj hsurj
    simp only [fourierCoeff, hcardW]
    field_simp [hW_pos.ne']
  rw [hM_sum] at hvar
  have hcard_old : ((fiber proj u₀).card : ℝ) = (2 ^ (n - r) : ℝ) := by
    exact_mod_cast fiber_card proj hsurj u₀
  have hdens_old : setDens M (fiber proj u₀) = (M.card : ℝ) / (2 ^ (n - r) : ℝ) := by
    have hne : (fiber proj u₀).card ≠ 0 := by
      rw [fiber_card proj hsurj u₀]; exact pow_ne_zero _ (by norm_num)
    simp [setDens, hne, hcard_old, inter_eq_left.mpr hM]
  have hrhs : ∑ u' ∈ fiber q u₀, ((fiber proj' u').card : ℝ) * setDens M (fiber proj' u') ^ 2 =
      (2 ^ (n - r') : ℝ) *
        ∑ u' ∈ fiber q u₀, (((M ∩ fiber proj' u').card : ℝ) / (2 ^ (n - r') : ℝ)) ^ 2 := by
    rw [mul_sum]
    refine sum_congr rfl fun u' _ => ?_
    have hcu' : ((fiber proj' u').card : ℝ) = (2 ^ (n - r') : ℝ) := by
      exact_mod_cast fiber_card proj' hsurj' u'
    have hne : (fiber proj' u').card ≠ 0 := by
      rw [fiber_card proj' hsurj' u']; exact pow_ne_zero _ (by norm_num)
    simp [setDens, hne, hcu']
  rw [hcard_old, hdens_old, hrhs] at hvar
  have hdiv := div_le_div_of_nonneg_right hvar hW_pos.le
  have hleft :
      ((2 ^ (n - r) : ℝ) * fourierCoeff W (shiftSet W x₀ M) ξ) ^ 2 / (2 ^ (n - r) : ℝ) =
        (2 ^ (n - r') : ℝ) * ((2 ^ (r' - r) : ℝ) *
          fourierCoeff W (shiftSet W x₀ M) ξ ^ 2) := by
    rw [hpow]; field_simp [hW'_pos.ne']
  have hright :
      (2 ^ (n - r) : ℝ) *
        ((2 ^ (n - r') : ℝ) *
            ∑ u' ∈ fiber q u₀, (((M ∩ fiber proj' u').card : ℝ) / (2 ^ (n - r') : ℝ)) ^ 2 -
          (2 ^ (n - r) : ℝ) * ((M.card : ℝ) / (2 ^ (n - r) : ℝ)) ^ 2) / (2 ^ (n - r) : ℝ) =
        (2 ^ (n - r') : ℝ) *
          (∑ u' ∈ fiber q u₀, (((M ∩ fiber proj' u').card : ℝ) / (2 ^ (n - r') : ℝ)) ^ 2 -
            (2 ^ (r' - r) : ℝ) * ((M.card : ℝ) / (2 ^ (n - r) : ℝ)) ^ 2) := by
    rw [hpow]; field_simp [hW'_pos.ne']
  rw [hleft, hright] at hdiv
  have h2 := le_of_mul_le_mul_left hdiv hW'_pos
  linarith

private lemma refinement_A {n : ℕ} (A : Finset (𝔽₂ n × 𝔽₂ n)) (B : Boxing n)
    {ε : ℝ} (hε : 0 < ε) (hfail : ¬ Cond1 B ε) :
    ∃ B' : Boxing n,
      B'.m = B.m ∧
      B'.r ≤ B.r + 4 ^ B.r ∧
      energyE2 A B ≤ energyE2 A B' ∧
      energyE1 B + ε ^ 3 / (3 * (B.m : ℝ) ^ 6) ≤ energyE1 B' := by
  classical
  let W := LinearMap.ker B.proj
  let bad1 : Finset (𝔽₂ B.r × 𝔽₂ B.r) :=
    univ.filter (fun p : 𝔽₂ B.r × 𝔽₂ B.r => ¬ OuterBoxReg1 B ε p.1 p.2)
  have hbad1_gt : ε * (4 ^ B.r : ℝ) < (bad1.card : ℝ) := by
    simpa [Cond1, bad1] using lt_of_not_ge hfail
  have hbad1_len : bad1.toList.length ≤ 4 ^ B.r := by
    rw [length_toList]
    have h1 : bad1.card ≤ Fintype.card (𝔽₂ B.r × 𝔽₂ B.r) := Finset.card_le_univ bad1
    have h2 : Fintype.card (𝔽₂ B.r × 𝔽₂ B.r) = 4 ^ B.r := by
      simp only [Fintype.card_prod, f2_card, ← sq, four_pow_eq]
    omega
  have hbad_wit : ∀ p : 𝔽₂ B.r × 𝔽₂ B.r, p ∈ bad1 →
      ∃ (ξ : W →ₗ[ZMod 2] ZMod 2), ξ ≠ 0 ∧
        ((∃ i x₀, x₀ ∈ fiber B.proj p.1 ∧
            ε / (B.m : ℝ) ^ 3 < |fourierCoeff W (shiftSet W x₀ (Bpart B p.1 p.2 i)) ξ|) ∨
         (∃ j y₀, y₀ ∈ fiber B.proj p.2 ∧
            ε / (B.m : ℝ) ^ 3 < |fourierCoeff W (shiftSet W y₀ (Cpart B p.1 p.2 j)) ξ|) ∨
         (∃ k z₀, z₀ ∈ fiber B.proj (p.1 + p.2) ∧
            ε / (B.m : ℝ) ^ 3 < |fourierCoeff W (shiftSet W z₀ (Dpart B p.1 p.2 k)) ξ|)) := by
    intro p hp
    have hnot : ¬ OuterBoxReg1 B ε p.1 p.2 := (mem_filter.mp hp).2
    simp only [OuterBoxReg1, IsFourierUniform, not_and_or, not_forall, not_le] at hnot
    rcases hnot with ⟨i, x₀, hx₀, ξ, hξ0, hlt⟩ | ⟨j, y₀, hy₀, ξ, hξ0, hlt⟩ |
        ⟨k, z₀, hz₀, ξ, hξ0, hlt⟩
    · exact ⟨ξ, hξ0, Or.inl ⟨i, x₀, hx₀, hlt⟩⟩
    · exact ⟨ξ, hξ0, Or.inr (Or.inl ⟨j, y₀, hy₀, hlt⟩)⟩
    · exact ⟨ξ, hξ0, Or.inr (Or.inr ⟨k, z₀, hz₀, hlt⟩)⟩
  obtain ⟨U, hWU⟩ := Submodule.exists_isCompl W
  let extW : (W →ₗ[ZMod 2] ZMod 2) → (𝔽₂ n →ₗ[ZMod 2] ZMod 2) :=
    fun ξ => ξ.comp (Submodule.projectionOnto W U hWU)
  have hextW : ∀ (ξ : W →ₗ[ZMod 2] ZMod 2) (w : W), extW ξ (w : 𝔽₂ n) = ξ w := by
    intro ξ w
    simp [extW, Submodule.projectionOnto_apply_left hWU w]
  let ξOf : 𝔽₂ B.r × 𝔽₂ B.r → (W →ₗ[ZMod 2] ZMod 2) := fun p =>
    if hp : p ∈ bad1 then Classical.choose (hbad_wit p hp) else 0
  let L : List (𝔽₂ n →ₗ[ZMod 2] ZMod 2) := bad1.toList.map (fun p => extW (ξOf p))
  obtain ⟨r', proj', hsurj', hr', hker', hvan⟩ := refineByList L B.r B.proj B.hsurj
  obtain ⟨q, hq_surj, hq_comp⟩ := factor_through_ker B.proj proj' B.hsurj hsurj' hker'
  let B' : Boxing n :=
    { r := r'
      proj := proj'
      hsurj := hsurj'
      m := B.m
      hm := B.hm
      bCol := fun u' v' x => B.bCol (q u') (q v') x
      cCol := fun u' v' y => B.cCol (q u') (q v') y
      dCol := fun u' v' z => B.dCol (q u') (q v') z }
  have hrr' : B.r ≤ r' := codim_le q hq_surj
  have hfib_sub_part : ∀ (u : 𝔽₂ B.r),
      (fiber q u).biUnion (fun u' => fiber proj' u') = fiber B.proj u := by
    intro u
    ext x
    simp only [mem_biUnion, mem_fiber]
    exact ⟨fun ⟨_, hqu, hpx⟩ => by rw [← hq_comp x, hpx, hqu],
           fun hx => ⟨proj' x, by rw [hq_comp x, hx], rfl⟩⟩
  have hfib_sub_disj : ∀ (u : 𝔽₂ B.r),
      ((fiber q u : Finset (𝔽₂ r')) : Set (𝔽₂ r')).PairwiseDisjoint (fun u' => fiber proj' u') := by
    intro u u₁ _ u₂ _ hne
    refine Finset.disjoint_left.mpr fun x h₁ h₂ => ?_
    rw [mem_fiber] at h₁ h₂
    exact hne (h₁.symm.trans h₂)
  have hX_cov : ∀ (u : 𝔽₂ B.r) (X : Finset (𝔽₂ n)), X ⊆ fiber B.proj u →
      (fiber q u).biUnion (fun u' => X ∩ fiber proj' u') = X := by
    intro u X hX
    rw [← inter_biUnion, hfib_sub_part u, inter_eq_left.mpr hX]
  have hX_dis : ∀ (u : 𝔽₂ B.r) (X : Finset (𝔽₂ n)),
      ((fiber q u : Finset (𝔽₂ r')) : Set (𝔽₂ r')).PairwiseDisjoint (fun u' => X ∩ fiber proj' u') := by
    intro u X u₁ hu₁ u₂ hu₂ hne
    exact (hfib_sub_disj u hu₁ hu₂ hne).mono inter_subset_right inter_subset_right
  have hBpart_eq : ∀ u' v' i,
      Bpart B' u' v' i = Bpart B (q u') (q v') i ∩ fiber proj' u' := by
    intro u' v' i
    ext x
    simp only [Bpart, mem_inter, mem_filter, mem_fiber, B']
    constructor
    · rintro ⟨hpx, hcol⟩
      exact ⟨⟨by rw [← hq_comp x, hpx], hcol⟩, hpx⟩
    · rintro ⟨⟨_, hcol⟩, hpx⟩
      exact ⟨hpx, hcol⟩
  have hCpart_eq : ∀ u' v' j,
      Cpart B' u' v' j = Cpart B (q u') (q v') j ∩ fiber proj' v' := by
    intro u' v' j
    ext y
    simp only [Cpart, mem_inter, mem_filter, mem_fiber, B']
    constructor
    · rintro ⟨hpy, hcol⟩
      exact ⟨⟨by rw [← hq_comp y, hpy], hcol⟩, hpy⟩
    · rintro ⟨⟨_, hcol⟩, hpy⟩
      exact ⟨hpy, hcol⟩
  have hDpart_eq : ∀ u' v' k,
      Dpart B' u' v' k = Dpart B (q u') (q v') k ∩ fiber proj' (u' + v') := by
    intro u' v' k
    ext z
    simp only [Dpart, mem_inter, mem_filter, mem_fiber, B']
    constructor
    · rintro ⟨hpz, hcol⟩
      exact ⟨⟨by rw [← hq_comp z, hpz, map_add], hcol⟩, hpz⟩
    · rintro ⟨⟨_, hcol⟩, hpz⟩
      exact ⟨hpz, hcol⟩
  have hsum_split : ∀ (f : 𝔽₂ r' → 𝔽₂ r' → ℝ),
      (∑ u' : 𝔽₂ r', ∑ v' : 𝔽₂ r', f u' v') =
        ∑ u : 𝔽₂ B.r, ∑ v : 𝔽₂ B.r, ∑ u' ∈ fiber q u, ∑ v' ∈ fiber q v, f u' v' := by
    intro f
    have hcov : (univ : Finset (𝔽₂ r')) = univ.biUnion (fun u : 𝔽₂ B.r => fiber q u) := by
      ext u'; simp [mem_fiber]
    have hdj : ((univ : Finset (𝔽₂ B.r)) : Set (𝔽₂ B.r)).PairwiseDisjoint (fun u => fiber q u) := by
      intro u₁ _ u₂ _ hne
      refine Finset.disjoint_left.mpr fun u' h₁ h₂ => ?_
      rw [mem_fiber] at h₁ h₂
      exact hne (h₁.symm.trans h₂)
    let S₁ : Finset (𝔽₂ r') → ℝ := fun s => ∑ u' ∈ s, ∑ v' : 𝔽₂ r', f u' v'
    let S₂ : 𝔽₂ r' → Finset (𝔽₂ r') → ℝ := fun u' s => ∑ v' ∈ s, f u' v'
    calc ∑ u' : 𝔽₂ r', ∑ v' : 𝔽₂ r', f u' v'
        = S₁ univ := rfl
      _ = S₁ ((univ : Finset (𝔽₂ B.r)).biUnion (fun u => fiber q u)) := by rw [hcov]
      _ = ∑ u : 𝔽₂ B.r, ∑ u' ∈ fiber q u, ∑ v' : 𝔽₂ r', f u' v' := sum_biUnion hdj
      _ = ∑ u : 𝔽₂ B.r, ∑ u' ∈ fiber q u, S₂ u' univ := rfl
      _ = ∑ u : 𝔽₂ B.r, ∑ u' ∈ fiber q u,
            S₂ u' ((univ : Finset (𝔽₂ B.r)).biUnion (fun v => fiber q v)) := by
          refine sum_congr rfl fun u _ => sum_congr rfl fun u' _ => ?_
          rw [hcov]
      _ = ∑ u : 𝔽₂ B.r, ∑ u' ∈ fiber q u, ∑ v : 𝔽₂ B.r, ∑ v' ∈ fiber q v, f u' v' := by
          refine sum_congr rfl fun u _ => sum_congr rfl fun u' _ => sum_biUnion hdj
      _ = ∑ u : 𝔽₂ B.r, ∑ v : 𝔽₂ B.r, ∑ u' ∈ fiber q u, ∑ v' ∈ fiber q v, f u' v' := by
          refine sum_congr rfl fun u _ => sum_comm
  have hq_card : ∀ u : 𝔽₂ B.r, ((fiber q u).card : ℝ) = (2 ^ (r' - B.r) : ℝ) := fun u => by
    exact_mod_cast fiber_card q hq_surj u
  have hpow_rel : (2 ^ (n - B.r) : ℝ) = (2 ^ (r' - B.r) : ℝ) * (2 ^ (n - r') : ℝ) := by
    have hrn : r' ≤ n := codim_le proj' hsurj'
    norm_cast
    rw [← pow_add]
    congr 1
    omega
  have hpow4_rel : (4 ^ r' : ℝ) = (4 ^ B.r : ℝ) * (2 ^ (r' - B.r) : ℝ) ^ 2 := by
    norm_cast
    rw [four_pow_eq, ← pow_add, Nat.add_sub_of_le hrr']
  have hsum_wsum_bij : ∀ (u v : 𝔽₂ B.r) (F : 𝔽₂ r' → ℝ),
      (∑ u' ∈ fiber q u, ∑ v' ∈ fiber q v, F (u' + v')) =
        (2 ^ (r' - B.r) : ℝ) * ∑ w' ∈ fiber q (u + v), F w' := by
    intro u v F
    have hinner : ∀ u' ∈ fiber q u,
        ∑ v' ∈ fiber q v, F (u' + v') = ∑ w' ∈ fiber q (u + v), F w' := by
      intro u' hu'
      rw [mem_fiber] at hu'
      refine Finset.sum_bij (fun v' _ => u' + v') ?_ ?_ ?_ ?_
      · intro v' hv'
        rw [mem_fiber] at hv' ⊢
        rw [map_add, hu', hv']
      · intro v₁ _ v₂ _ h; exact add_left_cancel h
      · intro w' hw'
        rw [mem_fiber] at hw'
        refine ⟨u' + w', mem_fiber.mpr ?_, ?_⟩
        · rw [map_add, hu', hw', ← add_assoc, f2_add_self, zero_add]
        · rw [← add_assoc, f2_add_self, zero_add]
      · intro v' _; rfl
    calc ∑ u' ∈ fiber q u, ∑ v' ∈ fiber q v, F (u' + v')
        = ∑ _u' ∈ fiber q u, ∑ w' ∈ fiber q (u + v), F w' := sum_congr rfl hinner
      _ = ((fiber q u).card : ℝ) * ∑ w' ∈ fiber q (u + v), F w' := by simp
      _ = (2 ^ (r' - B.r) : ℝ) * ∑ w' ∈ fiber q (u + v), F w' := by rw [hq_card u]
  have hE2_ge : energyE2 A B ≤ energyE2 A B' := by
    unfold energyE2
    rw [hsum_split, hpow4_rel]
    have hbox_E2 : ∀ u v : 𝔽₂ B.r,
        (2 ^ (r' - B.r) : ℝ) ^ 2 *
          ((∑ i : Fin B.m, ∑ j : Fin B.m,
              pB B u v i * pC B u v j * densBip (E_BC A) (Bpart B u v i) (Cpart B u v j) ^ 2 +
            ∑ i : Fin B.m, ∑ k : Fin B.m,
              pB B u v i * pD B u v k * densBip (E_BD A) (Bpart B u v i) (Dpart B u v k) ^ 2 +
            ∑ j : Fin B.m, ∑ k : Fin B.m,
              pC B u v j * pD B u v k * densBip (E_CD A) (Cpart B u v j) (Dpart B u v k) ^ 2) / 3) ≤
        ∑ u' ∈ fiber q u, ∑ v' ∈ fiber q v,
          (∑ i : Fin B.m, ∑ j : Fin B.m,
              pB B' u' v' i * pC B' u' v' j *
                densBip (E_BC A) (Bpart B' u' v' i) (Cpart B' u' v' j) ^ 2 +
            ∑ i : Fin B.m, ∑ k : Fin B.m,
              pB B' u' v' i * pD B' u' v' k *
                densBip (E_BD A) (Bpart B' u' v' i) (Dpart B' u' v' k) ^ 2 +
            ∑ j : Fin B.m, ∑ k : Fin B.m,
              pC B' u' v' j * pD B' u' v' k *
                densBip (E_CD A) (Cpart B' u' v' j) (Dpart B' u' v' k) ^ 2) / 3 := by
      intro u v
      have hBC : ∀ i j : Fin B.m,
          (2 ^ (r' - B.r) : ℝ) ^ 2 *
              (pB B u v i * pC B u v j * densBip (E_BC A) (Bpart B u v i) (Cpart B u v j) ^ 2) ≤
            ∑ u' ∈ fiber q u, ∑ v' ∈ fiber q v,
              pB B' u' v' i * pC B' u' v' j *
                densBip (E_BC A) (Bpart B' u' v' i) (Cpart B' u' v' j) ^ 2 := by
        intro i j
        have hsub := e2_refine_sub_ge (E_BC A) (Bpart B u v i) (Cpart B u v j)
          (fiber q u) (fiber q v) (fiber proj')
          (hX_cov u _ (filter_subset _ _)) (hX_dis u _)
          (hX_cov v _ (filter_subset _ _)) (hX_dis v _) hpow_rel
        refine hsub.trans_eq (sum_congr rfl fun u' hu' => sum_congr rfl fun v' hv' => ?_)
        rw [mem_fiber] at hu' hv'
        simp only [pB, pC, B', hBpart_eq u' v' i, hCpart_eq u' v' j, hu', hv']
      have hBD : ∀ i k : Fin B.m,
          (2 ^ (r' - B.r) : ℝ) ^ 2 *
              (pB B u v i * pD B u v k * densBip (E_BD A) (Bpart B u v i) (Dpart B u v k) ^ 2) ≤
            ∑ u' ∈ fiber q u, ∑ v' ∈ fiber q v,
              pB B' u' v' i * pD B' u' v' k *
                densBip (E_BD A) (Bpart B' u' v' i) (Dpart B' u' v' k) ^ 2 := by
        intro i k
        have hsub := e2_refine_sub_ge (E_BD A) (Bpart B u v i) (Dpart B u v k)
          (fiber q u) (fiber q (u + v)) (fiber proj')
          (hX_cov u _ (filter_subset _ _)) (hX_dis u _)
          (hX_cov (u + v) _ (filter_subset _ _)) (hX_dis (u + v) _) hpow_rel
        refine hsub.trans_eq (sum_congr rfl fun u' hu' => ?_)
        rw [mem_fiber] at hu'
        symm
        refine Finset.sum_bij (fun v' _ => u' + v') ?_ ?_ ?_ ?_
        · intro v' hv'; rw [mem_fiber] at hv' ⊢; rw [map_add, hu', hv']
        · intro v₁ _ v₂ _ h; exact add_left_cancel h
        · intro w' hw'; rw [mem_fiber] at hw'
          exact ⟨u' + w', mem_fiber.mpr (by rw [map_add, hu', hw', ← add_assoc, f2_add_self, zero_add]),
            by rw [← add_assoc, f2_add_self, zero_add]⟩
        · intro v' hv'; rw [mem_fiber] at hv'
          simp only [pB, pD, B', hBpart_eq u' v' i, hDpart_eq u' v' k, hu', hv']
      have hCD : ∀ j k : Fin B.m,
          (2 ^ (r' - B.r) : ℝ) ^ 2 *
              (pC B u v j * pD B u v k * densBip (E_CD A) (Cpart B u v j) (Dpart B u v k) ^ 2) ≤
            ∑ u' ∈ fiber q u, ∑ v' ∈ fiber q v,
              pC B' u' v' j * pD B' u' v' k *
                densBip (E_CD A) (Cpart B' u' v' j) (Dpart B' u' v' k) ^ 2 := by
        intro j k
        have hsub := e2_refine_sub_ge (E_CD A) (Cpart B u v j) (Dpart B u v k)
          (fiber q v) (fiber q (u + v)) (fiber proj')
          (hX_cov v _ (filter_subset _ _)) (hX_dis v _)
          (hX_cov (u + v) _ (filter_subset _ _)) (hX_dis (u + v) _) hpow_rel
        refine hsub.trans_eq ?_
        symm
        rw [sum_comm]
        refine sum_congr rfl fun v' hv' => ?_
        rw [mem_fiber] at hv'
        refine Finset.sum_bij (fun u' _ => u' + v') ?_ ?_ ?_ ?_
        · intro u' hu'; rw [mem_fiber] at hu' ⊢; rw [map_add, hu', hv']
        · intro u₁ _ u₂ _ h; exact add_right_cancel h
        · intro w' hw'; rw [mem_fiber] at hw'
          exact ⟨w' + v', mem_fiber.mpr (by rw [map_add, hw', hv', add_assoc, f2_add_self, add_zero]),
            by rw [add_assoc, f2_add_self, add_zero]⟩
        · intro u' hu'; rw [mem_fiber] at hu'
          simp only [pC, pD, B', hCpart_eq u' v' j, hDpart_eq u' v' k, hu', hv']
      have hsumBC := sum_le_sum fun i (_ : i ∈ (univ : Finset (Fin B.m))) =>
        sum_le_sum fun j (_ : j ∈ (univ : Finset (Fin B.m))) => hBC i j
      have hsumBD := sum_le_sum fun i (_ : i ∈ (univ : Finset (Fin B.m))) =>
        sum_le_sum fun k (_ : k ∈ (univ : Finset (Fin B.m))) => hBD i k
      have hsumCD := sum_le_sum fun j (_ : j ∈ (univ : Finset (Fin B.m))) =>
        sum_le_sum fun k (_ : k ∈ (univ : Finset (Fin B.m))) => hCD j k
      simp only [← mul_sum] at hsumBC hsumBD hsumCD
      have hsw1 : (∑ u' ∈ fiber q u, ∑ v' ∈ fiber q v,
            ∑ i, ∑ j, pB B' u' v' i * pC B' u' v' j *
              densBip (E_BC A) (Bpart B' u' v' i) (Cpart B' u' v' j) ^ 2) =
          ∑ i, ∑ j, ∑ u' ∈ fiber q u, ∑ v' ∈ fiber q v,
            pB B' u' v' i * pC B' u' v' j *
              densBip (E_BC A) (Bpart B' u' v' i) (Cpart B' u' v' j) ^ 2 := by
        calc _ = ∑ u' ∈ fiber q u, ∑ i, ∑ v' ∈ fiber q v, ∑ j, _ :=
                sum_congr rfl fun u' _ => sum_comm
          _ = ∑ i, ∑ u' ∈ fiber q u, ∑ j, ∑ v' ∈ fiber q v, _ := by
                rw [sum_comm]; exact sum_congr rfl fun i _ => sum_congr rfl fun u' _ => sum_comm
          _ = _ := sum_congr rfl fun i _ => sum_comm
      have hsw2 : (∑ u' ∈ fiber q u, ∑ v' ∈ fiber q v,
            ∑ i, ∑ k, pB B' u' v' i * pD B' u' v' k *
              densBip (E_BD A) (Bpart B' u' v' i) (Dpart B' u' v' k) ^ 2) =
          ∑ i, ∑ k, ∑ u' ∈ fiber q u, ∑ v' ∈ fiber q v,
            pB B' u' v' i * pD B' u' v' k *
              densBip (E_BD A) (Bpart B' u' v' i) (Dpart B' u' v' k) ^ 2 := by
        calc _ = ∑ u' ∈ fiber q u, ∑ i, ∑ v' ∈ fiber q v, ∑ k, _ :=
                sum_congr rfl fun u' _ => sum_comm
          _ = ∑ i, ∑ u' ∈ fiber q u, ∑ k, ∑ v' ∈ fiber q v, _ := by
                rw [sum_comm]; exact sum_congr rfl fun i _ => sum_congr rfl fun u' _ => sum_comm
          _ = _ := sum_congr rfl fun i _ => sum_comm
      have hsw3 : (∑ u' ∈ fiber q u, ∑ v' ∈ fiber q v,
            ∑ j, ∑ k, pC B' u' v' j * pD B' u' v' k *
              densBip (E_CD A) (Cpart B' u' v' j) (Dpart B' u' v' k) ^ 2) =
          ∑ j, ∑ k, ∑ u' ∈ fiber q u, ∑ v' ∈ fiber q v,
            pC B' u' v' j * pD B' u' v' k *
              densBip (E_CD A) (Cpart B' u' v' j) (Dpart B' u' v' k) ^ 2 := by
        calc _ = ∑ u' ∈ fiber q u, ∑ j, ∑ v' ∈ fiber q v, ∑ k, _ :=
                sum_congr rfl fun u' _ => sum_comm
          _ = ∑ j, ∑ u' ∈ fiber q u, ∑ k, ∑ v' ∈ fiber q v, _ := by
                rw [sum_comm]; exact sum_congr rfl fun j _ => sum_congr rfl fun u' _ => sum_comm
          _ = _ := sum_congr rfl fun j _ => sum_comm
      simp only [sum_add_distrib, ← sum_div]
      rw [hsw1, hsw2, hsw3]
      linarith
    have h4pos : (0 : ℝ) < (4 ^ B.r : ℝ) := by positivity
    have h2pos : (0 : ℝ) < (2 ^ (r' - B.r) : ℝ) ^ 2 := by positivity
    rw [div_le_div_iff₀ h4pos (mul_pos h4pos h2pos)]
    conv_lhs =>
      rw [show ∀ s : ℝ, s * ((4 ^ B.r : ℝ) * (2 ^ (r' - B.r) : ℝ) ^ 2) =
          ((2 ^ (r' - B.r) : ℝ) ^ 2 * s) * (4 ^ B.r : ℝ) from fun s => by ring]
    refine mul_le_mul_of_nonneg_right ?_ h4pos.le
    rw [mul_sum]
    refine sum_le_sum fun u _ => ?_
    rw [mul_sum]
    exact sum_le_sum fun v _ => hbox_E2 u v
  have hE1_inc : energyE1 B + ε ^ 3 / (3 * (B.m : ℝ) ^ 6) ≤ energyE1 B' := by
    have hcard_old : ∀ u : 𝔽₂ B.r, ((fiber B.proj u).card : ℝ) = (2 ^ (n - B.r) : ℝ) :=
      fun u => by exact_mod_cast fiber_card B.proj B.hsurj u
    have hcard_new : ∀ u' : 𝔽₂ r', ((fiber proj' u').card : ℝ) = (2 ^ (n - r') : ℝ) :=
      fun u' => by exact_mod_cast fiber_card proj' hsurj' u'
    have hbox_E1 : ∀ u v : 𝔽₂ B.r,
        (2 ^ (r' - B.r) : ℝ) ^ 2 *
          ((∑ i : Fin B.m, pB B u v i ^ 2 +
            ∑ j : Fin B.m, pC B u v j ^ 2 +
            ∑ k : Fin B.m, pD B u v k ^ 2) / 3 +
            if (u, v) ∈ bad1 then (ε / (B.m : ℝ) ^ 3) ^ 2 / 3 else 0) ≤
        ∑ u' ∈ fiber q u, ∑ v' ∈ fiber q v,
          (∑ i : Fin B.m, pB B' u' v' i ^ 2 +
            ∑ j : Fin B.m, pC B' u' v' j ^ 2 +
            ∑ k : Fin B.m, pD B' u' v' k ^ 2) / 3 := by
      intro u v
      have hB_eq : ∀ i,
          ∑ u' ∈ fiber q u, ∑ v' ∈ fiber q v, pB B' u' v' i ^ 2 =
            (2 ^ (r' - B.r) : ℝ) *
              ∑ u' ∈ fiber q u, (((Bpart B u v i ∩ fiber proj' u').card : ℝ) /
                (2 ^ (n - r') : ℝ)) ^ 2 := by
        intro i
        rw [mul_sum]
        refine sum_congr rfl fun u' hu' => ?_
        rw [mem_fiber] at hu'
        calc ∑ v' ∈ fiber q v, pB B' u' v' i ^ 2
            = ∑ _v' ∈ fiber q v,
                (((Bpart B u v i ∩ fiber proj' u').card : ℝ) / (2 ^ (n - r') : ℝ)) ^ 2 :=
                sum_congr rfl fun v' hv' => by
                  rw [mem_fiber] at hv'
                  have hb := hBpart_eq u' v' i
                  rw [hu', hv'] at hb
                  simp only [pB]
                  show (((Bpart B' u' v' i).card : ℝ) / (2 ^ (n - r') : ℝ)) ^ 2 = _
                  rw [hb]
          _ = (2 ^ (r' - B.r) : ℝ) *
                (((Bpart B u v i ∩ fiber proj' u').card : ℝ) / (2 ^ (n - r') : ℝ)) ^ 2 := by
                simp [hq_card v]
      have hC_eq : ∀ j,
          ∑ u' ∈ fiber q u, ∑ v' ∈ fiber q v, pC B' u' v' j ^ 2 =
            (2 ^ (r' - B.r) : ℝ) *
              ∑ v' ∈ fiber q v, (((Cpart B u v j ∩ fiber proj' v').card : ℝ) /
                (2 ^ (n - r') : ℝ)) ^ 2 := by
        intro j
        rw [sum_comm, mul_sum]
        refine sum_congr rfl fun v' hv' => ?_
        rw [mem_fiber] at hv'
        calc ∑ u' ∈ fiber q u, pC B' u' v' j ^ 2
            = ∑ _u' ∈ fiber q u,
                (((Cpart B u v j ∩ fiber proj' v').card : ℝ) / (2 ^ (n - r') : ℝ)) ^ 2 :=
                sum_congr rfl fun u' hu' => by
                  rw [mem_fiber] at hu'
                  have hc := hCpart_eq u' v' j
                  rw [hu', hv'] at hc
                  simp only [pC]
                  show (((Cpart B' u' v' j).card : ℝ) / (2 ^ (n - r') : ℝ)) ^ 2 = _
                  rw [hc]
          _ = (2 ^ (r' - B.r) : ℝ) *
                (((Cpart B u v j ∩ fiber proj' v').card : ℝ) / (2 ^ (n - r') : ℝ)) ^ 2 := by
                simp [hq_card u]
      have hD_eq : ∀ k,
          ∑ u' ∈ fiber q u, ∑ v' ∈ fiber q v, pD B' u' v' k ^ 2 =
            (2 ^ (r' - B.r) : ℝ) *
              ∑ w' ∈ fiber q (u + v), (((Dpart B u v k ∩ fiber proj' w').card : ℝ) /
                (2 ^ (n - r') : ℝ)) ^ 2 := by
        intro k
        calc ∑ u' ∈ fiber q u, ∑ v' ∈ fiber q v, pD B' u' v' k ^ 2
            = ∑ u' ∈ fiber q u, ∑ v' ∈ fiber q v,
                (((Dpart B u v k ∩ fiber proj' (u' + v')).card : ℝ) / (2 ^ (n - r') : ℝ)) ^ 2 :=
                sum_congr rfl fun u' hu' => sum_congr rfl fun v' hv' => by
                  rw [mem_fiber] at hu' hv'
                  have hd := hDpart_eq u' v' k
                  rw [hu', hv'] at hd
                  simp only [pD]
                  show (((Dpart B' u' v' k).card : ℝ) / (2 ^ (n - r') : ℝ)) ^ 2 = _
                  rw [hd]
          _ = _ := hsum_wsum_bij u v
                (fun w' => (((Dpart B u v k ∩ fiber proj' w').card : ℝ) / (2 ^ (n - r') : ℝ)) ^ 2)
      have hB_ge : ∀ i, (2 ^ (r' - B.r) : ℝ) ^ 2 * pB B u v i ^ 2 ≤
          ∑ u' ∈ fiber q u, ∑ v' ∈ fiber q v, pB B' u' v' i ^ 2 := fun i => by
        rw [hB_eq i, sq, mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (e1_refine_part_ge (fiber B.proj u) (Bpart B u v i) (fiber q u) (fiber proj')
            (hfib_sub_part u) (hfib_sub_disj u) (filter_subset _ _) (hcard_old u)
            (fun u' _ => hcard_new u') hpow_rel) (by positivity)
      have hC_ge : ∀ j, (2 ^ (r' - B.r) : ℝ) ^ 2 * pC B u v j ^ 2 ≤
          ∑ u' ∈ fiber q u, ∑ v' ∈ fiber q v, pC B' u' v' j ^ 2 := fun j => by
        rw [hC_eq j, sq, mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (e1_refine_part_ge (fiber B.proj v) (Cpart B u v j) (fiber q v) (fiber proj')
            (hfib_sub_part v) (hfib_sub_disj v) (filter_subset _ _) (hcard_old v)
            (fun v' _ => hcard_new v') hpow_rel) (by positivity)
      have hD_ge : ∀ k, (2 ^ (r' - B.r) : ℝ) ^ 2 * pD B u v k ^ 2 ≤
          ∑ u' ∈ fiber q u, ∑ v' ∈ fiber q v, pD B' u' v' k ^ 2 := fun k => by
        rw [hD_eq k, sq, mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (e1_refine_part_ge (fiber B.proj (u + v)) (Dpart B u v k) (fiber q (u + v)) (fiber proj')
            (hfib_sub_part (u + v)) (hfib_sub_disj (u + v)) (filter_subset _ _)
            (hcard_old (u + v)) (fun w' _ => hcard_new w') hpow_rel) (by positivity)
      have hswB : (∑ u' ∈ fiber q u, ∑ v' ∈ fiber q v, ∑ i, pB B' u' v' i ^ 2) =
          ∑ i, ∑ u' ∈ fiber q u, ∑ v' ∈ fiber q v, pB B' u' v' i ^ 2 := by
        calc _ = ∑ u' ∈ fiber q u, ∑ i, ∑ v' ∈ fiber q v, pB B' u' v' i ^ 2 :=
              sum_congr rfl fun u' _ => sum_comm
          _ = _ := sum_comm
      have hswC : (∑ u' ∈ fiber q u, ∑ v' ∈ fiber q v, ∑ j, pC B' u' v' j ^ 2) =
          ∑ j, ∑ u' ∈ fiber q u, ∑ v' ∈ fiber q v, pC B' u' v' j ^ 2 := by
        calc _ = ∑ u' ∈ fiber q u, ∑ j, ∑ v' ∈ fiber q v, pC B' u' v' j ^ 2 :=
              sum_congr rfl fun u' _ => sum_comm
          _ = _ := sum_comm
      have hswD : (∑ u' ∈ fiber q u, ∑ v' ∈ fiber q v, ∑ k, pD B' u' v' k ^ 2) =
          ∑ k, ∑ u' ∈ fiber q u, ∑ v' ∈ fiber q v, pD B' u' v' k ^ 2 := by
        calc _ = ∑ u' ∈ fiber q u, ∑ k, ∑ v' ∈ fiber q v, pD B' u' v' k ^ 2 :=
              sum_congr rfl fun u' _ => sum_comm
          _ = _ := sum_comm
      by_cases hbad : (u, v) ∈ bad1
      · simp only [hbad, ↓reduceIte]
        have hspec := Classical.choose_spec (hbad_wit (u, v) hbad)
        set ξ := Classical.choose (hbad_wit (u, v) hbad)
        have hξ_def : ξ = ξOf (u, v) := by simp [ξOf, hbad, ξ]
        have hvanξ : ∀ x ∈ LinearMap.ker proj', extW ξ x = 0 := by
          intro x hx
          have hmemL : extW ξ ∈ L := by
            rw [hξ_def]
            exact List.mem_map.mpr ⟨(u, v), mem_toList.mpr hbad, rfl⟩
          exact hvan (extW ξ) hmemL x hx
        rcases hspec with ⟨hξ0, hcases⟩
        have hsumB0 := sum_le_sum fun i (_ : i ∈ univ) => hB_ge i
        have hsumC0 := sum_le_sum fun j (_ : j ∈ univ) => hC_ge j
        have hsumD0 := sum_le_sum fun k (_ : k ∈ univ) => hD_ge k
        simp_rw [← mul_sum] at hsumB0 hsumC0 hsumD0
        rw [← hswB] at hsumB0
        rw [← hswC] at hsumC0
        rw [← hswD] at hsumD0
        simp only [sum_add_distrib, ← sum_div]
        rcases hcases with ⟨i₀, x₀, hx₀, hlt⟩ | ⟨j₀, y₀, hy₀, hlt⟩ | ⟨k₀, z₀, hz₀, hlt⟩
        · have hinc := e1_refine_part_fourier_inc B.proj proj' B.hsurj hsurj' q hq_comp u
            (Bpart B u v i₀) (filter_subset _ _) x₀ hx₀ ξ hξ0 (extW ξ) (hextW ξ) hvanξ hpow_rel
          have hlt_sq : (ε / (B.m : ℝ) ^ 3) ^ 2 ≤
              fourierCoeff W (shiftSet W x₀ (Bpart B u v i₀)) ξ ^ 2 := by
            calc (ε / (B.m : ℝ) ^ 3) ^ 2
                ≤ |fourierCoeff W (shiftSet W x₀ (Bpart B u v i₀)) ξ| ^ 2 :=
                  pow_le_pow_left₀ (by positivity) hlt.le 2
              _ = _ := sq_abs _
          have hB₀ : (2 ^ (r' - B.r) : ℝ) ^ 2 *
              (pB B u v i₀ ^ 2 + (ε / (B.m : ℝ) ^ 3) ^ 2) ≤
              ∑ u' ∈ fiber q u, ∑ v' ∈ fiber q v, pB B' u' v' i₀ ^ 2 := by
            rw [hB_eq i₀]
            have hmul : (2 ^ (r' - B.r) : ℝ) * (ε / (B.m : ℝ) ^ 3) ^ 2 ≤
                (2 ^ (r' - B.r) : ℝ) *
                  fourierCoeff B.proj.ker (shiftSet B.proj.ker x₀ (Bpart B u v i₀)) ξ ^ 2 :=
              mul_le_mul_of_nonneg_left hlt_sq (by positivity)
            have h1 : (2 ^ (r' - B.r) : ℝ) * (pB B u v i₀ ^ 2 + (ε / (B.m : ℝ) ^ 3) ^ 2) ≤
                ∑ u' ∈ fiber q u, (((Bpart B u v i₀ ∩ fiber proj' u').card : ℝ) /
                  (2 ^ (n - r') : ℝ)) ^ 2 := by
              calc (2 ^ (r' - B.r) : ℝ) * (pB B u v i₀ ^ 2 + (ε / (B.m : ℝ) ^ 3) ^ 2)
                  = (2 ^ (r' - B.r) : ℝ) * (((Bpart B u v i₀).card : ℝ) / (2 ^ (n - B.r) : ℝ)) ^ 2 +
                      (2 ^ (r' - B.r) : ℝ) * (ε / (B.m : ℝ) ^ 3) ^ 2 := by
                        simp only [pB]; ring
                _ ≤ (2 ^ (r' - B.r) : ℝ) * (((Bpart B u v i₀).card : ℝ) / (2 ^ (n - B.r) : ℝ)) ^ 2 +
                      (2 ^ (r' - B.r) : ℝ) *
                        fourierCoeff B.proj.ker (shiftSet B.proj.ker x₀ (Bpart B u v i₀)) ξ ^ 2 :=
                        add_le_add_right hmul _
                _ ≤ _ := hinc
            calc (2 ^ (r' - B.r) : ℝ) ^ 2 * (pB B u v i₀ ^ 2 + (ε / (B.m : ℝ) ^ 3) ^ 2)
                = (2 ^ (r' - B.r) : ℝ) *
                    ((2 ^ (r' - B.r) : ℝ) * (pB B u v i₀ ^ 2 + (ε / (B.m : ℝ) ^ 3) ^ 2)) := by ring
              _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)
          have hrest := sum_le_sum fun i (_ : i ∈ (univ : Finset (Fin B.m)).erase i₀) => hB_ge i
          rw [← mul_sum] at hrest
          have hsumB : (2 ^ (r' - B.r) : ℝ) ^ 2 *
              ((∑ i, pB B u v i ^ 2) + (ε / (B.m : ℝ) ^ 3) ^ 2) ≤
              ∑ u' ∈ fiber q u, ∑ v' ∈ fiber q v, ∑ i, pB B' u' v' i ^ 2 := by
            rw [← add_sum_erase (univ : Finset (Fin B.m)) (fun i => pB B u v i ^ 2) (mem_univ i₀)]
            rw [hswB, ← add_sum_erase (univ : Finset (Fin B.m))
              (fun i => ∑ u' ∈ fiber q u, ∑ v' ∈ fiber q v, pB B' u' v' i ^ 2) (mem_univ i₀)]
            calc (2 ^ (r' - B.r) : ℝ) ^ 2 *
                  ((pB B u v i₀ ^ 2 + ∑ i ∈ (univ : Finset (Fin B.m)).erase i₀, pB B u v i ^ 2) +
                    (ε / (B.m : ℝ) ^ 3) ^ 2)
                = (2 ^ (r' - B.r) : ℝ) ^ 2 * (pB B u v i₀ ^ 2 + (ε / (B.m : ℝ) ^ 3) ^ 2) +
                    (2 ^ (r' - B.r) : ℝ) ^ 2 *
                      ∑ i ∈ (univ : Finset (Fin B.m)).erase i₀, pB B u v i ^ 2 := by ring
              _ ≤ _ := add_le_add hB₀ hrest
          have htot := add_le_add (add_le_add hsumB hsumC0) hsumD0
          have hdiv := div_le_div_of_nonneg_right htot (by norm_num : (0 : ℝ) ≤ 3)
          calc (2 ^ (r' - B.r) : ℝ) ^ 2 *
                ((∑ i, pB B u v i ^ 2 + ∑ j, pC B u v j ^ 2 + ∑ k, pD B u v k ^ 2) / 3 +
                  (ε / (B.m : ℝ) ^ 3) ^ 2 / 3)
              = ((2 ^ (r' - B.r) : ℝ) ^ 2 * ((∑ i, pB B u v i ^ 2) + (ε / (B.m : ℝ) ^ 3) ^ 2) +
                  (2 ^ (r' - B.r) : ℝ) ^ 2 * ∑ j, pC B u v j ^ 2 +
                  (2 ^ (r' - B.r) : ℝ) ^ 2 * ∑ k, pD B u v k ^ 2) / 3 := by ring
            _ ≤ _ := hdiv
        · have hinc := e1_refine_part_fourier_inc B.proj proj' B.hsurj hsurj' q hq_comp v
            (Cpart B u v j₀) (filter_subset _ _) y₀ hy₀ ξ hξ0 (extW ξ) (hextW ξ) hvanξ hpow_rel
          have hlt_sq : (ε / (B.m : ℝ) ^ 3) ^ 2 ≤
              fourierCoeff W (shiftSet W y₀ (Cpart B u v j₀)) ξ ^ 2 := by
            calc (ε / (B.m : ℝ) ^ 3) ^ 2
                ≤ |fourierCoeff W (shiftSet W y₀ (Cpart B u v j₀)) ξ| ^ 2 :=
                  pow_le_pow_left₀ (by positivity) hlt.le 2
              _ = _ := sq_abs _
          have hC₀ : (2 ^ (r' - B.r) : ℝ) ^ 2 *
              (pC B u v j₀ ^ 2 + (ε / (B.m : ℝ) ^ 3) ^ 2) ≤
              ∑ u' ∈ fiber q u, ∑ v' ∈ fiber q v, pC B' u' v' j₀ ^ 2 := by
            rw [hC_eq j₀]
            have hmul : (2 ^ (r' - B.r) : ℝ) * (ε / (B.m : ℝ) ^ 3) ^ 2 ≤
                (2 ^ (r' - B.r) : ℝ) *
                  fourierCoeff B.proj.ker (shiftSet B.proj.ker y₀ (Cpart B u v j₀)) ξ ^ 2 :=
              mul_le_mul_of_nonneg_left hlt_sq (by positivity)
            have h1 : (2 ^ (r' - B.r) : ℝ) * (pC B u v j₀ ^ 2 + (ε / (B.m : ℝ) ^ 3) ^ 2) ≤
                ∑ v' ∈ fiber q v, (((Cpart B u v j₀ ∩ fiber proj' v').card : ℝ) /
                  (2 ^ (n - r') : ℝ)) ^ 2 := by
              calc (2 ^ (r' - B.r) : ℝ) * (pC B u v j₀ ^ 2 + (ε / (B.m : ℝ) ^ 3) ^ 2)
                  = (2 ^ (r' - B.r) : ℝ) * (((Cpart B u v j₀).card : ℝ) / (2 ^ (n - B.r) : ℝ)) ^ 2 +
                      (2 ^ (r' - B.r) : ℝ) * (ε / (B.m : ℝ) ^ 3) ^ 2 := by
                        simp only [pC]; ring
                _ ≤ (2 ^ (r' - B.r) : ℝ) * (((Cpart B u v j₀).card : ℝ) / (2 ^ (n - B.r) : ℝ)) ^ 2 +
                      (2 ^ (r' - B.r) : ℝ) *
                        fourierCoeff B.proj.ker (shiftSet B.proj.ker y₀ (Cpart B u v j₀)) ξ ^ 2 :=
                        add_le_add_right hmul _
                _ ≤ _ := hinc
            calc (2 ^ (r' - B.r) : ℝ) ^ 2 * (pC B u v j₀ ^ 2 + (ε / (B.m : ℝ) ^ 3) ^ 2)
                = (2 ^ (r' - B.r) : ℝ) *
                    ((2 ^ (r' - B.r) : ℝ) * (pC B u v j₀ ^ 2 + (ε / (B.m : ℝ) ^ 3) ^ 2)) := by ring
              _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)
          have hrest := sum_le_sum fun j (_ : j ∈ (univ : Finset (Fin B.m)).erase j₀) => hC_ge j
          rw [← mul_sum] at hrest
          have hsumC : (2 ^ (r' - B.r) : ℝ) ^ 2 *
              ((∑ j, pC B u v j ^ 2) + (ε / (B.m : ℝ) ^ 3) ^ 2) ≤
              ∑ u' ∈ fiber q u, ∑ v' ∈ fiber q v, ∑ j, pC B' u' v' j ^ 2 := by
            rw [← add_sum_erase (univ : Finset (Fin B.m)) (fun j => pC B u v j ^ 2) (mem_univ j₀)]
            rw [hswC, ← add_sum_erase (univ : Finset (Fin B.m))
              (fun j => ∑ u' ∈ fiber q u, ∑ v' ∈ fiber q v, pC B' u' v' j ^ 2) (mem_univ j₀)]
            calc (2 ^ (r' - B.r) : ℝ) ^ 2 *
                  ((pC B u v j₀ ^ 2 + ∑ j ∈ (univ : Finset (Fin B.m)).erase j₀, pC B u v j ^ 2) +
                    (ε / (B.m : ℝ) ^ 3) ^ 2)
                = (2 ^ (r' - B.r) : ℝ) ^ 2 * (pC B u v j₀ ^ 2 + (ε / (B.m : ℝ) ^ 3) ^ 2) +
                    (2 ^ (r' - B.r) : ℝ) ^ 2 *
                      ∑ j ∈ (univ : Finset (Fin B.m)).erase j₀, pC B u v j ^ 2 := by ring
              _ ≤ _ := add_le_add hC₀ hrest
          have htot := add_le_add (add_le_add hsumB0 hsumC) hsumD0
          have hdiv := div_le_div_of_nonneg_right htot (by norm_num : (0 : ℝ) ≤ 3)
          calc (2 ^ (r' - B.r) : ℝ) ^ 2 *
                ((∑ i, pB B u v i ^ 2 + ∑ j, pC B u v j ^ 2 + ∑ k, pD B u v k ^ 2) / 3 +
                  (ε / (B.m : ℝ) ^ 3) ^ 2 / 3)
              = ((2 ^ (r' - B.r) : ℝ) ^ 2 * ∑ i, pB B u v i ^ 2 +
                  (2 ^ (r' - B.r) : ℝ) ^ 2 * ((∑ j, pC B u v j ^ 2) + (ε / (B.m : ℝ) ^ 3) ^ 2) +
                  (2 ^ (r' - B.r) : ℝ) ^ 2 * ∑ k, pD B u v k ^ 2) / 3 := by ring
            _ ≤ _ := hdiv
        · have hinc := e1_refine_part_fourier_inc B.proj proj' B.hsurj hsurj' q hq_comp (u + v)
            (Dpart B u v k₀) (filter_subset _ _) z₀ hz₀ ξ hξ0 (extW ξ) (hextW ξ) hvanξ hpow_rel
          have hlt_sq : (ε / (B.m : ℝ) ^ 3) ^ 2 ≤
              fourierCoeff W (shiftSet W z₀ (Dpart B u v k₀)) ξ ^ 2 := by
            calc (ε / (B.m : ℝ) ^ 3) ^ 2
                ≤ |fourierCoeff W (shiftSet W z₀ (Dpart B u v k₀)) ξ| ^ 2 :=
                  pow_le_pow_left₀ (by positivity) hlt.le 2
              _ = _ := sq_abs _
          have hD₀ : (2 ^ (r' - B.r) : ℝ) ^ 2 *
              (pD B u v k₀ ^ 2 + (ε / (B.m : ℝ) ^ 3) ^ 2) ≤
              ∑ u' ∈ fiber q u, ∑ v' ∈ fiber q v, pD B' u' v' k₀ ^ 2 := by
            rw [hD_eq k₀]
            have hmul : (2 ^ (r' - B.r) : ℝ) * (ε / (B.m : ℝ) ^ 3) ^ 2 ≤
                (2 ^ (r' - B.r) : ℝ) *
                  fourierCoeff B.proj.ker (shiftSet B.proj.ker z₀ (Dpart B u v k₀)) ξ ^ 2 :=
              mul_le_mul_of_nonneg_left hlt_sq (by positivity)
            have h1 : (2 ^ (r' - B.r) : ℝ) * (pD B u v k₀ ^ 2 + (ε / (B.m : ℝ) ^ 3) ^ 2) ≤
                ∑ w' ∈ fiber q (u + v), (((Dpart B u v k₀ ∩ fiber proj' w').card : ℝ) /
                  (2 ^ (n - r') : ℝ)) ^ 2 := by
              calc (2 ^ (r' - B.r) : ℝ) * (pD B u v k₀ ^ 2 + (ε / (B.m : ℝ) ^ 3) ^ 2)
                  = (2 ^ (r' - B.r) : ℝ) * (((Dpart B u v k₀).card : ℝ) / (2 ^ (n - B.r) : ℝ)) ^ 2 +
                      (2 ^ (r' - B.r) : ℝ) * (ε / (B.m : ℝ) ^ 3) ^ 2 := by
                        simp only [pD]; ring
                _ ≤ (2 ^ (r' - B.r) : ℝ) * (((Dpart B u v k₀).card : ℝ) / (2 ^ (n - B.r) : ℝ)) ^ 2 +
                      (2 ^ (r' - B.r) : ℝ) *
                        fourierCoeff B.proj.ker (shiftSet B.proj.ker z₀ (Dpart B u v k₀)) ξ ^ 2 :=
                        add_le_add_right hmul _
                _ ≤ _ := hinc
            calc (2 ^ (r' - B.r) : ℝ) ^ 2 * (pD B u v k₀ ^ 2 + (ε / (B.m : ℝ) ^ 3) ^ 2)
                = (2 ^ (r' - B.r) : ℝ) *
                    ((2 ^ (r' - B.r) : ℝ) * (pD B u v k₀ ^ 2 + (ε / (B.m : ℝ) ^ 3) ^ 2)) := by ring
              _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)
          have hrest := sum_le_sum fun k (_ : k ∈ (univ : Finset (Fin B.m)).erase k₀) => hD_ge k
          rw [← mul_sum] at hrest
          have hsumD : (2 ^ (r' - B.r) : ℝ) ^ 2 *
              ((∑ k, pD B u v k ^ 2) + (ε / (B.m : ℝ) ^ 3) ^ 2) ≤
              ∑ u' ∈ fiber q u, ∑ v' ∈ fiber q v, ∑ k, pD B' u' v' k ^ 2 := by
            rw [← add_sum_erase (univ : Finset (Fin B.m)) (fun k => pD B u v k ^ 2) (mem_univ k₀)]
            rw [hswD, ← add_sum_erase (univ : Finset (Fin B.m))
              (fun k => ∑ u' ∈ fiber q u, ∑ v' ∈ fiber q v, pD B' u' v' k ^ 2) (mem_univ k₀)]
            calc (2 ^ (r' - B.r) : ℝ) ^ 2 *
                  ((pD B u v k₀ ^ 2 + ∑ k ∈ (univ : Finset (Fin B.m)).erase k₀, pD B u v k ^ 2) +
                    (ε / (B.m : ℝ) ^ 3) ^ 2)
                = (2 ^ (r' - B.r) : ℝ) ^ 2 * (pD B u v k₀ ^ 2 + (ε / (B.m : ℝ) ^ 3) ^ 2) +
                    (2 ^ (r' - B.r) : ℝ) ^ 2 *
                      ∑ k ∈ (univ : Finset (Fin B.m)).erase k₀, pD B u v k ^ 2 := by ring
              _ ≤ _ := add_le_add hD₀ hrest
          have htot := add_le_add (add_le_add hsumB0 hsumC0) hsumD
          have hdiv := div_le_div_of_nonneg_right htot (by norm_num : (0 : ℝ) ≤ 3)
          calc (2 ^ (r' - B.r) : ℝ) ^ 2 *
                ((∑ i, pB B u v i ^ 2 + ∑ j, pC B u v j ^ 2 + ∑ k, pD B u v k ^ 2) / 3 +
                  (ε / (B.m : ℝ) ^ 3) ^ 2 / 3)
              = ((2 ^ (r' - B.r) : ℝ) ^ 2 * ∑ i, pB B u v i ^ 2 +
                  (2 ^ (r' - B.r) : ℝ) ^ 2 * ∑ j, pC B u v j ^ 2 +
                  (2 ^ (r' - B.r) : ℝ) ^ 2 * ((∑ k, pD B u v k ^ 2) + (ε / (B.m : ℝ) ^ 3) ^ 2)) / 3 := by ring
            _ ≤ _ := hdiv
      · simp only [hbad, ↓reduceIte, add_zero]
        have hsumB := sum_le_sum fun i (_ : i ∈ univ) => hB_ge i
        have hsumC := sum_le_sum fun j (_ : j ∈ univ) => hC_ge j
        have hsumD := sum_le_sum fun k (_ : k ∈ univ) => hD_ge k
        simp_rw [← mul_sum] at hsumB hsumC hsumD
        rw [← hswB] at hsumB
        rw [← hswC] at hsumC
        rw [← hswD] at hsumD
        simp only [sum_add_distrib, ← sum_div]
        linarith
    have hsum_box := sum_le_sum fun u (_ : u ∈ univ) => sum_le_sum fun v (_ : v ∈ univ) => hbox_E1 u v
    have hbad_sum :
        (∑ u : 𝔽₂ B.r, ∑ v : 𝔽₂ B.r, if (u, v) ∈ bad1 then (ε / (B.m : ℝ) ^ 3) ^ 2 / 3 else 0) =
          (bad1.card : ℝ) * ((ε / (B.m : ℝ) ^ 3) ^ 2 / 3) := by
      calc (∑ u : 𝔽₂ B.r, ∑ v : 𝔽₂ B.r, if (u, v) ∈ bad1 then (ε / (B.m : ℝ) ^ 3) ^ 2 / 3 else 0)
          = ∑ p : 𝔽₂ B.r × 𝔽₂ B.r, if p ∈ bad1 then (ε / (B.m : ℝ) ^ 3) ^ 2 / 3 else 0 :=
            (Fintype.sum_prod_type (fun p : 𝔽₂ B.r × 𝔽₂ B.r =>
              if p ∈ bad1 then (ε / (B.m : ℝ) ^ 3) ^ 2 / 3 else 0)).symm
        _ = (bad1.card : ℝ) * ((ε / (B.m : ℝ) ^ 3) ^ 2 / 3) := by
            rw [← Finset.sum_filter]
            simp
    have hinc_lb : ε ^ 3 / (3 * (B.m : ℝ) ^ 6) * (4 ^ B.r : ℝ) ≤
        (bad1.card : ℝ) * ((ε / (B.m : ℝ) ^ 3) ^ 2 / 3) := by
      have heq1 : (ε / (B.m : ℝ) ^ 3) ^ 2 / 3 = ε ^ 2 / (3 * (B.m : ℝ) ^ 6) := by ring
      have heq2 : ε ^ 3 / (3 * (B.m : ℝ) ^ 6) * (4 ^ B.r : ℝ) =
          (ε * (4 ^ B.r : ℝ)) * (ε ^ 2 / (3 * (B.m : ℝ) ^ 6)) := by ring
      rw [heq1, heq2]
      exact mul_le_mul_of_nonneg_right hbad1_gt.le (by positivity)
    unfold energyE1
    rw [hsum_split, hpow4_rel]
    have h4pos : (0 : ℝ) < (4 ^ B.r : ℝ) := by positivity
    have h2pos : (0 : ℝ) < (2 ^ (r' - B.r) : ℝ) ^ 2 := by positivity
    have hsum_box' : (2 ^ (r' - B.r) : ℝ) ^ 2 *
        ((∑ u, ∑ v, (∑ i, pB B u v i ^ 2 + ∑ j, pC B u v j ^ 2 + ∑ k, pD B u v k ^ 2) / 3) +
          (bad1.card : ℝ) * ((ε / (B.m : ℝ) ^ 3) ^ 2 / 3)) ≤
        ∑ u, ∑ v, ∑ u' ∈ fiber q u, ∑ v' ∈ fiber q v,
          (∑ i, pB B' u' v' i ^ 2 + ∑ j, pC B' u' v' j ^ 2 + ∑ k, pD B' u' v' k ^ 2) / 3 := by
      rw [← hbad_sum]
      calc (2 ^ (r' - B.r) : ℝ) ^ 2 *
            ((∑ u, ∑ v, (∑ i, pB B u v i ^ 2 + ∑ j, pC B u v j ^ 2 + ∑ k, pD B u v k ^ 2) / 3) +
              ∑ u, ∑ v, if (u, v) ∈ bad1 then (ε / (B.m : ℝ) ^ 3) ^ 2 / 3 else 0)
          = (2 ^ (r' - B.r) : ℝ) ^ 2 *
              ∑ u, ∑ v, ((∑ i, pB B u v i ^ 2 + ∑ j, pC B u v j ^ 2 + ∑ k, pD B u v k ^ 2) / 3 +
                if (u, v) ∈ bad1 then (ε / (B.m : ℝ) ^ 3) ^ 2 / 3 else 0) := by
              simp only [sum_add_distrib]
        _ = ∑ u, ∑ v, (2 ^ (r' - B.r) : ℝ) ^ 2 *
              ((∑ i, pB B u v i ^ 2 + ∑ j, pC B u v j ^ 2 + ∑ k, pD B u v k ^ 2) / 3 +
                if (u, v) ∈ bad1 then (ε / (B.m : ℝ) ^ 3) ^ 2 / 3 else 0) := by
              rw [mul_sum]; refine sum_congr rfl fun u _ => ?_; rw [mul_sum]
        _ ≤ _ := hsum_box
    have hdiv := div_le_div_of_nonneg_right hsum_box' (mul_pos h4pos h2pos).le
    have hlhs_simp :
        (2 ^ (r' - B.r) : ℝ) ^ 2 *
          ((∑ u, ∑ v, (∑ i, pB B u v i ^ 2 + ∑ j, pC B u v j ^ 2 + ∑ k, pD B u v k ^ 2) / 3) +
            (bad1.card : ℝ) * ((ε / (B.m : ℝ) ^ 3) ^ 2 / 3)) /
          ((4 ^ B.r : ℝ) * (2 ^ (r' - B.r) : ℝ) ^ 2) =
        (∑ u, ∑ v, (∑ i, pB B u v i ^ 2 + ∑ j, pC B u v j ^ 2 + ∑ k, pD B u v k ^ 2) / 3) /
            (4 ^ B.r : ℝ) +
          ((bad1.card : ℝ) * ((ε / (B.m : ℝ) ^ 3) ^ 2 / 3)) / (4 ^ B.r : ℝ) := by
      field_simp [h4pos.ne', h2pos.ne']
    rw [hlhs_simp] at hdiv
    have hinc_div : ε ^ 3 / (3 * (B.m : ℝ) ^ 6) ≤
        ((bad1.card : ℝ) * ((ε / (B.m : ℝ) ^ 3) ^ 2 / 3)) / (4 ^ B.r : ℝ) :=
      (le_div_iff₀ h4pos).mpr hinc_lb
    linarith
  have hBr' : B'.r ≤ B.r + 4 ^ B.r := by
    have hLlen : L.length = bad1.toList.length := List.length_map _
    change r' ≤ B.r + 4 ^ B.r
    omega
  exact ⟨B', rfl, hBr', hE2_ge, hE1_inc⟩

open scoped Classical in
private lemma e2_block_inc_qr {α : Type*} [DecidableEq α]
    (Wcard ε : ℝ) (hW_pos : 0 < Wcard) (hε : 0 ≤ ε)
    (m m' : ℕ) (X Y : Fin m → Finset α) (X' Y' : Fin m' → Finset α)
    (getX getY : Fin m' → Fin m)
    (bitX bitY : Fin m' → Fin m → Bool)
    (E : Finset (α × α)) (Xwit Ywit : Fin m → Fin m → Finset α)
    (hX'dis : ((univ : Finset (Fin m')) : Set (Fin m')).PairwiseDisjoint X')
    (hY'dis : ((univ : Finset (Fin m')) : Set (Fin m')).PairwiseDisjoint Y')
    (hXcov : ∀ i, (univ.filter (fun i' => getX i' = i)).biUnion X' = X i)
    (hYcov : ∀ j, (univ.filter (fun j' => getY j' = j)).biUnion Y' = Y j)
    (hXbit : ∀ i' j x, x ∈ X' i' → (bitX i' j = true ↔ x ∈ Xwit (getX i') j))
    (hYbit : ∀ j' i y, y ∈ Y' j' → (bitY j' i = true ↔ y ∈ Ywit i (getY j')))
    (hwitSub : ∀ i j, Xwit i j ⊆ X i ∧ Ywit i j ⊆ Y j)
    (hwitQR : ∀ i j, ¬ IsQuasirandom E (X i) (Y j) ε →
      ε * ((X i).card : ℝ) ≤ ((Xwit i j).card : ℝ) ∧
      ε * ((Y j).card : ℝ) ≤ ((Ywit i j).card : ℝ) ∧
      ε < |densBip E (Xwit i j) (Ywit i j) - densBip E (X i) (Y j)|) :
    (∑ i : Fin m, ∑ j : Fin m,
        (((X i).card : ℝ) / Wcard * ((Y j).card : ℝ) / Wcard * densBip E (X i) (Y j) ^ 2 +
        if IsQuasirandom E (X i) (Y j) ε then 0
        else ((X i).card : ℝ) / Wcard * ((Y j).card : ℝ) / Wcard * ε ^ 4)) ≤
      ∑ i' : Fin m', ∑ j' : Fin m',
        ((X' i').card : ℝ) / Wcard * ((Y' j').card : ℝ) / Wcard * densBip E (X' i') (Y' j') ^ 2 := by
  classical
  have hpair : ∀ i j : Fin m,
      ((X i).card : ℝ) / Wcard * ((Y j).card : ℝ) / Wcard * densBip E (X i) (Y j) ^ 2 +
        (if IsQuasirandom E (X i) (Y j) ε then 0
          else ((X i).card : ℝ) / Wcard * ((Y j).card : ℝ) / Wcard * ε ^ 4) ≤
        ∑ i' ∈ univ.filter (fun i' => getX i' = i),
          ∑ j' ∈ univ.filter (fun j' => getY j' = j),
            ((X' i').card : ℝ) / Wcard * ((Y' j').card : ℝ) / Wcard * densBip E (X' i') (Y' j') ^ 2 := by
    intro i j
    let sI := univ.filter (fun i' => getX i' = i)
    let sJ := univ.filter (fun j' => getY j' = j)
    let parts := fun q : Fin m' × Fin m' => X' q.1 ×ˢ Y' q.2
    have hcov : (sI ×ˢ sJ).biUnion parts = X i ×ˢ Y j := by
      rw [← hXcov i, ← hYcov j]
      ext ⟨x, y⟩
      simp only [parts, mem_biUnion, mem_product]
      exact ⟨fun ⟨⟨i', j'⟩, ⟨hi', hj'⟩, hx, hy⟩ => ⟨⟨i', hi', hx⟩, ⟨j', hj', hy⟩⟩,
             fun ⟨⟨i', hi', hx⟩, ⟨j', hj', hy⟩⟩ => ⟨(i', j'), ⟨hi', hj'⟩, hx, hy⟩⟩
    have hdis : ((sI ×ˢ sJ : Finset (Fin m' × Fin m')) : Set (Fin m' × Fin m')).PairwiseDisjoint parts := by
      intro q₁ _ q₂ _ hne
      refine Finset.disjoint_left.mpr ?_
      rintro ⟨x, y⟩ h₁ h₂
      simp only [parts, mem_product] at h₁ h₂
      by_cases h1 : q₁.1 = q₂.1
      · have h2 : q₁.2 ≠ q₂.2 := fun he => hne (Prod.ext h1 he)
        exact Finset.disjoint_left.mp (hY'dis (mem_univ q₁.2) (mem_univ q₂.2) h2) h₁.2 h₂.2
      · exact Finset.disjoint_left.mp (hX'dis (mem_univ q₁.1) (mem_univ q₂.1) h1) h₁.1 h₂.1
    have hr : ∑ q ∈ sI ×ˢ sJ, ((parts q).card : ℝ) * setDens E (parts q) ^ 2 =
        Wcard ^ 2 * ∑ i' ∈ sI, ∑ j' ∈ sJ,
          ((X' i').card : ℝ) / Wcard * ((Y' j').card : ℝ) / Wcard * densBip E (X' i') (Y' j') ^ 2 := by
      rw [sum_product, mul_sum]
      refine sum_congr rfl fun i' _ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun j' _ => ?_
      simp only [parts, card_product, Nat.cast_mul, densBip]
      field_simp [hW_pos.ne']
    by_cases hqr : IsQuasirandom E (X i) (Y j) ε
    · simp only [hqr, ↓reduceIte, add_zero]
      have hvar := sum_card_mul_setDens_sq_ge (sI ×ˢ sJ) parts (X i ×ˢ Y j) E hcov hdis
      have hl : ((X i ×ˢ Y j).card : ℝ) * setDens E (X i ×ˢ Y j) ^ 2 =
          Wcard ^ 2 * (((X i).card : ℝ) / Wcard * ((Y j).card : ℝ) / Wcard * densBip E (X i) (Y j) ^ 2) := by
        rw [card_product, Nat.cast_mul]; simp only [densBip]; field_simp [hW_pos.ne']
      rw [hl, hr] at hvar
      exact le_of_mul_le_mul_left hvar (sq_pos_of_pos hW_pos)
    · simp only [hqr, ↓reduceIte]
      obtain ⟨hcardX, hcardY, hdiff⟩ := hwitQR i j hqr
      let U := Xwit i j ×ˢ Ywit i j
      have hUS : U ⊆ X i ×ˢ Y j := product_subset_product (hwitSub i j).1 (hwitSub i j).2
      have hrefine : ∀ q ∈ sI ×ˢ sJ, parts q ⊆ U ∨ Disjoint (parts q) U := by
        rintro ⟨i', j'⟩ hq
        simp only [mem_product, mem_filter, mem_univ, true_and, sI, sJ] at hq
        rcases hq with ⟨hi', hj'⟩
        by_cases h1 : bitX i' j = true ∧ bitY j' i = true
        · left
          intro p hp
          rcases p with ⟨x, y⟩
          simp only [parts, mem_product] at hp
          have hx' := (hXbit i' j x hp.1).mp h1.1
          have hy' := (hYbit j' i y hp.2).mp h1.2
          rw [hi'] at hx'
          rw [hj'] at hy'
          exact mem_product.mpr ⟨hx', hy'⟩
        · right
          refine Finset.disjoint_left.mpr ?_
          intro p hp hxy
          rcases p with ⟨x, y⟩
          simp only [parts, U, mem_product] at hp hxy
          have hxb : bitX i' j = true := (hXbit i' j x hp.1).mpr (by rw [hi']; exact hxy.1)
          have hyb : bitY j' i = true := (hYbit j' i y hp.2).mpr (by rw [hj']; exact hxy.2)
          exact h1 ⟨hxb, hyb⟩
      have hvar := sum_card_mul_setDens_sq_ge_add (sI ×ˢ sJ) parts (X i ×ˢ Y j) E U hcov hdis hUS hrefine
      have hU_card : ε ^ 2 * ((X i ×ˢ Y j).card : ℝ) ≤ (U.card : ℝ) := by
        simp only [U, card_product, Nat.cast_mul]
        calc ε ^ 2 * (((X i).card : ℝ) * ((Y j).card : ℝ))
            = (ε * ((X i).card : ℝ)) * (ε * ((Y j).card : ℝ)) := by ring
          _ ≤ ((Xwit i j).card : ℝ) * ((Ywit i j).card : ℝ) :=
              mul_le_mul hcardX hcardY (by positivity) (by positivity)
      have hdiff_sq : ε ^ 2 ≤ (setDens E U - setDens E (X i ×ˢ Y j)) ^ 2 := by
        calc ε ^ 2
            ≤ |densBip E (Xwit i j) (Ywit i j) - densBip E (X i) (Y j)| ^ 2 :=
              pow_le_pow_left₀ hε hdiff.le 2
          _ = (setDens E U - setDens E (X i ×ˢ Y j)) ^ 2 := by
              simp [U, densBip, sq_abs]
      have hincU : ε ^ 4 * ((X i ×ˢ Y j).card : ℝ) ≤
          (U.card : ℝ) * (setDens E U - setDens E (X i ×ˢ Y j)) ^ 2 := by
        calc ε ^ 4 * ((X i ×ˢ Y j).card : ℝ)
            = (ε ^ 2 * ((X i ×ˢ Y j).card : ℝ)) * ε ^ 2 := by ring
          _ ≤ (U.card : ℝ) * (setDens E U - setDens E (X i ×ˢ Y j)) ^ 2 :=
              mul_le_mul hU_card hdiff_sq (by positivity) (by positivity)
      have hl : ((X i ×ˢ Y j).card : ℝ) * setDens E (X i ×ˢ Y j) ^ 2 +
            ε ^ 4 * ((X i ×ˢ Y j).card : ℝ) =
          Wcard ^ 2 * (((X i).card : ℝ) / Wcard * ((Y j).card : ℝ) / Wcard *
            densBip E (X i) (Y j) ^ 2 +
            ((X i).card : ℝ) / Wcard * ((Y j).card : ℝ) / Wcard * ε ^ 4) := by
        rw [card_product, Nat.cast_mul]; simp only [densBip]; field_simp [hW_pos.ne']
      have hcomb : Wcard ^ 2 * (((X i).card : ℝ) / Wcard * ((Y j).card : ℝ) / Wcard *
            densBip E (X i) (Y j) ^ 2 +
            ((X i).card : ℝ) / Wcard * ((Y j).card : ℝ) / Wcard * ε ^ 4) ≤
          Wcard ^ 2 * ∑ i' ∈ sI, ∑ j' ∈ sJ,
            ((X' i').card : ℝ) / Wcard * ((Y' j').card : ℝ) / Wcard * densBip E (X' i') (Y' j') ^ 2 := by
        linarith
      exact le_of_mul_le_mul_left hcomb (sq_pos_of_pos hW_pos)
  have hsum := sum_le_sum fun i (_ : i ∈ univ) => sum_le_sum fun j (_ : j ∈ univ) => hpair i j
  have hsplit_fin : ∀ (f : Fin m' → Fin m' → ℝ),
      (∑ i' : Fin m', ∑ j' : Fin m', f i' j') =
        ∑ i : Fin m, ∑ j : Fin m,
          ∑ i' ∈ univ.filter (fun i' => getX i' = i),
            ∑ j' ∈ univ.filter (fun j' => getY j' = j), f i' j' := by
    intro f
    have hcovX : (univ : Finset (Fin m')) =
        univ.biUnion (fun i : Fin m => univ.filter (fun i' => getX i' = i)) := by ext i'; simp
    have hcovY : (univ : Finset (Fin m')) =
        univ.biUnion (fun j : Fin m => univ.filter (fun j' => getY j' = j)) := by ext j'; simp
    have hdjX : ((univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint
        (fun i => univ.filter (fun i' => getX i' = i)) := by
      intro a _ b _ hab
      refine Finset.disjoint_left.mpr fun i' ha hb => ?_
      simp only [mem_filter] at ha hb
      exact hab (ha.2.symm.trans hb.2)
    have hdjY : ((univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint
        (fun j => univ.filter (fun j' => getY j' = j)) := by
      intro a _ b _ hab
      refine Finset.disjoint_left.mpr fun j' ha hb => ?_
      simp only [mem_filter] at ha hb
      exact hab (ha.2.symm.trans hb.2)
    let S₁ : Finset (Fin m') → ℝ := fun s => ∑ i' ∈ s, ∑ j' : Fin m', f i' j'
    let S₂ : Fin m' → Finset (Fin m') → ℝ := fun i' s => ∑ j' ∈ s, f i' j'
    calc ∑ i' : Fin m', ∑ j' : Fin m', f i' j'
        = S₁ univ := rfl
      _ = S₁ (univ.biUnion (fun i : Fin m => univ.filter (fun i' => getX i' = i))) :=
          congrArg S₁ hcovX
      _ = ∑ i : Fin m, ∑ i' ∈ univ.filter (fun i' => getX i' = i), ∑ j' : Fin m', f i' j' :=
          sum_biUnion hdjX
      _ = ∑ i : Fin m, ∑ i' ∈ univ.filter (fun i' => getX i' = i), S₂ i' univ := rfl
      _ = ∑ i : Fin m, ∑ i' ∈ univ.filter (fun i' => getX i' = i),
            S₂ i' (univ.biUnion (fun j : Fin m => univ.filter (fun j' => getY j' = j))) := by
          refine sum_congr rfl fun i _ => sum_congr rfl fun i' _ => ?_
          exact congrArg (S₂ i') hcovY
      _ = ∑ i : Fin m, ∑ i' ∈ univ.filter (fun i' => getX i' = i),
            ∑ j : Fin m, ∑ j' ∈ univ.filter (fun j' => getY j' = j), f i' j' := by
          refine sum_congr rfl fun i _ => sum_congr rfl fun i' _ => sum_biUnion hdjY
      _ = _ := by refine sum_congr rfl fun i _ => sum_comm
  rw [← hsplit_fin] at hsum
  exact hsum

private lemma refinement_B {n : ℕ} (A : Finset (𝔽₂ n × 𝔽₂ n)) (B : Boxing n)
    {ε : ℝ} (hε : 0 < ε) (hfail : ¬ Cond2 A B ε) :
    ∃ B' : Boxing n,
      B'.r = B.r ∧
      B'.m = B.m * 4 ^ B.m ∧
      energyE2 A B + ε ^ 6 / 3 ≤ energyE2 A B' := by
  classical
  let α := Fin B.m × (Fin B.m → Bool) × (Fin B.m → Bool)
  let m' : ℕ := Fintype.card α
  have hm'eq : m' = B.m * 4 ^ B.m := by
    simp only [m', α, Fintype.card_prod, Fintype.card_fin, Fintype.card_fun, Fintype.card_bool]
    have h4 : 2 ^ B.m * 2 ^ B.m = 4 ^ B.m := by rw [← mul_pow]; norm_num
    rw [h4]
  have hm'pos : 0 < m' := by rw [hm'eq]; exact Nat.mul_pos B.hm (pow_pos (by norm_num) _)
  let enc : α ≃ Fin m' := Fintype.equivFin α
  have hwitBC : ∀ u v i j,
      ∃ p : Finset (𝔽₂ n) × Finset (𝔽₂ n),
        p.1 ⊆ Bpart B u v i ∧ p.2 ⊆ Cpart B u v j ∧
        (¬ IsQuasirandom (E_BC A) (Bpart B u v i) (Cpart B u v j) ε →
          ε * ((Bpart B u v i).card : ℝ) ≤ (p.1.card : ℝ) ∧
          ε * ((Cpart B u v j).card : ℝ) ≤ (p.2.card : ℝ) ∧
          ε < |densBip (E_BC A) p.1 p.2 -
            densBip (E_BC A) (Bpart B u v i) (Cpart B u v j)|) := by
    intro u v i j
    by_cases h : IsQuasirandom (E_BC A) (Bpart B u v i) (Cpart B u v j) ε
    · exact ⟨(∅, ∅), empty_subset _, empty_subset _, fun hn => absurd h hn⟩
    · have h' := h
      unfold IsQuasirandom at h'
      push Not at h'
      rcases h' with ⟨B1, hB1, C1, hC1, hcardB, hcardC, hdiff⟩
      exact ⟨(B1, C1), hB1, hC1, fun _ => ⟨hcardB, hcardC, hdiff⟩⟩
  have hwitBD : ∀ u v i k,
      ∃ p : Finset (𝔽₂ n) × Finset (𝔽₂ n),
        p.1 ⊆ Bpart B u v i ∧ p.2 ⊆ Dpart B u v k ∧
        (¬ IsQuasirandom (E_BD A) (Bpart B u v i) (Dpart B u v k) ε →
          ε * ((Bpart B u v i).card : ℝ) ≤ (p.1.card : ℝ) ∧
          ε * ((Dpart B u v k).card : ℝ) ≤ (p.2.card : ℝ) ∧
          ε < |densBip (E_BD A) p.1 p.2 -
            densBip (E_BD A) (Bpart B u v i) (Dpart B u v k)|) := by
    intro u v i k
    by_cases h : IsQuasirandom (E_BD A) (Bpart B u v i) (Dpart B u v k) ε
    · exact ⟨(∅, ∅), empty_subset _, empty_subset _, fun hn => absurd h hn⟩
    · have h' := h
      unfold IsQuasirandom at h'
      push Not at h'
      rcases h' with ⟨B2, hB2, D2, hD2, hcardB, hcardD, hdiff⟩
      exact ⟨(B2, D2), hB2, hD2, fun _ => ⟨hcardB, hcardD, hdiff⟩⟩
  have hwitCD : ∀ u v j k,
      ∃ p : Finset (𝔽₂ n) × Finset (𝔽₂ n),
        p.1 ⊆ Cpart B u v j ∧ p.2 ⊆ Dpart B u v k ∧
        (¬ IsQuasirandom (E_CD A) (Cpart B u v j) (Dpart B u v k) ε →
          ε * ((Cpart B u v j).card : ℝ) ≤ (p.1.card : ℝ) ∧
          ε * ((Dpart B u v k).card : ℝ) ≤ (p.2.card : ℝ) ∧
          ε < |densBip (E_CD A) p.1 p.2 -
            densBip (E_CD A) (Cpart B u v j) (Dpart B u v k)|) := by
    intro u v j k
    by_cases h : IsQuasirandom (E_CD A) (Cpart B u v j) (Dpart B u v k) ε
    · exact ⟨(∅, ∅), empty_subset _, empty_subset _, fun hn => absurd h hn⟩
    · have h' := h
      unfold IsQuasirandom at h'
      push Not at h'
      rcases h' with ⟨C3, hC3, D3, hD3, hcardC, hcardD, hdiff⟩
      exact ⟨(C3, D3), hC3, hD3, fun _ => ⟨hcardC, hcardD, hdiff⟩⟩
  let B1w : 𝔽₂ B.r → 𝔽₂ B.r → Fin B.m → Fin B.m → Finset (𝔽₂ n) :=
    fun u v i j => (Classical.choose (hwitBC u v i j)).1
  let C1w : 𝔽₂ B.r → 𝔽₂ B.r → Fin B.m → Fin B.m → Finset (𝔽₂ n) :=
    fun u v i j => (Classical.choose (hwitBC u v i j)).2
  let B2w : 𝔽₂ B.r → 𝔽₂ B.r → Fin B.m → Fin B.m → Finset (𝔽₂ n) :=
    fun u v i k => (Classical.choose (hwitBD u v i k)).1
  let D2w : 𝔽₂ B.r → 𝔽₂ B.r → Fin B.m → Fin B.m → Finset (𝔽₂ n) :=
    fun u v i k => (Classical.choose (hwitBD u v i k)).2
  let C3w : 𝔽₂ B.r → 𝔽₂ B.r → Fin B.m → Fin B.m → Finset (𝔽₂ n) :=
    fun u v j k => (Classical.choose (hwitCD u v j k)).1
  let D3w : 𝔽₂ B.r → 𝔽₂ B.r → Fin B.m → Fin B.m → Finset (𝔽₂ n) :=
    fun u v j k => (Classical.choose (hwitCD u v j k)).2
  let B' : Boxing n :=
    { r := B.r
      proj := B.proj
      hsurj := B.hsurj
      m := m'
      hm := hm'pos
      bCol := fun u v x => enc (B.bCol u v x,
        fun j => decide (x ∈ B1w u v (B.bCol u v x) j),
        fun k => decide (x ∈ B2w u v (B.bCol u v x) k))
      cCol := fun u v y => enc (B.cCol u v y,
        fun i => decide (y ∈ C1w u v i (B.cCol u v y)),
        fun k => decide (y ∈ C3w u v (B.cCol u v y) k))
      dCol := fun u v z => enc (B.dCol u v z,
        fun i => decide (z ∈ D2w u v i (B.dCol u v z)),
        fun j => decide (z ∈ D3w u v j (B.dCol u v z))) }
  have hW_pos : (0 : ℝ) < (2 ^ (n - B.r) : ℝ) := by positivity
  let bad2 : Finset (𝔽₂ B.r × 𝔽₂ B.r) :=
    univ.filter (fun p : 𝔽₂ B.r × 𝔽₂ B.r => ¬ OuterBoxReg2 A B ε p.1 p.2)
  have hbad2_gt : ε * (4 ^ B.r : ℝ) < (bad2.card : ℝ) := by
    simpa [Cond2, bad2] using lt_of_not_ge hfail
  have hB'cov : ∀ u v i,
      (univ.filter (fun i' : Fin m' => (enc.symm i').1 = i)).biUnion (Bpart B' u v) =
        Bpart B u v i := by
    intro u v i
    ext x
    simp only [mem_biUnion, mem_filter, mem_univ, true_and, Bpart, B']
    constructor
    · rintro ⟨i', hi', hpx, hcol⟩
      have heq : (enc.symm i').1 = B.bCol u v x := by rw [← hcol]; simp
      exact ⟨hpx, heq.symm.trans hi'⟩
    · rintro ⟨hpx, hcol⟩
      exact ⟨B'.bCol u v x, by simp [B', hcol], hpx, rfl⟩
  have hC'cov : ∀ u v j,
      (univ.filter (fun j' : Fin m' => (enc.symm j').1 = j)).biUnion (Cpart B' u v) =
        Cpart B u v j := by
    intro u v j
    ext y
    simp only [mem_biUnion, mem_filter, mem_univ, true_and, Cpart, B']
    constructor
    · rintro ⟨j', hj', hpy, hcol⟩
      have heq : (enc.symm j').1 = B.cCol u v y := by rw [← hcol]; simp
      exact ⟨hpy, heq.symm.trans hj'⟩
    · rintro ⟨hpy, hcol⟩
      exact ⟨B'.cCol u v y, by simp [B', hcol], hpy, rfl⟩
  have hD'cov : ∀ u v k,
      (univ.filter (fun k' : Fin m' => (enc.symm k').1 = k)).biUnion (Dpart B' u v) =
        Dpart B u v k := by
    intro u v k
    ext z
    simp only [mem_biUnion, mem_filter, mem_univ, true_and, Dpart, B']
    exact ⟨fun ⟨k', hk', hpz, hcol⟩ =>
             ⟨hpz, ((by rw [← hcol]; simp : (enc.symm k').1 = B.dCol u v z).symm.trans hk')⟩,
           fun ⟨hpz, hcol⟩ => ⟨enc (B.dCol u v z, _, _), by simp [hcol], hpz, rfl⟩⟩
  have hbox_E2 : ∀ u v : 𝔽₂ B.r,
      (∑ i, ∑ j, pB B u v i * pC B u v j *
          densBip (E_BC A) (Bpart B u v i) (Cpart B u v j) ^ 2 +
        ∑ i, ∑ k, pB B u v i * pD B u v k *
          densBip (E_BD A) (Bpart B u v i) (Dpart B u v k) ^ 2 +
        ∑ j, ∑ k, pC B u v j * pD B u v k *
          densBip (E_CD A) (Cpart B u v j) (Dpart B u v k) ^ 2) / 3 +
        (if (u, v) ∈ bad2 then ε ^ 5 / 3 else 0) ≤
      (∑ i', ∑ j', pB B' u v i' * pC B' u v j' *
          densBip (E_BC A) (Bpart B' u v i') (Cpart B' u v j') ^ 2 +
        ∑ i', ∑ k', pB B' u v i' * pD B' u v k' *
          densBip (E_BD A) (Bpart B' u v i') (Dpart B' u v k') ^ 2 +
        ∑ j', ∑ k', pC B' u v j' * pD B' u v k' *
          densBip (E_CD A) (Cpart B' u v j') (Dpart B' u v k') ^ 2) / 3 := by
    intro u v
    have hBC_sum := e2_block_inc_qr (2 ^ (n - B.r) : ℝ) ε hW_pos hε.le B.m m'
      (Bpart B u v) (Cpart B u v) (Bpart B' u v) (Cpart B' u v)
      (fun i' => (enc.symm i').1) (fun j' => (enc.symm j').1)
      (fun i' j => (enc.symm i').2.1 j) (fun j' i => (enc.symm j').2.1 i)
      (E_BC A) (B1w u v) (C1w u v)
      (Bpart_disjoint B' u v) (Cpart_disjoint B' u v)
      (hB'cov u v) (hC'cov u v)
      (fun i' j x hx => by
        simp only [Bpart, B', mem_filter] at hx
        have he1 : (enc.symm i').1 = B.bCol u v x := by rw [← hx.2]; simp
        have he2 : (enc.symm i').2.1 j = decide (x ∈ B1w u v (B.bCol u v x) j) := by
          rw [← hx.2]; simp
        rw [he1, he2, decide_eq_true_eq])
      (fun j' i y hy => by
        simp only [Cpart, B', mem_filter] at hy
        have he1 : (enc.symm j').1 = B.cCol u v y := by rw [← hy.2]; simp
        have he2 : (enc.symm j').2.1 i = decide (y ∈ C1w u v i (B.cCol u v y)) := by
          rw [← hy.2]; simp
        rw [he1, he2, decide_eq_true_eq])
      (fun i j => ⟨(Classical.choose_spec (hwitBC u v i j)).1,
        (Classical.choose_spec (hwitBC u v i j)).2.1⟩)
      (fun i j => (Classical.choose_spec (hwitBC u v i j)).2.2)
    have hBD_sum := e2_block_inc_qr (2 ^ (n - B.r) : ℝ) ε hW_pos hε.le B.m m'
      (Bpart B u v) (Dpart B u v) (Bpart B' u v) (Dpart B' u v)
      (fun i' => (enc.symm i').1) (fun k' => (enc.symm k').1)
      (fun i' k => (enc.symm i').2.2 k) (fun k' i => (enc.symm k').2.1 i)
      (E_BD A) (B2w u v) (D2w u v)
      (Bpart_disjoint B' u v) (Dpart_disjoint B' u v)
      (hB'cov u v) (hD'cov u v)
      (fun i' k x hx => by
        simp only [Bpart, B', mem_filter] at hx
        have he1 : (enc.symm i').1 = B.bCol u v x := by rw [← hx.2]; simp
        have he2 : (enc.symm i').2.2 k = decide (x ∈ B2w u v (B.bCol u v x) k) := by
          rw [← hx.2]; simp
        rw [he1, he2, decide_eq_true_eq])
      (fun k' i z hz => by
        simp only [Dpart, B', mem_filter] at hz
        have he1 : (enc.symm k').1 = B.dCol u v z := by rw [← hz.2]; simp
        have he2 : (enc.symm k').2.1 i = decide (z ∈ D2w u v i (B.dCol u v z)) := by
          rw [← hz.2]; simp
        rw [he1, he2, decide_eq_true_eq])
      (fun i k => ⟨(Classical.choose_spec (hwitBD u v i k)).1,
        (Classical.choose_spec (hwitBD u v i k)).2.1⟩)
      (fun i k => (Classical.choose_spec (hwitBD u v i k)).2.2)
    have hCD_sum := e2_block_inc_qr (2 ^ (n - B.r) : ℝ) ε hW_pos hε.le B.m m'
      (Cpart B u v) (Dpart B u v) (Cpart B' u v) (Dpart B' u v)
      (fun j' => (enc.symm j').1) (fun k' => (enc.symm k').1)
      (fun j' k => (enc.symm j').2.2 k) (fun k' j => (enc.symm k').2.2 j)
      (E_CD A) (C3w u v) (D3w u v)
      (Cpart_disjoint B' u v) (Dpart_disjoint B' u v)
      (hC'cov u v) (hD'cov u v)
      (fun j' k y hy => by
        simp only [Cpart, B', mem_filter] at hy
        have he1 : (enc.symm j').1 = B.cCol u v y := by rw [← hy.2]; simp
        have he2 : (enc.symm j').2.2 k = decide (y ∈ C3w u v (B.cCol u v y) k) := by
          rw [← hy.2]; simp
        rw [he1, he2, decide_eq_true_eq])
      (fun k' j z hz => by
        simp only [Dpart, B', mem_filter] at hz
        have he1 : (enc.symm k').1 = B.dCol u v z := by rw [← hz.2]; simp
        have he2 : (enc.symm k').2.2 j = decide (z ∈ D3w u v j (B.dCol u v z)) := by
          rw [← hz.2]; simp
        rw [he1, he2, decide_eq_true_eq])
      (fun j k => ⟨(Classical.choose_spec (hwitCD u v j k)).1,
        (Classical.choose_spec (hwitCD u v j k)).2.1⟩)
      (fun j k => (Classical.choose_spec (hwitCD u v j k)).2.2)
    have hp_rew : ∀ (X Y : Finset (𝔽₂ n)) (d : ℝ),
        (X.card : ℝ) / (2 ^ (n - B.r) : ℝ) * (Y.card : ℝ) / (2 ^ (n - B.r) : ℝ) * d =
          ((X.card : ℝ) / (2 ^ (n - B.r) : ℝ)) * ((Y.card : ℝ) / (2 ^ (n - B.r) : ℝ)) * d :=
      fun _ _ _ => by ring
    simp only [sum_add_distrib] at hBC_sum hBD_sum hCD_sum
    have hbad_weight : (if (u, v) ∈ bad2 then ε ^ 5 else 0) ≤
        (badWeightBC A B ε u v + badWeightBD A B ε u v + badWeightCD A B ε u v) * ε ^ 4 := by
      have hbc0 : 0 ≤ badWeightBC A B ε u v := sum_nonneg fun i _ => sum_nonneg fun j _ => by
        split_ifs <;> [exact le_rfl; exact mul_nonneg (pB_nonneg _ _ _ _) (pC_nonneg _ _ _ _)]
      have hbd0 : 0 ≤ badWeightBD A B ε u v := sum_nonneg fun i _ => sum_nonneg fun k _ => by
        split_ifs <;> [exact le_rfl; exact mul_nonneg (pB_nonneg _ _ _ _) (pD_nonneg _ _ _ _)]
      have hcd0 : 0 ≤ badWeightCD A B ε u v := sum_nonneg fun j _ => sum_nonneg fun k _ => by
        split_ifs <;> [exact le_rfl; exact mul_nonneg (pC_nonneg _ _ _ _) (pD_nonneg _ _ _ _)]
      by_cases hb : (u, v) ∈ bad2
      · simp only [hb, ↓reduceIte]
        have hnot : ¬ OuterBoxReg2 A B ε u v := (mem_filter.mp hb).2
        have hsum_gt : ε ≤ badWeightBC A B ε u v + badWeightBD A B ε u v + badWeightCD A B ε u v := by
          unfold OuterBoxReg2 at hnot
          by_cases h1 : ε < badWeightBC A B ε u v
          · linarith
          · by_cases h2 : ε < badWeightBD A B ε u v
            · linarith
            · have h3 : ε < badWeightCD A B ε u v := by
                by_contra h3le
                exact hnot ⟨not_lt.mp h1, not_lt.mp h2, not_lt.mp h3le⟩
              linarith
        calc ε ^ 5 = ε * ε ^ 4 := by ring
          _ ≤ (badWeightBC A B ε u v + badWeightBD A B ε u v + badWeightCD A B ε u v) * ε ^ 4 :=
              mul_le_mul_of_nonneg_right hsum_gt (by positivity)
      · simp only [hb, ↓reduceIte]
        exact mul_nonneg (by linarith) (by positivity)
    have hrewrite :
        (∑ i, ∑ j, if IsQuasirandom (E_BC A) (Bpart B u v i) (Cpart B u v j) ε then 0
            else ((Bpart B u v i).card : ℝ) / (2 ^ (n - B.r) : ℝ) *
              ((Cpart B u v j).card : ℝ) / (2 ^ (n - B.r) : ℝ) * ε ^ 4) +
          (∑ i, ∑ k, if IsQuasirandom (E_BD A) (Bpart B u v i) (Dpart B u v k) ε then 0
            else ((Bpart B u v i).card : ℝ) / (2 ^ (n - B.r) : ℝ) *
              ((Dpart B u v k).card : ℝ) / (2 ^ (n - B.r) : ℝ) * ε ^ 4) +
          (∑ j, ∑ k, if IsQuasirandom (E_CD A) (Cpart B u v j) (Dpart B u v k) ε then 0
            else ((Cpart B u v j).card : ℝ) / (2 ^ (n - B.r) : ℝ) *
              ((Dpart B u v k).card : ℝ) / (2 ^ (n - B.r) : ℝ) * ε ^ 4) =
        (badWeightBC A B ε u v + badWeightBD A B ε u v + badWeightCD A B ε u v) * ε ^ 4 := by
      have f1 : ∀ i j,
          (if IsQuasirandom (E_BC A) (Bpart B u v i) (Cpart B u v j) ε then 0
            else ((Bpart B u v i).card : ℝ) / (2 ^ (n - B.r) : ℝ) *
              ((Cpart B u v j).card : ℝ) / (2 ^ (n - B.r) : ℝ) * ε ^ 4) =
          (if IsQuasirandom (E_BC A) (Bpart B u v i) (Cpart B u v j) ε then 0
            else pB B u v i * pC B u v j) * ε ^ 4 := fun i j => by
        split_ifs <;> [ring; (simp only [pB, pC]; ring)]
      have f2 : ∀ i k,
          (if IsQuasirandom (E_BD A) (Bpart B u v i) (Dpart B u v k) ε then 0
            else ((Bpart B u v i).card : ℝ) / (2 ^ (n - B.r) : ℝ) *
              ((Dpart B u v k).card : ℝ) / (2 ^ (n - B.r) : ℝ) * ε ^ 4) =
          (if IsQuasirandom (E_BD A) (Bpart B u v i) (Dpart B u v k) ε then 0
            else pB B u v i * pD B u v k) * ε ^ 4 := fun i k => by
        split_ifs <;> [ring; (simp only [pB, pD]; ring)]
      have f3 : ∀ j k,
          (if IsQuasirandom (E_CD A) (Cpart B u v j) (Dpart B u v k) ε then 0
            else ((Cpart B u v j).card : ℝ) / (2 ^ (n - B.r) : ℝ) *
              ((Dpart B u v k).card : ℝ) / (2 ^ (n - B.r) : ℝ) * ε ^ 4) =
          (if IsQuasirandom (E_CD A) (Cpart B u v j) (Dpart B u v k) ε then 0
            else pC B u v j * pD B u v k) * ε ^ 4 := fun j k => by
        split_ifs <;> [ring; (simp only [pC, pD]; ring)]
      simp_rw [f1, f2, f3, ← sum_mul]
      unfold badWeightBC badWeightBD badWeightCD
      ring
    have hBC_s : ∑ i, ∑ j, pB B u v i * pC B u v j *
          densBip (E_BC A) (Bpart B u v i) (Cpart B u v j) ^ 2 =
        ∑ i, ∑ j, ((Bpart B u v i).card : ℝ) / (2 ^ (n - B.r) : ℝ) *
          ((Cpart B u v j).card : ℝ) / (2 ^ (n - B.r) : ℝ) *
          densBip (E_BC A) (Bpart B u v i) (Cpart B u v j) ^ 2 := by
      refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => by simp only [pB, pC]; ring
    have hBD_s : ∑ i, ∑ k, pB B u v i * pD B u v k *
          densBip (E_BD A) (Bpart B u v i) (Dpart B u v k) ^ 2 =
        ∑ i, ∑ k, ((Bpart B u v i).card : ℝ) / (2 ^ (n - B.r) : ℝ) *
          ((Dpart B u v k).card : ℝ) / (2 ^ (n - B.r) : ℝ) *
          densBip (E_BD A) (Bpart B u v i) (Dpart B u v k) ^ 2 := by
      refine sum_congr rfl fun i _ => sum_congr rfl fun k _ => by simp only [pB, pD]; ring
    have hCD_s : ∑ j, ∑ k, pC B u v j * pD B u v k *
          densBip (E_CD A) (Cpart B u v j) (Dpart B u v k) ^ 2 =
        ∑ j, ∑ k, ((Cpart B u v j).card : ℝ) / (2 ^ (n - B.r) : ℝ) *
          ((Dpart B u v k).card : ℝ) / (2 ^ (n - B.r) : ℝ) *
          densBip (E_CD A) (Cpart B u v j) (Dpart B u v k) ^ 2 := by
      refine sum_congr rfl fun j _ => sum_congr rfl fun k _ => by simp only [pC, pD]; ring
    have hBC'_s : ∑ i', ∑ j', pB B' u v i' * pC B' u v j' *
          densBip (E_BC A) (Bpart B' u v i') (Cpart B' u v j') ^ 2 =
        ∑ i', ∑ j', ((Bpart B' u v i').card : ℝ) / (2 ^ (n - B.r) : ℝ) *
          ((Cpart B' u v j').card : ℝ) / (2 ^ (n - B.r) : ℝ) *
          densBip (E_BC A) (Bpart B' u v i') (Cpart B' u v j') ^ 2 := by
      refine sum_congr rfl fun i' _ => sum_congr rfl fun j' _ => by simp only [pB, pC, B']; ring
    have hBD'_s : ∑ i', ∑ k', pB B' u v i' * pD B' u v k' *
          densBip (E_BD A) (Bpart B' u v i') (Dpart B' u v k') ^ 2 =
        ∑ i', ∑ k', ((Bpart B' u v i').card : ℝ) / (2 ^ (n - B.r) : ℝ) *
          ((Dpart B' u v k').card : ℝ) / (2 ^ (n - B.r) : ℝ) *
          densBip (E_BD A) (Bpart B' u v i') (Dpart B' u v k') ^ 2 := by
      refine sum_congr rfl fun i' _ => sum_congr rfl fun k' _ => by simp only [pB, pD, B']; ring
    have hCD'_s : ∑ j', ∑ k', pC B' u v j' * pD B' u v k' *
          densBip (E_CD A) (Cpart B' u v j') (Dpart B' u v k') ^ 2 =
        ∑ j', ∑ k', ((Cpart B' u v j').card : ℝ) / (2 ^ (n - B.r) : ℝ) *
          ((Dpart B' u v k').card : ℝ) / (2 ^ (n - B.r) : ℝ) *
          densBip (E_CD A) (Cpart B' u v j') (Dpart B' u v k') ^ 2 := by
      refine sum_congr rfl fun j' _ => sum_congr rfl fun k' _ => by simp only [pC, pD, B']; ring
    rw [hBC_s, hBD_s, hCD_s, hBC'_s, hBD'_s, hCD'_s]
    have h123 := add_le_add (add_le_add hBC_sum hBD_sum) hCD_sum
    have hstep1 :
        (∑ i, ∑ j, ((Bpart B u v i).card : ℝ) / (2 ^ (n - B.r) : ℝ) *
            ((Cpart B u v j).card : ℝ) / (2 ^ (n - B.r) : ℝ) *
            densBip (E_BC A) (Bpart B u v i) (Cpart B u v j) ^ 2 +
          ∑ i, ∑ k, ((Bpart B u v i).card : ℝ) / (2 ^ (n - B.r) : ℝ) *
            ((Dpart B u v k).card : ℝ) / (2 ^ (n - B.r) : ℝ) *
            densBip (E_BD A) (Bpart B u v i) (Dpart B u v k) ^ 2 +
          ∑ j, ∑ k, ((Cpart B u v j).card : ℝ) / (2 ^ (n - B.r) : ℝ) *
            ((Dpart B u v k).card : ℝ) / (2 ^ (n - B.r) : ℝ) *
            densBip (E_CD A) (Cpart B u v j) (Dpart B u v k) ^ 2) +
        (badWeightBC A B ε u v + badWeightBD A B ε u v + badWeightCD A B ε u v) * ε ^ 4 ≤
        (∑ i' : Fin m', ∑ j' : Fin m', ((Bpart B' u v i').card : ℝ) / (2 ^ (n - B.r) : ℝ) *
            ((Cpart B' u v j').card : ℝ) / (2 ^ (n - B.r) : ℝ) *
            densBip (E_BC A) (Bpart B' u v i') (Cpart B' u v j') ^ 2 +
          ∑ i' : Fin m', ∑ k' : Fin m', ((Bpart B' u v i').card : ℝ) / (2 ^ (n - B.r) : ℝ) *
            ((Dpart B' u v k').card : ℝ) / (2 ^ (n - B.r) : ℝ) *
            densBip (E_BD A) (Bpart B' u v i') (Dpart B' u v k') ^ 2 +
          ∑ j' : Fin m', ∑ k' : Fin m', ((Cpart B' u v j').card : ℝ) / (2 ^ (n - B.r) : ℝ) *
            ((Dpart B' u v k').card : ℝ) / (2 ^ (n - B.r) : ℝ) *
            densBip (E_CD A) (Cpart B' u v j') (Dpart B' u v k') ^ 2) := by
      rw [← hrewrite]
      linarith [h123]
    have hsum3 := (add_le_add_right hbad_weight _).trans hstep1
    have hdiv3 := div_le_div_of_nonneg_right hsum3 (by norm_num : (0 : ℝ) ≤ 3)
    have hite3 : (if (u, v) ∈ bad2 then ε ^ 5 / 3 else 0) = (if (u, v) ∈ bad2 then ε ^ 5 else 0) / 3 := by
      split_ifs <;> ring
    rw [hite3]
    change _ / 3 + (if (u, v) ∈ bad2 then ε ^ 5 else 0) / 3 ≤
      (∑ i' : Fin m', ∑ j' : Fin m', ((Bpart B' u v i').card : ℝ) / (2 ^ (n - B.r) : ℝ) *
          ((Cpart B' u v j').card : ℝ) / (2 ^ (n - B.r) : ℝ) *
          densBip (E_BC A) (Bpart B' u v i') (Cpart B' u v j') ^ 2 +
        ∑ i' : Fin m', ∑ k' : Fin m', ((Bpart B' u v i').card : ℝ) / (2 ^ (n - B.r) : ℝ) *
          ((Dpart B' u v k').card : ℝ) / (2 ^ (n - B.r) : ℝ) *
          densBip (E_BD A) (Bpart B' u v i') (Dpart B' u v k') ^ 2 +
        ∑ j' : Fin m', ∑ k' : Fin m', ((Cpart B' u v j').card : ℝ) / (2 ^ (n - B.r) : ℝ) *
          ((Dpart B' u v k').card : ℝ) / (2 ^ (n - B.r) : ℝ) *
          densBip (E_CD A) (Cpart B' u v j') (Dpart B' u v k') ^ 2) / 3
    linarith [hdiv3]
  have hsum_box := sum_le_sum fun u (_ : u ∈ univ) => sum_le_sum fun v (_ : v ∈ univ) => hbox_E2 u v
  have hbad_sum : (∑ u : 𝔽₂ B.r, ∑ v : 𝔽₂ B.r, if (u, v) ∈ bad2 then ε ^ 5 / 3 else 0) =
      (bad2.card : ℝ) * (ε ^ 5 / 3) := by
    calc (∑ u : 𝔽₂ B.r, ∑ v : 𝔽₂ B.r, if (u, v) ∈ bad2 then ε ^ 5 / 3 else 0)
        = ∑ p : 𝔽₂ B.r × 𝔽₂ B.r, (if p ∈ bad2 then ε ^ 5 / 3 else 0) :=
          (Fintype.sum_prod_type (fun p : 𝔽₂ B.r × 𝔽₂ B.r =>
            if p ∈ bad2 then ε ^ 5 / 3 else 0)).symm
      _ = (bad2.card : ℝ) * (ε ^ 5 / 3) := by
          rw [← Finset.sum_filter]
          simp
  have h4pos : (0 : ℝ) < (4 ^ B.r : ℝ) := by positivity
  simp only [sum_add_distrib] at hsum_box
  rw [hbad_sum] at hsum_box
  have hinc : ε ^ 6 / 3 ≤ ((bad2.card : ℝ) * (ε ^ 5 / 3)) / (4 ^ B.r : ℝ) := by
    rw [le_div_iff₀ h4pos]
    calc ε ^ 6 / 3 * (4 ^ B.r : ℝ) = (ε * (4 ^ B.r : ℝ)) * (ε ^ 5 / 3) := by ring
      _ ≤ (bad2.card : ℝ) * (ε ^ 5 / 3) := mul_le_mul_of_nonneg_right hbad2_gt.le (by positivity)
  have hdiv := div_le_div_of_nonneg_right hsum_box h4pos.le
  rw [add_div] at hdiv
  refine ⟨B', rfl, hm'eq, ?_⟩
  unfold energyE2
  change _ / (4 ^ B.r : ℝ) + ε ^ 6 / 3 ≤
    (∑ u : 𝔽₂ B.r, ∑ v : 𝔽₂ B.r,
      (∑ i' : Fin m', ∑ j' : Fin m',
          pB B' u v i' * pC B' u v j' * densBip (E_BC A) (Bpart B' u v i') (Cpart B' u v j') ^ 2 +
        ∑ i' : Fin m', ∑ k' : Fin m',
          pB B' u v i' * pD B' u v k' * densBip (E_BD A) (Bpart B' u v i') (Dpart B' u v k') ^ 2 +
        ∑ j' : Fin m', ∑ k' : Fin m',
          pC B' u v j' * pD B' u v k' * densBip (E_CD A) (Cpart B' u v j') (Dpart B' u v k') ^ 2) / 3) /
      (4 ^ B.r : ℝ)
  linarith

private def stepR (r : ℕ) : ℕ := r + 4 ^ r

private def iterStepR : ℕ → ℕ → ℕ
  | 0, r => r
  | k + 1, r => iterStepR k (stepR r)

private lemma stepR_le_self (r : ℕ) : r ≤ stepR r := Nat.le_add_right r _

private lemma stepR_mono {r₁ r₂ : ℕ} (h : r₁ ≤ r₂) : stepR r₁ ≤ stepR r₂ := by
  unfold stepR
  exact Nat.add_le_add h (Nat.pow_le_pow_right (by norm_num) h)

private lemma iterStepR_mono {k r₁ r₂ : ℕ} (h : r₁ ≤ r₂) : iterStepR k r₁ ≤ iterStepR k r₂ := by
  induction k generalizing r₁ r₂ with
  | zero => exact h
  | succ k ih => exact ih (stepR_mono h)

private lemma le_iterStepR (k r : ℕ) : r ≤ iterStepR k r := by
  induction k generalizing r with
  | zero => exact le_rfl
  | succ k ih => exact le_trans (stepR_le_self r) (ih (stepR r))

private lemma inner_regularity_loop {n : ℕ} (A : Finset (𝔽₂ n × 𝔽₂ n))
    {ε : ℝ} (hε : 0 < ε) (m : ℕ) (_hm : 0 < m) :
    ∀ k : ℕ, ∀ B : Boxing n,
      B.m = m →
      1 - energyE1 B ≤ (k : ℝ) * (ε ^ 3 / (3 * (m : ℝ) ^ 6)) →
      ∃ B' : Boxing n,
        B'.m = m ∧
        Cond1 B' ε ∧
        energyE2 A B ≤ energyE2 A B' ∧
        B'.r ≤ iterStepR k B.r := by
  intro k
  induction k with
  | zero =>
      intro B hBm hE
      simp only [Nat.cast_zero, zero_mul] at hE
      have hcond1 : Cond1 B ε := by
        by_contra hfail
        obtain ⟨B', _, _, _, hinc⟩ := refinement_A A B hε hfail
        have hle := energyE1_le_one B'
        have hmpos : (0 : ℝ) < B.m := Nat.cast_pos.mpr B.hm
        have hpos : 0 < ε ^ 3 / (3 * (B.m : ℝ) ^ 6) := by positivity
        linarith
      exact ⟨B, hBm, hcond1, le_rfl, le_rfl⟩
  | succ k ih =>
      intro B hBm hE
      by_cases hcond1 : Cond1 B ε
      · exact ⟨B, hBm, hcond1, le_rfl, le_iterStepR (k + 1) B.r⟩
      · obtain ⟨B₁, hB₁m, hB₁r, hE2, hE1⟩ := refinement_A A B hε hcond1
        have hB₁m' : B₁.m = m := hB₁m.trans hBm
        have hE' : 1 - energyE1 B₁ ≤ (k : ℝ) * (ε ^ 3 / (3 * (m : ℝ) ^ 6)) := by
          rw [hBm] at hE1
          push_cast at hE
          linarith
        obtain ⟨B', hB'm, hB'c1, hB'E2, hB'r⟩ := ih B₁ hB₁m' hE'
        refine ⟨B', hB'm, hB'c1, le_trans hE2 hB'E2, ?_⟩
        calc B'.r ≤ iterStepR k B₁.r := hB'r
          _ ≤ iterStepR k (stepR B.r) := iterStepR_mono hB₁r
          _ = iterStepR (k + 1) B.r := rfl

private noncomputable def K1 (ε : ℝ) (m : ℕ) : ℕ :=
  Nat.floor (3 * (m : ℝ) ^ 6 / ε ^ 3) + 1

private lemma K1_bound {ε : ℝ} (hε : 0 < ε) (m : ℕ) (hm : 0 < m) (x : ℝ) (hx : 0 ≤ x) :
    1 - x ≤ (K1 ε m : ℝ) * (ε ^ 3 / (3 * (m : ℝ) ^ 6)) := by
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hden : 0 < ε ^ 3 / (3 * (m : ℝ) ^ 6) := by positivity
  have hfl := Nat.lt_floor_add_one (3 * (m : ℝ) ^ 6 / ε ^ 3)
  have h1 : 1 ≤ (K1 ε m : ℝ) * (ε ^ 3 / (3 * (m : ℝ) ^ 6)) := by
    unfold K1
    push_cast
    calc 1 = (3 * (m : ℝ) ^ 6 / ε ^ 3) * (ε ^ 3 / (3 * (m : ℝ) ^ 6)) := by
            field_simp [hε.ne', hmpos.ne']
      _ ≤ ((Nat.floor (3 * (m : ℝ) ^ 6 / ε ^ 3) : ℝ) + 1) * (ε ^ 3 / (3 * (m : ℝ) ^ 6)) :=
            mul_le_mul_of_nonneg_right hfl.le hden.le
  linarith

private def boundM : ℕ → ℕ → ℕ
  | 0, m => m
  | k + 1, m => boundM k (m * 4 ^ m)

private noncomputable def boundR (ε : ℝ) : ℕ → ℕ → ℕ → ℕ
  | 0, r, m => iterStepR (K1 ε m) r
  | k + 1, r, m => boundR ε k (iterStepR (K1 ε m) r) (m * 4 ^ m)

private lemma boundM_mono_k (k m : ℕ) (hm : 0 < m) : m ≤ boundM (k + 1) m := by
  induction k generalizing m with
  | zero => exact Nat.le_mul_of_pos_right m (pow_pos (by norm_num) _)
  | succ k ih =>
      calc m ≤ m * 4 ^ m := Nat.le_mul_of_pos_right m (pow_pos (by norm_num) _)
        _ ≤ boundM (k + 1) (m * 4 ^ m) := ih (m * 4 ^ m) (Nat.mul_pos hm (pow_pos (by norm_num) _))

private lemma le_boundM (k m : ℕ) (hm : 0 < m) : m ≤ boundM k m := by
  cases k with
  | zero => exact le_rfl
  | succ k => exact boundM_mono_k k m hm

private lemma iterStepR_le_boundR (ε : ℝ) (k r m : ℕ) :
    iterStepR (K1 ε m) r ≤ boundR ε k r m := by
  induction k generalizing r m with
  | zero => exact le_rfl
  | succ k ih =>
      calc iterStepR (K1 ε m) r
          ≤ iterStepR (K1 ε (m * 4 ^ m)) (iterStepR (K1 ε m) r) :=
            le_iterStepR (K1 ε (m * 4 ^ m)) _
        _ ≤ boundR ε k (iterStepR (K1 ε m) r) (m * 4 ^ m) :=
            ih (iterStepR (K1 ε m) r) (m * 4 ^ m)

private lemma boundR_mono (ε : ℝ) : ∀ (j m r₁ r₂ : ℕ), r₁ ≤ r₂ →
    boundR ε j r₁ m ≤ boundR ε j r₂ m := by
  intro j
  induction j with
  | zero => intro m r₁ r₂ hr; exact iterStepR_mono hr
  | succ j ih => intro m r₁ r₂ hr; exact ih (m * 4 ^ m) _ _ (iterStepR_mono hr)

private lemma outer_regularity_loop {n : ℕ} (A : Finset (𝔽₂ n × 𝔽₂ n))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ k : ℕ, ∀ B : Boxing n,
      1 - energyE2 A B ≤ (k : ℝ) * (ε ^ 6 / 3) →
      ∃ B' : Boxing n,
        Cond1 B' ε ∧
        Cond2 A B' ε ∧
        B'.r ≤ boundR ε k B.r B.m ∧
        B'.m ≤ boundM k B.m := by
  intro k
  induction k with
  | zero =>
      intro B hE2
      simp only [Nat.cast_zero, zero_mul] at hE2
      obtain ⟨B₁, hB₁m, hB₁c1, hB₁E2, hB₁r⟩ :=
        inner_regularity_loop A hε B.m B.hm (K1 ε B.m) B rfl
          (K1_bound hε B.m B.hm (energyE1 B) (energyE1_nonneg B))
      have hcond2 : Cond2 A B₁ ε := by
        by_contra hfail
        obtain ⟨B₂, _, _, hinc⟩ := refinement_B A B₁ hε hfail
        have hle := energyE2_le_one A B₂
        have hpos : 0 < ε ^ 6 / 3 := by positivity
        linarith
      refine ⟨B₁, hB₁c1, hcond2, hB₁r, ?_⟩
      rw [hB₁m]; exact le_rfl
  | succ k ih =>
      intro B hE2
      obtain ⟨B₁, hB₁m, hB₁c1, hB₁E2, hB₁r⟩ :=
        inner_regularity_loop A hε B.m B.hm (K1 ε B.m) B rfl
          (K1_bound hε B.m B.hm (energyE1 B) (energyE1_nonneg B))
      by_cases hcond2 : Cond2 A B₁ ε
      · refine ⟨B₁, hB₁c1, hcond2, ?_, ?_⟩
        · exact le_trans hB₁r (iterStepR_le_boundR ε (k + 1) B.r B.m)
        · rw [hB₁m]; exact le_boundM (k + 1) B.m B.hm
      · obtain ⟨B₂, hB₂r, hB₂m, hinc⟩ := refinement_B A B₁ hε hcond2
        have hE2' : 1 - energyE2 A B₂ ≤ (k : ℝ) * (ε ^ 6 / 3) := by
          push_cast at hE2
          linarith
        obtain ⟨B', hB'c1, hB'c2, hB'r, hB'm⟩ := ih B₂ hE2'
        refine ⟨B', hB'c1, hB'c2, ?_, ?_⟩
        · have hr1 : B₂.r ≤ iterStepR (K1 ε B.m) B.r := by rw [hB₂r]; exact hB₁r
          have hm1 : B₂.m = B.m * 4 ^ B.m := by rw [hB₂m, hB₁m]
          calc B'.r ≤ boundR ε k B₂.r B₂.m := hB'r
            _ = boundR ε k B₂.r (B.m * 4 ^ B.m) := by rw [hm1]
            _ ≤ boundR ε k (iterStepR (K1 ε B.m) B.r) (B.m * 4 ^ B.m) :=
                boundR_mono ε k (B.m * 4 ^ B.m) _ _ hr1
            _ = boundR ε (k + 1) B.r B.m := rfl
        · have hm1 : B₂.m = B.m * 4 ^ B.m := by rw [hB₂m, hB₁m]
          rw [hm1] at hB'm
          exact hB'm

private lemma regularity_lemma {ε : ℝ} (hε : 0 < ε) :
    ∃ R_max : ℕ, ∀ (n : ℕ) (A : Finset (𝔽₂ n × 𝔽₂ n)),
      ∃ B : Boxing n, Cond1 B ε ∧ Cond2 A B ε ∧ B.r ≤ R_max := by
  let k₂ : ℕ := Nat.floor (3 / ε ^ 6) + 1
  refine ⟨boundR ε k₂ 0 1, fun n A => ?_⟩
  have hk₂ : 1 - energyE2 A (initialBoxing n) ≤ (k₂ : ℝ) * (ε ^ 6 / 3) := by
    have hfl := Nat.lt_floor_add_one (3 / ε ^ 6)
    have hden : 0 < ε ^ 6 / 3 := by positivity
    have h1 : 1 ≤ (k₂ : ℝ) * (ε ^ 6 / 3) := by
      dsimp only [k₂]
      push_cast
      calc 1 = (3 / ε ^ 6) * (ε ^ 6 / 3) := by field_simp [hε.ne']
        _ ≤ ((Nat.floor (3 / ε ^ 6) : ℝ) + 1) * (ε ^ 6 / 3) :=
            mul_le_mul_of_nonneg_right hfl.le hden.le
    linarith [energyE2_nonneg A (initialBoxing n)]
  obtain ⟨B, hc1, hc2, hr, _⟩ := outer_regularity_loop A hε k₂ (initialBoxing n) hk₂
  exact ⟨B, hc1, hc2, hr⟩

end QuasirandomAndBoxing

/-
## Section 4: Triangle Counting, Popular Corners, and Main Theorems
-/

section TriangleCountingAndMain

private lemma qr_rect_sum_bound {α β : Type*} [DecidableEq α] [DecidableEq β]
    (E : Finset (α × β)) (B : Finset α) (C : Finset β) {ε : ℝ} (hε : 0 ≤ ε)
    (hqr : IsQuasirandom E B C ε) {B' : Finset α} {C' : Finset β}
    (hB' : B' ⊆ B) (hC' : C' ⊆ C) :
    |∑ x ∈ B', ∑ y ∈ C', ((if (x, y) ∈ E then (1 : ℝ) else 0) - densBip E B C)| ≤
      ε * (B.card : ℝ) * (C.card : ℝ) := by
  have hsum_id :
      ∑ x ∈ B', ∑ y ∈ C', ((if (x, y) ∈ E then (1 : ℝ) else 0) - densBip E B C) =
        (B'.card : ℝ) * (C'.card : ℝ) * (densBip E B' C' - densBip E B C) := by
    have h1 : ∑ x ∈ B', ∑ y ∈ C', (if (x, y) ∈ E then (1 : ℝ) else 0) =
        ((E ∩ (B' ×ˢ C')).card : ℝ) := by
      rw [← sum_product']
      have hfil : E ∩ (B' ×ˢ C') = (B' ×ˢ C').filter (fun p => p ∈ E) := by
        ext p; simp [and_comm]
      rw [hfil, card_filter, Nat.cast_sum]
      refine sum_congr rfl fun p _ => ?_
      by_cases hp : p ∈ E
      · simp [hp]
      · simp [hp]
    have h2 : ∑ x ∈ B', ∑ y ∈ C', densBip E B C =
        (B'.card : ℝ) * (C'.card : ℝ) * densBip E B C := by
      simp [mul_assoc]
    simp only [sum_sub_distrib, h1, h2, ← card_mul_densBip]
    ring
  rw [hsum_id, abs_mul, abs_mul, Nat.abs_cast, Nat.abs_cast]
  have hB'le : (B'.card : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast card_le_card hB'
  have hC'le : (C'.card : ℝ) ≤ (C.card : ℝ) := by exact_mod_cast card_le_card hC'
  by_cases hcond : ε * (B.card : ℝ) ≤ (B'.card : ℝ) ∧ ε * (C.card : ℝ) ≤ (C'.card : ℝ)
  · have hdiff := hqr B' hB' C' hC' hcond.1 hcond.2
    calc (B'.card : ℝ) * (C'.card : ℝ) * |densBip E B' C' - densBip E B C|
        ≤ (B.card : ℝ) * (C.card : ℝ) * ε :=
          mul_le_mul (mul_le_mul hB'le hC'le (by positivity) (by positivity))
            hdiff (abs_nonneg _) (by positivity)
      _ = ε * (B.card : ℝ) * (C.card : ℝ) := by ring
  · have hdiff1 : |densBip E B' C' - densBip E B C| ≤ 1 := by
      rw [abs_le]
      have a0 := densBip_nonneg E B' C'
      have a1 := densBip_le_one E B' C'
      have b0 := densBip_nonneg E B C
      have b1 := densBip_le_one E B C
      constructor <;> linarith
    have hprod : (B'.card : ℝ) * (C'.card : ℝ) ≤ ε * (B.card : ℝ) * (C.card : ℝ) := by
      rw [not_and_or] at hcond
      rcases hcond with hB_lt | hC_lt
      · have h1 := (not_le.mp hB_lt).le
        calc (B'.card : ℝ) * (C'.card : ℝ)
            ≤ (ε * (B.card : ℝ)) * (C.card : ℝ) :=
              mul_le_mul h1 hC'le (by positivity) (by positivity)
          _ = ε * (B.card : ℝ) * (C.card : ℝ) := by ring
      · have h2 := (not_le.mp hC_lt).le
        calc (B'.card : ℝ) * (C'.card : ℝ)
            ≤ (B.card : ℝ) * (ε * (C.card : ℝ)) :=
              mul_le_mul hB'le h2 (by positivity) (by positivity)
          _ = ε * (B.card : ℝ) * (C.card : ℝ) := by ring
    calc (B'.card : ℝ) * (C'.card : ℝ) * |densBip E B' C' - densBip E B C|
        ≤ (B'.card : ℝ) * (C'.card : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hdiff1 (by positivity)
      _ = (B'.card : ℝ) * (C'.card : ℝ) := mul_one _
      _ ≤ ε * (B.card : ℝ) * (C.card : ℝ) := hprod

private lemma triangle_counting_lemma {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (B : Finset α) (C : Finset β) (D : Finset γ)
    (E_BC : Finset (α × β)) (E_BD : Finset (α × γ)) (E_CD : Finset (β × γ))
    {ε : ℝ} (hε : 0 ≤ ε)
    (hBC : IsQuasirandom E_BC B C ε)
    (hBD : IsQuasirandom E_BD B D ε)
    (_hCD : IsQuasirandom E_CD C D ε) :
    |(((B ×ˢ (C ×ˢ D)).filter (fun p =>
        (p.1, p.2.1) ∈ E_BC ∧ (p.1, p.2.2) ∈ E_BD ∧ (p.2.1, p.2.2) ∈ E_CD)).card : ℝ) -
      densBip E_BC B C * densBip E_BD B D * densBip E_CD C D *
        (B.card : ℝ) * (C.card : ℝ) * (D.card : ℝ)| ≤
      2 * ε * (B.card : ℝ) * (C.card : ℝ) * (D.card : ℝ) := by
  classical
  let fBC : α → β → ℝ := fun x y => if (x, y) ∈ E_BC then 1 else 0
  let fBD : α → γ → ℝ := fun x z => if (x, z) ∈ E_BD then 1 else 0
  let fCD : β → γ → ℝ := fun y z => if (y, z) ∈ E_CD then 1 else 0
  let δBC := densBip E_BC B C
  let δBD := densBip E_BD B D
  let δCD := densBip E_CD C D
  have htri_eq :
      (((B ×ˢ (C ×ˢ D)).filter (fun p =>
          (p.1, p.2.1) ∈ E_BC ∧ (p.1, p.2.2) ∈ E_BD ∧ (p.2.1, p.2.2) ∈ E_CD)).card : ℝ) =
        ∑ x ∈ B, ∑ y ∈ C, ∑ z ∈ D, fBC x y * fBD x z * fCD y z := by
    rw [card_filter, Nat.cast_sum, sum_product]
    refine sum_congr rfl fun x _ => ?_
    rw [sum_product]
    refine sum_congr rfl fun y _ => sum_congr rfl fun z _ => ?_
    by_cases h1 : (x, y) ∈ E_BC <;> by_cases h2 : (x, z) ∈ E_BD <;>
      by_cases h3 : (y, z) ∈ E_CD <;> simp [fBC, fBD, fCD, h1, h2, h3]
  have hprod_eq :
      δBC * δBD * δCD * (B.card : ℝ) * (C.card : ℝ) * (D.card : ℝ) =
        ∑ x ∈ B, ∑ y ∈ C, ∑ z ∈ D, δBC * δBD * δCD := by
    simp [mul_assoc, mul_left_comm, mul_comm]
  have hdiff_split :
      (∑ x ∈ B, ∑ y ∈ C, ∑ z ∈ D, fBC x y * fBD x z * fCD y z) -
        (∑ x ∈ B, ∑ y ∈ C, ∑ z ∈ D, δBC * δBD * δCD) =
      (∑ z ∈ D, ∑ x ∈ B.filter (fun x => (x, z) ∈ E_BD),
        ∑ y ∈ C.filter (fun y => (y, z) ∈ E_CD), (fBC x y - δBC)) +
      δBC * (∑ y ∈ C, ∑ x ∈ B, ∑ z ∈ D.filter (fun z => (y, z) ∈ E_CD), (fBD x z - δBD)) +
      δBC * δBD * (B.card : ℝ) * (∑ y ∈ C, ∑ z ∈ D, (fCD y z - δCD)) := by
    have hpt : ∀ x y z,
        fBC x y * fBD x z * fCD y z - δBC * δBD * δCD =
          (fBC x y - δBC) * fBD x z * fCD y z +
          δBC * ((fBD x z - δBD) * fCD y z) +
          δBC * δBD * (fCD y z - δCD) := fun x y z => by ring
    simp_rw [← sum_sub_distrib, hpt, sum_add_distrib]
    have h1 :
        (∑ x ∈ B, ∑ y ∈ C, ∑ z ∈ D, (fBC x y - δBC) * fBD x z * fCD y z) =
          ∑ z ∈ D, ∑ x ∈ B.filter (fun x => (x, z) ∈ E_BD),
            ∑ y ∈ C.filter (fun y => (y, z) ∈ E_CD), (fBC x y - δBC) := by
      calc ∑ x ∈ B, ∑ y ∈ C, ∑ z ∈ D, (fBC x y - δBC) * fBD x z * fCD y z
          = ∑ x ∈ B, ∑ z ∈ D, ∑ y ∈ C, (fBC x y - δBC) * fBD x z * fCD y z :=
              sum_congr rfl fun x _ => sum_comm
        _ = ∑ z ∈ D, ∑ x ∈ B, ∑ y ∈ C, (fBC x y - δBC) * fBD x z * fCD y z := sum_comm
        _ = ∑ z ∈ D, ∑ x ∈ B.filter (fun x => (x, z) ∈ E_BD),
              ∑ y ∈ C.filter (fun y => (y, z) ∈ E_CD), (fBC x y - δBC) := by
            refine sum_congr rfl fun z _ => ?_
            simp_rw [sum_filter]
            refine sum_congr rfl fun x _ => ?_
            by_cases hxz : (x, z) ∈ E_BD
            · simp only [hxz, ↓reduceIte, fBD, mul_one]
              refine sum_congr rfl fun y _ => ?_
              by_cases hyz : (y, z) ∈ E_CD <;> simp [hyz, fCD]
            · simp [hxz, fBD]
    have h2 :
        (∑ x ∈ B, ∑ y ∈ C, ∑ z ∈ D, δBC * ((fBD x z - δBD) * fCD y z)) =
          δBC * ∑ y ∈ C, ∑ x ∈ B, ∑ z ∈ D.filter (fun z => (y, z) ∈ E_CD), (fBD x z - δBD) := by
      calc ∑ x ∈ B, ∑ y ∈ C, ∑ z ∈ D, δBC * ((fBD x z - δBD) * fCD y z)
          = ∑ y ∈ C, ∑ x ∈ B, ∑ z ∈ D, δBC * ((fBD x z - δBD) * fCD y z) := sum_comm
        _ = δBC * ∑ y ∈ C, ∑ x ∈ B, ∑ z ∈ D, (fBD x z - δBD) * fCD y z := by
            rw [mul_sum]; refine sum_congr rfl fun y _ => ?_
            rw [mul_sum]; refine sum_congr rfl fun x _ => ?_; rw [mul_sum]
        _ = δBC * ∑ y ∈ C, ∑ x ∈ B, ∑ z ∈ D.filter (fun z => (y, z) ∈ E_CD), (fBD x z - δBD) := by
            congr 1; refine sum_congr rfl fun y _ => sum_congr rfl fun x _ => ?_
            rw [sum_filter]
            refine sum_congr rfl fun z _ => ?_
            by_cases hyz : (y, z) ∈ E_CD <;> simp [hyz, fCD]
    have h3 :
        (∑ x ∈ B, ∑ y ∈ C, ∑ z ∈ D, δBC * δBD * (fCD y z - δCD)) =
          δBC * δBD * (B.card : ℝ) * ∑ y ∈ C, ∑ z ∈ D, (fCD y z - δCD) := by
      calc ∑ x ∈ B, ∑ y ∈ C, ∑ z ∈ D, δBC * δBD * (fCD y z - δCD)
          = ∑ _x ∈ B, (δBC * δBD * ∑ y ∈ C, ∑ z ∈ D, (fCD y z - δCD)) := by
              refine sum_congr rfl fun x _ => ?_
              rw [mul_sum]; refine sum_congr rfl fun y _ => ?_; rw [mul_sum]
        _ = (B.card : ℝ) * (δBC * δBD * ∑ y ∈ C, ∑ z ∈ D, (fCD y z - δCD)) := by simp
        _ = δBC * δBD * (B.card : ℝ) * ∑ y ∈ C, ∑ z ∈ D, (fCD y z - δCD) := by ring
    rw [h1, h2, h3]
  have hterm3 : (∑ y ∈ C, ∑ z ∈ D, (fCD y z - δCD)) = 0 := by
    have hsum1 : ∑ y ∈ C, ∑ z ∈ D, fCD y z = ((E_CD ∩ (C ×ˢ D)).card : ℝ) := by
      have hfil : E_CD ∩ (C ×ˢ D) = (C ×ˢ D).filter (fun p => p ∈ E_CD) := by
        ext p; simp [and_comm]
      rw [← sum_product', hfil, card_filter, Nat.cast_sum]
      refine sum_congr rfl fun p _ => ?_
      by_cases hp : p ∈ E_CD <;> simp [fCD, hp]
    have hsum2 : ∑ y ∈ C, ∑ z ∈ D, δCD = (C.card : ℝ) * (D.card : ℝ) * δCD := by
      simp [mul_assoc]
    simp_rw [sum_sub_distrib]
    rw [hsum1, hsum2, ← card_mul_densBip]
    ring
  have hterm1 :
      |∑ z ∈ D, ∑ x ∈ B.filter (fun x => (x, z) ∈ E_BD),
          ∑ y ∈ C.filter (fun y => (y, z) ∈ E_CD), (fBC x y - δBC)| ≤
        ε * (B.card : ℝ) * (C.card : ℝ) * (D.card : ℝ) := by
    calc |∑ z ∈ D, ∑ x ∈ B.filter (fun x => (x, z) ∈ E_BD),
            ∑ y ∈ C.filter (fun y => (y, z) ∈ E_CD), (fBC x y - δBC)|
        ≤ ∑ z ∈ D, |∑ x ∈ B.filter (fun x => (x, z) ∈ E_BD),
            ∑ y ∈ C.filter (fun y => (y, z) ∈ E_CD), (fBC x y - δBC)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _z ∈ D, ε * (B.card : ℝ) * (C.card : ℝ) :=
          sum_le_sum fun z _ => qr_rect_sum_bound E_BC B C hε hBC
            (filter_subset _ _) (filter_subset _ _)
      _ = ε * (B.card : ℝ) * (C.card : ℝ) * (D.card : ℝ) := by simp; ring
  have hterm2 :
      |δBC * ∑ y ∈ C, ∑ x ∈ B, ∑ z ∈ D.filter (fun z => (y, z) ∈ E_CD), (fBD x z - δBD)| ≤
        ε * (B.card : ℝ) * (C.card : ℝ) * (D.card : ℝ) := by
    rw [abs_mul]
    have hδ0 : 0 ≤ δBC := densBip_nonneg E_BC B C
    have hδ1 : δBC ≤ 1 := densBip_le_one E_BC B C
    have hinner :
        |∑ y ∈ C, ∑ x ∈ B, ∑ z ∈ D.filter (fun z => (y, z) ∈ E_CD), (fBD x z - δBD)| ≤
          ε * (B.card : ℝ) * (C.card : ℝ) * (D.card : ℝ) := by
      calc |∑ y ∈ C, ∑ x ∈ B, ∑ z ∈ D.filter (fun z => (y, z) ∈ E_CD), (fBD x z - δBD)|
          ≤ ∑ y ∈ C, |∑ x ∈ B, ∑ z ∈ D.filter (fun z => (y, z) ∈ E_CD), (fBD x z - δBD)| :=
              abs_sum_le_sum_abs _ _
        _ ≤ ∑ _y ∈ C, ε * (B.card : ℝ) * (D.card : ℝ) :=
            sum_le_sum fun y _ => qr_rect_sum_bound E_BD B D hε hBD
              (Subset.refl _) (filter_subset _ _)
        _ = ε * (B.card : ℝ) * (C.card : ℝ) * (D.card : ℝ) := by simp; ring
    calc |δBC| * |∑ y ∈ C, ∑ x ∈ B, ∑ z ∈ D.filter (fun z => (y, z) ∈ E_CD), (fBD x z - δBD)|
        = δBC * |∑ y ∈ C, ∑ x ∈ B, ∑ z ∈ D.filter (fun z => (y, z) ∈ E_CD), (fBD x z - δBD)| := by
            rw [abs_of_nonneg hδ0]
      _ ≤ 1 * (ε * (B.card : ℝ) * (C.card : ℝ) * (D.card : ℝ)) :=
            mul_le_mul hδ1 hinner (abs_nonneg _) (by positivity)
      _ = ε * (B.card : ℝ) * (C.card : ℝ) * (D.card : ℝ) := one_mul _
  rw [htri_eq, hprod_eq, hdiff_split, hterm3, mul_zero, add_zero]
  exact (abs_add_le _ _).trans (by linarith)

private lemma sum_fin_triple_prod {m : ℕ} (g : Fin m × Fin m × Fin m → ℕ) :
    (∑ i : Fin m, ∑ j : Fin m, ∑ k : Fin m, g (i, j, k)) =
      ∑ t : Fin m × Fin m × Fin m, g t := by
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]

private lemma sum_corners_ker_eq {n : ℕ} (A : Finset (𝔽₂ n × 𝔽₂ n)) (B : Boxing n) :
    (∑ d ∈ fiber B.proj 0, (S d A).card : ℕ) =
      ∑ u : 𝔽₂ B.r, ∑ v : 𝔽₂ B.r,
        ∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
          ((Bpart B u v i ×ˢ (Cpart B u v j ×ˢ Dpart B u v k)).filter (fun p =>
            (p.1, p.2.1) ∈ E_BC A ∧ (p.1, p.2.2) ∈ E_BD A ∧ (p.2.1, p.2.2) ∈ E_CD A)).card := by
  classical
  let pred : 𝔽₂ n × (𝔽₂ n × 𝔽₂ n) → Prop := fun p =>
    (p.1, p.2.1) ∈ E_BC A ∧ (p.1, p.2.2) ∈ E_BD A ∧ (p.2.1, p.2.2) ∈ E_CD A
  have hinner : ∀ u v : 𝔽₂ B.r,
      (∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
        ((Bpart B u v i ×ˢ (Cpart B u v j ×ˢ Dpart B u v k)).filter pred).card) =
      ((fiber B.proj u ×ˢ (fiber B.proj v ×ˢ fiber B.proj (u + v))).filter pred).card := by
    intro u v
    let parts := fun t : Fin B.m × Fin B.m × Fin B.m =>
      (Bpart B u v t.1 ×ˢ (Cpart B u v t.2.1 ×ˢ Dpart B u v t.2.2)).filter pred
    have hdisj : ((univ : Finset (Fin B.m × Fin B.m × Fin B.m)) :
        Set (Fin B.m × Fin B.m × Fin B.m)).PairwiseDisjoint parts := by
      intro t₁ _ t₂ _ hne
      refine Finset.disjoint_left.mpr ?_
      rintro ⟨x, y, z⟩ h₁ h₂
      simp only [parts, mem_filter, mem_product, Bpart, Cpart, Dpart] at h₁ h₂
      by_cases h1 : t₁.1 = t₂.1
      · by_cases h2 : t₁.2.1 = t₂.2.1
        · exact hne (Prod.ext h1 (Prod.ext h2 (h₁.1.2.2.2.symm.trans h₂.1.2.2.2)))
        · exact h2 (h₁.1.2.1.2.symm.trans h₂.1.2.1.2)
      · exact h1 (h₁.1.1.2.symm.trans h₂.1.1.2)
    have hcov : (univ : Finset (Fin B.m × Fin B.m × Fin B.m)).biUnion parts =
        (fiber B.proj u ×ˢ (fiber B.proj v ×ˢ fiber B.proj (u + v))).filter pred := by
      ext ⟨x, y, z⟩
      simp only [parts, mem_biUnion, mem_univ, true_and, mem_filter, mem_product,
        Bpart, Cpart, Dpart]
      constructor
      · rintro ⟨⟨i, j, k⟩, ⟨⟨hx, _⟩, ⟨hy, _⟩, ⟨hz, _⟩⟩, hp⟩
        exact ⟨⟨hx, hy, hz⟩, hp⟩
      · rintro ⟨⟨hx, hy, hz⟩, hp⟩
        exact ⟨(B.bCol u v x, B.cCol u v y, B.dCol u v z),
          ⟨⟨hx, rfl⟩, ⟨hy, rfl⟩, ⟨hz, rfl⟩⟩, hp⟩
    have hsum_eq :
        (∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
          ((Bpart B u v i ×ˢ (Cpart B u v j ×ˢ Dpart B u v k)).filter pred).card) =
        ∑ t : Fin B.m × Fin B.m × Fin B.m, (parts t).card :=
      sum_fin_triple_prod (fun t => (parts t).card)
    rw [hsum_eq, ← card_biUnion hdisj, hcov]
  dsimp only [pred] at hinner
  simp_rw [hinner]
  have houter :
      (∑ u : 𝔽₂ B.r, ∑ v : 𝔽₂ B.r,
        ((fiber B.proj u ×ˢ (fiber B.proj v ×ˢ fiber B.proj (u + v))).filter pred).card) =
      ((univ : Finset (𝔽₂ n × (𝔽₂ n × 𝔽₂ n))).filter (fun p =>
        B.proj (p.1 + p.2.1 + p.2.2) = 0 ∧ pred p)).card := by
    let parts := fun uv : 𝔽₂ B.r × 𝔽₂ B.r =>
      (fiber B.proj uv.1 ×ˢ (fiber B.proj uv.2 ×ˢ fiber B.proj (uv.1 + uv.2))).filter pred
    have hdisj : ((univ : Finset (𝔽₂ B.r × 𝔽₂ B.r)) : Set (𝔽₂ B.r × 𝔽₂ B.r)).PairwiseDisjoint parts := by
      intro uv₁ _ uv₂ _ hne
      refine Finset.disjoint_left.mpr ?_
      rintro ⟨x, y, z⟩ h₁ h₂
      simp only [parts, mem_filter, mem_product, mem_fiber] at h₁ h₂
      exact hne (Prod.ext (h₁.1.1.symm.trans h₂.1.1) (h₁.1.2.1.symm.trans h₂.1.2.1))
    have hcov : (univ : Finset (𝔽₂ B.r × 𝔽₂ B.r)).biUnion parts =
        (univ : Finset (𝔽₂ n × (𝔽₂ n × 𝔽₂ n))).filter (fun p =>
          B.proj (p.1 + p.2.1 + p.2.2) = 0 ∧ pred p) := by
      ext ⟨x, y, z⟩
      simp only [parts, mem_biUnion, mem_univ, true_and, mem_filter, mem_product, mem_fiber]
      constructor
      · rintro ⟨⟨u, v⟩, ⟨hx, hy, hz⟩, hp⟩
        refine ⟨?_, hp⟩
        rw [map_add, map_add, hx, hy, hz, f2_add_self]
      · rintro ⟨hzero, hp⟩
        refine ⟨(B.proj x, B.proj y), ⟨rfl, rfl, ?_⟩, hp⟩
        rw [map_add, map_add] at hzero
        calc B.proj z = (B.proj x + B.proj y) + (B.proj x + B.proj y + B.proj z) := by
              rw [← add_assoc, f2_add_self, zero_add]
          _ = B.proj x + B.proj y := by rw [hzero, add_zero]
    calc (∑ u : 𝔽₂ B.r, ∑ v : 𝔽₂ B.r,
            ((fiber B.proj u ×ˢ (fiber B.proj v ×ˢ fiber B.proj (u + v))).filter pred).card)
        = ∑ uv : 𝔽₂ B.r × 𝔽₂ B.r, (parts uv).card :=
          (Fintype.sum_prod_type (fun uv : 𝔽₂ B.r × 𝔽₂ B.r => (parts uv).card)).symm
      _ = _ := by rw [← card_biUnion hdisj, hcov]
  rw [houter]
  have hlhs : (∑ d ∈ fiber B.proj 0, (S d A).card) =
      (((fiber B.proj 0) ×ˢ (univ : Finset (𝔽₂ n × 𝔽₂ n))).filter
        (fun q => IsCorner A q.2.1 q.2.2 q.1)).card := by
    calc (∑ d ∈ fiber B.proj 0, (S d A).card)
        = ∑ d ∈ fiber B.proj 0,
            ∑ p ∈ (univ : Finset (𝔽₂ n × 𝔽₂ n)), if IsCorner A p.1 p.2 d then 1 else 0 := by
            refine sum_congr rfl fun d _ => ?_
            simp only [S]
            exact Finset.card_filter _ _
      _ = ∑ q ∈ (fiber B.proj 0) ×ˢ (univ : Finset (𝔽₂ n × 𝔽₂ n)),
            if IsCorner A q.2.1 q.2.2 q.1 then 1 else 0 := (sum_product' _ _ _).symm
      _ = _ := (Finset.card_filter _ _).symm
  rw [hlhs]
  refine Finset.card_bij (fun q _ => (q.2.1, (q.2.2, q.2.1 + q.2.2 + q.1))) ?_ ?_ ?_
  · rintro ⟨d, x, y⟩ hq
    rw [mem_filter, mem_product, mem_fiber] at hq
    simp only [mem_filter, mem_univ, true_and, pred, E_BC, E_BD, E_CD]
    simp only [mem_univ, and_true, IsCorner] at hq
    rcases hq with ⟨hd, hxy, hxd, hyd⟩
    refine ⟨?_, hxy, ?_, ?_⟩
    · rw [map_add, map_add]
      calc B.proj x + B.proj y + B.proj (x + y + d)
          = B.proj x + B.proj y + (B.proj x + B.proj y + B.proj d) := by rw [map_add, map_add]
        _ = (B.proj x + B.proj y) + (B.proj x + B.proj y) + B.proj d := by abel
        _ = 0 := by rw [f2_add_self, zero_add, hd]
    · have hid : x + (x + y + d) = y + d := by
        calc x + (x + y + d) = (x + x) + (y + d) := by abel
          _ = y + d := by rw [f2_add_self, zero_add]
      simpa [hid] using hyd
    · have hid : y + (x + y + d) = x + d := by
        calc y + (x + y + d) = x + (y + y) + d := by abel
          _ = x + d := by rw [f2_add_self, add_zero]
      simpa [hid] using hxd
  · rintro ⟨d₁, x₁, y₁⟩ _ ⟨d₂, x₂, y₂⟩ _ heq
    have hx : x₁ = x₂ := congrArg Prod.fst heq
    have hy : y₁ = y₂ := congrArg (fun p => p.2.1) heq
    have hz : x₁ + y₁ + d₁ = x₂ + y₂ + d₂ := congrArg (fun p => p.2.2) heq
    subst hx hy
    have hd : d₁ = d₂ := add_left_cancel hz
    subst hd
    rfl
  · rintro ⟨x, y, z⟩ hp
    rw [mem_filter] at hp
    simp only [mem_univ, true_and, pred, E_BC, E_BD, E_CD] at hp
    rcases hp with ⟨hz, hxy, hxz, hyz⟩
    refine ⟨(x + y + z, (x, y)), ?_, ?_⟩
    · rw [mem_filter, mem_product, mem_fiber]
      simp only [mem_univ, and_true, IsCorner]
      refine ⟨hz, hxy, ?_, ?_⟩
      · have hid : x + (x + y + z) = y + z := by
          calc x + (x + y + z) = (x + x) + (y + z) := by abel
            _ = y + z := by rw [f2_add_self, zero_add]
        simpa [hid] using hyz
      · have hid : y + (x + y + z) = x + z := by
          calc y + (x + y + z) = x + (y + y) + z := by abel
            _ = x + z := by rw [f2_add_self, add_zero]
        simpa [hid] using hxz
    · apply Prod.ext
      · rfl
      · apply Prod.ext
        · rfl
        · change x + y + (x + y + z) = z
          calc x + y + (x + y + z) = (x + x) + (y + y) + z := by abel
            _ = z := by rw [f2_add_self, f2_add_self, zero_add, zero_add]

private noncomputable def alphaBox {n : ℕ} (A : Finset (𝔽₂ n × 𝔽₂ n)) (B : Boxing n)
    (u v : 𝔽₂ B.r) : ℝ :=
  ((A ∩ (fiber B.proj u ×ˢ fiber B.proj v)).card : ℝ) / ((2 ^ (n - B.r) : ℝ) ^ 2)

private lemma alphaBox_nonneg {n : ℕ} (A : Finset (𝔽₂ n × 𝔽₂ n)) (B : Boxing n) (u v : 𝔽₂ B.r) :
    0 ≤ alphaBox A B u v := by
  unfold alphaBox; positivity

private lemma alphaBox_le_one {n : ℕ} (A : Finset (𝔽₂ n × 𝔽₂ n)) (B : Boxing n) (u v : 𝔽₂ B.r) :
    alphaBox A B u v ≤ 1 := by
  unfold alphaBox
  have hpos : (0 : ℝ) < (2 ^ (n - B.r) : ℝ) ^ 2 := by positivity
  rw [div_le_one hpos]
  have hle : (A ∩ (fiber B.proj u ×ˢ fiber B.proj v)).card ≤
      (fiber B.proj u ×ˢ fiber B.proj v).card := Finset.card_le_card inter_subset_right
  have hcard : ((fiber B.proj u ×ˢ fiber B.proj v).card : ℝ) = (2 ^ (n - B.r) : ℝ) ^ 2 := by
    rw [card_product, fiber_card B.proj B.hsurj u, fiber_card B.proj B.hsurj v, Nat.cast_mul]
    push_cast
    rw [sq]
  linarith [show ((A ∩ (fiber B.proj u ×ˢ fiber B.proj v)).card : ℝ) ≤
    ((fiber B.proj u ×ˢ fiber B.proj v).card : ℝ) from by exact_mod_cast hle]

private lemma sum_alphaBox_eq {n : ℕ} (A : Finset (𝔽₂ n × 𝔽₂ n)) (B : Boxing n) :
    (∑ u : 𝔽₂ B.r, ∑ v : 𝔽₂ B.r, alphaBox A B u v) / (4 ^ B.r : ℝ) =
      (A.card : ℝ) / (Fintype.card (𝔽₂ n) : ℝ) ^ 2 := by
  have hrn : B.r ≤ n := codim_le B.proj B.hsurj
  have hcov : (univ : Finset (𝔽₂ n × 𝔽₂ n)) =
      (univ : Finset (𝔽₂ B.r × 𝔽₂ B.r)).biUnion
        (fun p => fiber B.proj p.1 ×ˢ fiber B.proj p.2) := by
    ext ⟨x, y⟩
    simp [mem_fiber]
  have hdisj : ((univ : Finset (𝔽₂ B.r × 𝔽₂ B.r)) : Set (𝔽₂ B.r × 𝔽₂ B.r)).PairwiseDisjoint
      (fun p => fiber B.proj p.1 ×ˢ fiber B.proj p.2) := by
    intro p₁ _ p₂ _ hne
    refine Finset.disjoint_left.mpr ?_
    rintro ⟨x, y⟩ h₁ h₂
    simp only [mem_product, mem_fiber] at h₁ h₂
    exact hne (Prod.ext (h₁.1.symm.trans h₂.1) (h₁.2.symm.trans h₂.2))
  have hA_part : A = (univ : Finset (𝔽₂ B.r × 𝔽₂ B.r)).biUnion
      (fun p => A ∩ (fiber B.proj p.1 ×ˢ fiber B.proj p.2)) := by
    rw [← inter_biUnion, ← hcov, inter_univ]
  have hdisjA : ((univ : Finset (𝔽₂ B.r × 𝔽₂ B.r)) : Set (𝔽₂ B.r × 𝔽₂ B.r)).PairwiseDisjoint
      (fun p => A ∩ (fiber B.proj p.1 ×ˢ fiber B.proj p.2)) :=
    fun p₁ hp₁ p₂ hp₂ hne => (hdisj hp₁ hp₂ hne).mono inter_subset_right inter_subset_right
  have hAcard : (A.card : ℝ) =
      ∑ u : 𝔽₂ B.r, ∑ v : 𝔽₂ B.r, ((A ∩ (fiber B.proj u ×ˢ fiber B.proj v)).card : ℝ) := by
    have hnat : A.card =
        ∑ p : 𝔽₂ B.r × 𝔽₂ B.r, (A ∩ (fiber B.proj p.1 ×ˢ fiber B.proj p.2)).card := by
      conv_lhs => rw [hA_part, card_biUnion hdisjA]
    rw [Fintype.sum_prod_type] at hnat
    exact_mod_cast hnat
  have hden : (4 ^ B.r : ℝ) * (2 ^ (n - B.r) : ℝ) ^ 2 = (Fintype.card (𝔽₂ n) : ℝ) ^ 2 := by
    rw [f2_card]
    norm_cast
    rw [← four_pow_eq, ← mul_pow, ← pow_add, Nat.add_sub_of_le hrn]
  calc (∑ u : 𝔽₂ B.r, ∑ v : 𝔽₂ B.r, alphaBox A B u v) / (4 ^ B.r : ℝ)
      = ((∑ u, ∑ v, ((A ∩ (fiber B.proj u ×ˢ fiber B.proj v)).card : ℝ)) /
          (2 ^ (n - B.r) : ℝ) ^ 2) / (4 ^ B.r : ℝ) := by
          simp [alphaBox, ← sum_div]
    _ = (A.card : ℝ) / ((4 ^ B.r : ℝ) * (2 ^ (n - B.r) : ℝ) ^ 2) := by
          rw [← hAcard, div_div, mul_comm]
    _ = (A.card : ℝ) / (Fintype.card (𝔽₂ n) : ℝ) ^ 2 := by rw [hden]

private lemma regular_outer_box_cap_le {n : ℕ} (A : Finset (𝔽₂ n × 𝔽₂ n)) (B : Boxing n)
    {η : ℝ} (hη0 : 0 ≤ η) (u v : 𝔽₂ B.r) (hreg1 : OuterBoxReg1 B η u v)
    (f' : Fin B.m → Fin B.m → Fin B.m → ℝ)
    (hf'z_case : ∀ i j k, (Bpart B u v i).card * (Cpart B u v j).card * (Dpart B u v k).card = 0 →
      f' i j k = 0)
    (hpf'_prod : ∀ i j k,
      pB B u v i * pC B u v j * pD B u v k * f' i j k =
        (((Bpart B u v i ×ˢ (Cpart B u v j ×ˢ Dpart B u v k)).filter
          (fun p => p.1 + p.2.1 + p.2.2 = 0 ∧ (p.1, p.2.1) ∈ A)).card : ℝ) /
        (2 ^ (n - B.r) : ℝ) ^ 2) :
    ∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
      pB B u v i * pC B u v j * pD B u v k * (f' i j k - min (f' i j k) 1) ≤ η := by
  classical
  let W := LinearMap.ker B.proj
  have hW_card : (Fintype.card W : ℝ) = (2 ^ (n - B.r) : ℝ) := by
    exact_mod_cast card_ker_eq B.proj B.hsurj
  have hW_pos : (0 : ℝ) < (2 ^ (n - B.r) : ℝ) := by positivity
  let f : Fin B.m → Fin B.m → Fin B.m → ℝ := fun i j k => min (f' i j k) 1
  obtain ⟨x₀, hx₀⟩ := fiber_nonempty B.proj B.hsurj u
  obtain ⟨y₀, hy₀⟩ := fiber_nonempty B.proj B.hsurj v
  have hz₀ : x₀ + y₀ ∈ fiber B.proj (u + v) := by
    rw [mem_fiber] at hx₀ hy₀ ⊢; rw [map_add, hx₀, hy₀]
  have hm_ne : (B.m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr B.hm.ne'
  have hterm_diff : ∀ i j k,
      pB B u v i * pC B u v j * pD B u v k * (f' i j k - f i j k) ≤
        η / (B.m : ℝ) ^ 3 := by
    intro i j k
    by_cases hzero : (Bpart B u v i).card * (Cpart B u v j).card * (Dpart B u v k).card = 0
    · have hf'z : f' i j k = 0 := hf'z_case i j k hzero
      have hfz : f i j k = 0 := by simp [f, hf'z]
      rw [hf'z, hfz, sub_zero, mul_zero]
      positivity
    · have hf'bound : f' i j k ≤
          1 + (η / (B.m : ℝ) ^ 3) / (pB B u v i * pC B u v j * pD B u v k) := by
        let S₁ := shiftSet W x₀ (Bpart B u v i)
        let S₂ := shiftSet W y₀ (Cpart B u v j)
        let S₃ := shiftSet W (x₀ + y₀) (Dpart B u v k)
        have hS₁ : S₁.card = (Bpart B u v i).card :=
          card_shiftSet B.proj u hx₀ (filter_subset _ _)
        have hS₂ : S₂.card = (Cpart B u v j).card :=
          card_shiftSet B.proj v hy₀ (filter_subset _ _)
        have hS₃ : S₃.card = (Dpart B u v k).card :=
          card_shiftSet B.proj (u + v) hz₀ (filter_subset _ _)
        have hunif : ∀ ξ : W →ₗ[ZMod 2] ZMod 2, ξ ≠ 0 →
            |fourierCoeff W S₁ ξ| ≤ η / (B.m : ℝ) ^ 3 :=
          hreg1.1 i x₀ hx₀
        have hfour := triple_count_bound W S₁ S₂ S₃ 0 (by positivity) hunif
        let liftW : 𝔽₂ n → W := fun a => if h : a ∈ W then ⟨a, h⟩ else 0
        let toW : (𝔽₂ n × (𝔽₂ n × 𝔽₂ n)) → (W × (W × W)) := fun p =>
          (liftW (p.1 + x₀), liftW (p.2.1 + y₀), liftW (p.2.2 + (x₀ + y₀)))
        have hcard_le :
            ((Bpart B u v i ×ˢ (Cpart B u v j ×ˢ Dpart B u v k)).filter
              (fun p => p.1 + p.2.1 + p.2.2 = 0 ∧ (p.1, p.2.1) ∈ A)).card ≤
            ((S₁ ×ˢ (S₂ ×ˢ S₃)).filter (fun q => q.1 + q.2.1 + q.2.2 = 0)).card := by
          refine Finset.card_le_card_of_injOn toW ?_ ?_
          · rintro ⟨x, y, z⟩ hp
            simp only [coe_filter, mem_product, Set.mem_ofPred_eq] at hp ⊢
            rcases hp with ⟨⟨hx, hy, hz⟩, hzero, _⟩
            have hxW : x + x₀ ∈ W := by
              have hxf := mem_fiber.mp (filter_subset _ _ hx)
              rw [LinearMap.mem_ker, map_add, hxf, mem_fiber.mp hx₀, f2_add_self]
            have hyW : y + y₀ ∈ W := by
              have hyf := mem_fiber.mp (filter_subset _ _ hy)
              rw [LinearMap.mem_ker, map_add, hyf, mem_fiber.mp hy₀, f2_add_self]
            have hzW : z + (x₀ + y₀) ∈ W := by
              have hzf := mem_fiber.mp (filter_subset _ _ hz)
              rw [LinearMap.mem_ker, map_add, hzf, mem_fiber.mp hz₀, f2_add_self]
            have hl1 : (liftW (x + x₀) : 𝔽₂ n) = x + x₀ := by simp [liftW, hxW]
            have hl2 : (liftW (y + y₀) : 𝔽₂ n) = y + y₀ := by simp [liftW, hyW]
            have hl3 : (liftW (z + (x₀ + y₀)) : 𝔽₂ n) = z + (x₀ + y₀) := by simp [liftW, hzW]
            have hc1 : (x + x₀) + x₀ = x := by rw [add_assoc, f2_add_self, add_zero]
            have hc2 : (y + y₀) + y₀ = y := by rw [add_assoc, f2_add_self, add_zero]
            have hc3 : (z + (x₀ + y₀)) + (x₀ + y₀) = z := by
              rw [add_assoc, f2_add_self, add_zero]
            refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
            · simpa [S₁, shiftSet, toW, hl1, hc1] using hx
            · simpa [S₂, shiftSet, toW, hl2, hc2] using hy
            · simpa [S₃, shiftSet, toW, hl3, hc3] using hz
            · apply Subtype.ext
              change ((liftW (x + x₀) : 𝔽₂ n) + (liftW (y + y₀) : 𝔽₂ n)) +
                  (liftW (z + (x₀ + y₀)) : 𝔽₂ n) = 0
              rw [hl1, hl2, hl3]
              calc (x + x₀) + (y + y₀) + (z + (x₀ + y₀))
                  = (x + y + z) + (x₀ + x₀) + (y₀ + y₀) := by abel
                _ = 0 := by rw [hzero, f2_add_self x₀, f2_add_self y₀, add_zero, add_zero]
          · rintro ⟨x₁, y₁, z₁⟩ h₁ ⟨x₂, y₂, z₂⟩ h₂ heq
            simp only [coe_filter, mem_product, Set.mem_ofPred_eq] at h₁ h₂
            have hx₁W : x₁ + x₀ ∈ W := by
              rw [LinearMap.mem_ker, map_add, mem_fiber.mp (filter_subset _ _ h₁.1.1),
                mem_fiber.mp hx₀, f2_add_self]
            have hy₁W : y₁ + y₀ ∈ W := by
              rw [LinearMap.mem_ker, map_add, mem_fiber.mp (filter_subset _ _ h₁.1.2.1),
                mem_fiber.mp hy₀, f2_add_self]
            have hz₁W : z₁ + (x₀ + y₀) ∈ W := by
              rw [LinearMap.mem_ker, map_add, mem_fiber.mp (filter_subset _ _ h₁.1.2.2),
                mem_fiber.mp hz₀, f2_add_self]
            have hx₂W : x₂ + x₀ ∈ W := by
              rw [LinearMap.mem_ker, map_add, mem_fiber.mp (filter_subset _ _ h₂.1.1),
                mem_fiber.mp hx₀, f2_add_self]
            have hy₂W : y₂ + y₀ ∈ W := by
              rw [LinearMap.mem_ker, map_add, mem_fiber.mp (filter_subset _ _ h₂.1.2.1),
                mem_fiber.mp hy₀, f2_add_self]
            have hz₂W : z₂ + (x₀ + y₀) ∈ W := by
              rw [LinearMap.mem_ker, map_add, mem_fiber.mp (filter_subset _ _ h₂.1.2.2),
                mem_fiber.mp hz₀, f2_add_self]
            have e1 : x₁ + x₀ = x₂ + x₀ := by
              have := congrArg (fun q : W × W × W => (q.1 : 𝔽₂ n)) heq
              simpa [toW, liftW, hx₁W, hx₂W] using this
            have e2 : y₁ + y₀ = y₂ + y₀ := by
              have := congrArg (fun q : W × W × W => (q.2.1 : 𝔽₂ n)) heq
              simpa [toW, liftW, hy₁W, hy₂W] using this
            have e3 : z₁ + (x₀ + y₀) = z₂ + (x₀ + y₀) := by
              have := congrArg (fun q : W × W × W => (q.2.2 : 𝔽₂ n)) heq
              simpa [toW, liftW, hz₁W, hz₂W] using this
            exact Prod.ext (add_right_cancel e1) (Prod.ext (add_right_cancel e2) (add_right_cancel e3))
        have hcard_leR :
            (((Bpart B u v i ×ˢ (Cpart B u v j ×ˢ Dpart B u v k)).filter
              (fun p => p.1 + p.2.1 + p.2.2 = 0 ∧ (p.1, p.2.1) ∈ A)).card : ℝ) ≤
            (2 ^ (n - B.r) : ℝ) ^ 2 *
              (pB B u v i * pC B u v j * pD B u v k + η / (B.m : ℝ) ^ 3) := by
          have h1 : (((Bpart B u v i ×ˢ (Cpart B u v j ×ˢ Dpart B u v k)).filter
              (fun p => p.1 + p.2.1 + p.2.2 = 0 ∧ (p.1, p.2.1) ∈ A)).card : ℝ) ≤
              (((S₁ ×ˢ (S₂ ×ˢ S₃)).filter (fun q => q.1 + q.2.1 + q.2.2 = 0)).card : ℝ) := by
            exact_mod_cast hcard_le
          rw [hW_card, hS₁, hS₂, hS₃] at hfour
          have h4' : (((S₁ ×ˢ (S₂ ×ˢ S₃)).filter (fun q => q.1 + q.2.1 + q.2.2 = 0)).card : ℝ) ≤
              (2 ^ (n - B.r) : ℝ) ^ 2 *
                (pB B u v i * pC B u v j * pD B u v k + η / (B.m : ℝ) ^ 3) := by
            simpa only [pB, pC, pD] using hfour
          exact h1.trans h4'
        have h1 : ((Bpart B u v i).card : ℝ) ≠ 0 := by
          intro h; apply hzero; simp [Nat.cast_eq_zero.mp h]
        have h2 : ((Cpart B u v j).card : ℝ) ≠ 0 := by
          intro h; apply hzero; simp [Nat.cast_eq_zero.mp h]
        have h3 : ((Dpart B u v k).card : ℝ) ≠ 0 := by
          intro h; apply hzero; simp [Nat.cast_eq_zero.mp h]
        have hp_pos : 0 < pB B u v i * pC B u v j * pD B u v k := by
          simp only [pB, pC, pD]
          have h1p : 0 < ((Bpart B u v i).card : ℝ) := lt_of_le_of_ne (Nat.cast_nonneg _) h1.symm
          have h2p : 0 < ((Cpart B u v j).card : ℝ) := lt_of_le_of_ne (Nat.cast_nonneg _) h2.symm
          have h3p : 0 < ((Dpart B u v k).card : ℝ) := lt_of_le_of_ne (Nat.cast_nonneg _) h3.symm
          positivity
        calc f' i j k
            = (pB B u v i * pC B u v j * pD B u v k * f' i j k) /
                (pB B u v i * pC B u v j * pD B u v k) := by
                  exact (mul_div_cancel_left₀ (f' i j k) hp_pos.ne').symm
          _ = (((Bpart B u v i ×ˢ (Cpart B u v j ×ˢ Dpart B u v k)).filter
                (fun p => p.1 + p.2.1 + p.2.2 = 0 ∧ (p.1, p.2.1) ∈ A)).card : ℝ) /
                ((2 ^ (n - B.r) : ℝ) ^ 2 * (pB B u v i * pC B u v j * pD B u v k)) := by
                rw [hpf'_prod i j k, div_div]
          _ ≤ ((2 ^ (n - B.r) : ℝ) ^ 2 *
                (pB B u v i * pC B u v j * pD B u v k + η / (B.m : ℝ) ^ 3)) /
                ((2 ^ (n - B.r) : ℝ) ^ 2 * (pB B u v i * pC B u v j * pD B u v k)) :=
                div_le_div_of_nonneg_right hcard_leR (by positivity)
          _ = ((2 ^ (n - B.r) : ℝ) ^ 2 * (pB B u v i * pC B u v j * pD B u v k) +
                (2 ^ (n - B.r) : ℝ) ^ 2 * (η / (B.m : ℝ) ^ 3)) /
                ((2 ^ (n - B.r) : ℝ) ^ 2 * (pB B u v i * pC B u v j * pD B u v k)) := by ring
          _ = 1 + (η / (B.m : ℝ) ^ 3) / (pB B u v i * pC B u v j * pD B u v k) := by
                have hW2_ne : (2 ^ (n - B.r) : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hW_pos.ne'
                rw [add_div, div_self (mul_ne_zero hW2_ne hp_pos.ne'),
                  mul_div_mul_left _ _ hW2_ne]
      have hp_nn : 0 ≤ pB B u v i * pC B u v j * pD B u v k :=
        mul_nonneg (mul_nonneg (pB_nonneg _ _ _ _) (pC_nonneg _ _ _ _)) (pD_nonneg _ _ _ _)
      by_cases hf1le : f' i j k ≤ 1
      · have hfeq : f i j k = f' i j k := min_eq_left hf1le
        rw [hfeq, sub_self, mul_zero]
        positivity
      · have h1lt : 1 < f' i j k := not_le.mp hf1le
        have hfeq : f i j k = 1 := min_eq_right h1lt.le
        rw [hfeq]
        have hsub : f' i j k - 1 ≤ (η / (B.m : ℝ) ^ 3) / (pB B u v i * pC B u v j * pD B u v k) := by
          linarith
        have h1 : ((Bpart B u v i).card : ℝ) ≠ 0 := by
          intro h; apply hzero; simp [Nat.cast_eq_zero.mp h]
        have h2 : ((Cpart B u v j).card : ℝ) ≠ 0 := by
          intro h; apply hzero; simp [Nat.cast_eq_zero.mp h]
        have h3 : ((Dpart B u v k).card : ℝ) ≠ 0 := by
          intro h; apply hzero; simp [Nat.cast_eq_zero.mp h]
        have hp_pos : 0 < pB B u v i * pC B u v j * pD B u v k := by
          simp only [pB, pC, pD]
          have h1p : 0 < ((Bpart B u v i).card : ℝ) := lt_of_le_of_ne (Nat.cast_nonneg _) h1.symm
          have h2p : 0 < ((Cpart B u v j).card : ℝ) := lt_of_le_of_ne (Nat.cast_nonneg _) h2.symm
          have h3p : 0 < ((Dpart B u v k).card : ℝ) := lt_of_le_of_ne (Nat.cast_nonneg _) h3.symm
          positivity
        calc pB B u v i * pC B u v j * pD B u v k * (f' i j k - 1)
            ≤ pB B u v i * pC B u v j * pD B u v k *
                ((η / (B.m : ℝ) ^ 3) / (pB B u v i * pC B u v j * pD B u v k)) :=
                mul_le_mul_of_nonneg_left hsub hp_nn
          _ = η / (B.m : ℝ) ^ 3 := mul_div_cancel₀ _ hp_pos.ne'
  calc ∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
          pB B u v i * pC B u v j * pD B u v k * (f' i j k - f i j k)
      ≤ ∑ _i : Fin B.m, ∑ _j : Fin B.m, ∑ _k : Fin B.m, η / (B.m : ℝ) ^ 3 :=
        sum_le_sum fun i _ => sum_le_sum fun j _ => sum_le_sum fun k _ => hterm_diff i j k
    _ = (B.m : ℝ) ^ 3 * (η / (B.m : ℝ) ^ 3) := by simp; ring
    _ = η := by field_simp [hm_ne]

private noncomputable def capDens {n : ℕ} (A : Finset (𝔽₂ n × 𝔽₂ n)) (B : Boxing n)
    (u v : 𝔽₂ B.r) (i j k : Fin B.m) : ℝ :=
  if (Bpart B u v i).card * (Cpart B u v j).card * (Dpart B u v k).card = 0 then 0
  else (((Bpart B u v i ×ˢ (Cpart B u v j ×ˢ Dpart B u v k)).filter
          (fun p => p.1 + p.2.1 + p.2.2 = 0 ∧ (p.1, p.2.1) ∈ A)).card : ℝ) *
        (2 ^ (n - B.r) : ℝ) /
        (((Bpart B u v i).card : ℝ) * ((Cpart B u v j).card : ℝ) * ((Dpart B u v k).card : ℝ))

private lemma capDens_nonneg {n : ℕ} (A : Finset (𝔽₂ n × 𝔽₂ n)) (B : Boxing n)
    (u v : 𝔽₂ B.r) (i j k : Fin B.m) : 0 ≤ capDens A B u v i j k := by
  dsimp only [capDens]
  split_ifs <;> positivity

private lemma capDens_eq_zero {n : ℕ} (A : Finset (𝔽₂ n × 𝔽₂ n)) (B : Boxing n)
    (u v : 𝔽₂ B.r) {i j k : Fin B.m}
    (hzero : (Bpart B u v i).card * (Cpart B u v j).card * (Dpart B u v k).card = 0) :
    capDens A B u v i j k = 0 := by
  dsimp only [capDens]
  rw [if_pos hzero]

private lemma capDens_p_mul {n : ℕ} (A : Finset (𝔽₂ n × 𝔽₂ n)) (B : Boxing n)
    (u v : 𝔽₂ B.r) (i j k : Fin B.m) :
    pB B u v i * pC B u v j * pD B u v k * capDens A B u v i j k =
      (((Bpart B u v i ×ˢ (Cpart B u v j ×ˢ Dpart B u v k)).filter
        (fun p => p.1 + p.2.1 + p.2.2 = 0 ∧ (p.1, p.2.1) ∈ A)).card : ℝ) /
      (2 ^ (n - B.r) : ℝ) ^ 2 := by
  classical
  have hW_pos : (0 : ℝ) < (2 ^ (n - B.r) : ℝ) := by positivity
  dsimp only [capDens]
  by_cases hzero : (Bpart B u v i).card * (Cpart B u v j).card * (Dpart B u v k).card = 0
  · simp only [hzero, ↓reduceIte, mul_zero]
    rcases mul_eq_zero.mp hzero with h12 | h3
    · rcases mul_eq_zero.mp h12 with h1 | h2
      · simp [Finset.card_eq_zero.mp h1]
      · simp [Finset.card_eq_zero.mp h2]
    · simp [Finset.card_eq_zero.mp h3]
  · simp only [hzero, ↓reduceIte, pB, pC, pD]
    have h1 : ((Bpart B u v i).card : ℝ) ≠ 0 := by
      intro h; apply hzero; simp [Nat.cast_eq_zero.mp h]
    have h2 : ((Cpart B u v j).card : ℝ) ≠ 0 := by
      intro h; apply hzero; simp [Nat.cast_eq_zero.mp h]
    have h3 : ((Dpart B u v k).card : ℝ) ≠ 0 := by
      intro h; apply hzero; simp [Nat.cast_eq_zero.mp h]
    field_simp [hW_pos.ne', h1, h2, h3]

private lemma capDens_mean {n : ℕ} (A : Finset (𝔽₂ n × 𝔽₂ n)) (B : Boxing n)
    (u v : 𝔽₂ B.r) :
    ∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
      pB B u v i * pC B u v j * pD B u v k * capDens A B u v i j k = alphaBox A B u v := by
  classical
  simp_rw [capDens_p_mul A B u v, ← sum_div, ← Nat.cast_sum]
  unfold alphaBox
  congr 2
  let parts := fun t : Fin B.m × Fin B.m × Fin B.m =>
    (Bpart B u v t.1 ×ˢ (Cpart B u v t.2.1 ×ˢ Dpart B u v t.2.2)).filter
      (fun p => p.1 + p.2.1 + p.2.2 = 0 ∧ (p.1, p.2.1) ∈ A)
  have hdisj : ((univ : Finset (Fin B.m × Fin B.m × Fin B.m)) :
      Set (Fin B.m × Fin B.m × Fin B.m)).PairwiseDisjoint parts := by
    intro t₁ _ t₂ _ hne
    refine Finset.disjoint_left.mpr ?_
    rintro ⟨x, y, z⟩ h₁ h₂
    simp only [parts, mem_filter, mem_product, Bpart, Cpart, Dpart] at h₁ h₂
    by_cases h1 : t₁.1 = t₂.1
    · by_cases h2 : t₁.2.1 = t₂.2.1
      · exact hne (Prod.ext h1 (Prod.ext h2 (h₁.1.2.2.2.symm.trans h₂.1.2.2.2)))
      · exact h2 (h₁.1.2.1.2.symm.trans h₂.1.2.1.2)
    · exact h1 (h₁.1.1.2.symm.trans h₂.1.1.2)
  have hsum :
      (∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
        ((Bpart B u v i ×ˢ (Cpart B u v j ×ˢ Dpart B u v k)).filter
          (fun p => p.1 + p.2.1 + p.2.2 = 0 ∧ (p.1, p.2.1) ∈ A)).card) =
      ((univ.biUnion parts).card) := by
    rw [card_biUnion hdisj]
    exact sum_fin_triple_prod (fun t => (parts t).card)
  rw [hsum]
  refine Finset.card_bij (fun p _ => (p.1, p.2.1)) ?_ ?_ ?_
  · rintro ⟨x, y, z⟩ hp
    simp only [parts, mem_biUnion, mem_univ, true_and, mem_filter, mem_product,
      Bpart, Cpart, Dpart] at hp
    rcases hp with ⟨_, ⟨⟨hx, _⟩, ⟨hy, _⟩, _⟩, _, hA⟩
    exact mem_inter.mpr ⟨hA, mem_product.mpr ⟨hx, hy⟩⟩
  · rintro ⟨x₁, y₁, z₁⟩ h₁ ⟨x₂, y₂, z₂⟩ h₂ heq
    simp only [parts, mem_biUnion, mem_univ, true_and, mem_filter, mem_product] at h₁ h₂
    rcases h₁ with ⟨_, _, hz₁, _⟩
    rcases h₂ with ⟨_, _, hz₂, _⟩
    have hx : x₁ = x₂ := congrArg Prod.fst heq
    have hy : y₁ = y₂ := congrArg Prod.snd heq
    subst hx hy
    have hz : z₁ = z₂ := by
      calc z₁ = (x₁ + y₁) + (x₁ + y₁ + z₁) := by rw [← add_assoc, f2_add_self, zero_add]
        _ = x₁ + y₁ := by rw [hz₁, add_zero]
        _ = (x₁ + y₁) + (x₁ + y₁ + z₂) := by rw [hz₂, add_zero]
        _ = z₂ := by rw [← add_assoc, f2_add_self, zero_add]
    subst hz
    rfl
  · rintro ⟨x, y⟩ hxy
    rw [mem_inter, mem_product] at hxy
    rcases hxy with ⟨hA, hxu, hyv⟩
    have hz_fib : x + y ∈ fiber B.proj (u + v) := by
      rw [mem_fiber] at hxu hyv ⊢
      rw [map_add, hxu, hyv]
    refine ⟨(x, y, x + y), ?_, rfl⟩
    simp only [parts, mem_biUnion, mem_univ, true_and, mem_filter, mem_product,
      Bpart, Cpart, Dpart]
    refine ⟨(B.bCol u v x, B.cCol u v y, B.dCol u v (x + y)),
      ⟨⟨hxu, rfl⟩, ⟨hyv, rfl⟩, ⟨hz_fib, rfl⟩⟩, ?_, hA⟩
    rw [f2_add_self]

private lemma capDens_marg₁ {n : ℕ} (A : Finset (𝔽₂ n × 𝔽₂ n)) (B : Boxing n)
    (u v : 𝔽₂ B.r) (j k : Fin B.m) :
    ∑ i : Fin B.m, pB B u v i * capDens A B u v i j k =
      densBip (E_CD A) (Cpart B u v j) (Dpart B u v k) := by
  classical
  have hW_pos : (0 : ℝ) < (2 ^ (n - B.r) : ℝ) := by positivity
  by_cases hjk : (Cpart B u v j).card * (Dpart B u v k).card = 0
  · have h0 : ∀ i, pB B u v i * capDens A B u v i j k = 0 := fun i => by
      dsimp only [capDens]
      have hzero : (Bpart B u v i).card * (Cpart B u v j).card * (Dpart B u v k).card = 0 := by
        rw [mul_assoc, hjk, mul_zero]
      simp [hzero]
    rw [sum_eq_zero fun i _ => h0 i]
    unfold densBip setDens
    rw [card_product, hjk]
    simp
  · have hjne : (Cpart B u v j).card ≠ 0 := fun h => hjk (by simp [h])
    have hkne : (Dpart B u v k).card ≠ 0 := fun h => hjk (by simp [h])
    have hterm : ∀ i, pB B u v i * capDens A B u v i j k =
        (((Bpart B u v i ×ˢ (Cpart B u v j ×ˢ Dpart B u v k)).filter
          (fun p => p.1 + p.2.1 + p.2.2 = 0 ∧ (p.1, p.2.1) ∈ A)).card : ℝ) /
          (((Cpart B u v j).card : ℝ) * ((Dpart B u v k).card : ℝ)) := by
      intro i
      by_cases hi : (Bpart B u v i).card = 0
      · dsimp only [capDens]
        have hzero : (Bpart B u v i).card * (Cpart B u v j).card * (Dpart B u v k).card = 0 := by
          simp [hi]
        simp only [hzero, ↓reduceIte, mul_zero]
        simp [Finset.card_eq_zero.mp hi]
      · have hzero : (Bpart B u v i).card * (Cpart B u v j).card * (Dpart B u v k).card ≠ 0 :=
          mul_ne_zero (mul_ne_zero hi hjne) hkne
        dsimp only [capDens, pB]
        simp only [hzero, ↓reduceIte]
        have h1 : ((Bpart B u v i).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hi
        have h2 : ((Cpart B u v j).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hjne
        have h3 : ((Dpart B u v k).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hkne
        field_simp [hW_pos.ne', h1, h2, h3]
    simp_rw [hterm, ← sum_div, ← Nat.cast_sum]
    have hcard_eq :
        (∑ i : Fin B.m, ((Bpart B u v i ×ˢ (Cpart B u v j ×ˢ Dpart B u v k)).filter
          (fun p => p.1 + p.2.1 + p.2.2 = 0 ∧ (p.1, p.2.1) ∈ A)).card) =
        (E_CD A ∩ (Cpart B u v j ×ˢ Dpart B u v k)).card := by
      let parts := fun i : Fin B.m =>
        (Bpart B u v i ×ˢ (Cpart B u v j ×ˢ Dpart B u v k)).filter
          (fun p => p.1 + p.2.1 + p.2.2 = 0 ∧ (p.1, p.2.1) ∈ A)
      have hdisj : ((univ : Finset (Fin B.m)) : Set (Fin B.m)).PairwiseDisjoint parts := by
        intro i₁ _ i₂ _ hne
        refine Finset.disjoint_left.mpr ?_
        rintro ⟨x, y, z⟩ h₁ h₂
        simp only [parts, mem_filter, mem_product, Bpart] at h₁ h₂
        exact hne (h₁.1.1.2.symm.trans h₂.1.1.2)
      have hsum : (∑ i : Fin B.m, (parts i).card) = (univ.biUnion parts).card :=
        (card_biUnion hdisj).symm
      rw [hsum]
      refine Finset.card_bij (fun p _ => (p.2.1, p.2.2)) ?_ ?_ ?_
      · rintro ⟨x, y, z⟩ hp
        simp only [parts, mem_biUnion, mem_univ, true_and, mem_filter, mem_product] at hp
        rcases hp with ⟨_, ⟨_, hy, hz⟩, hzero, hA⟩
        have hid : y + z = x := by
          have h1 : (x + x) + (y + z) = (x + y + z) + x := by abel
          rw [f2_add_self x, zero_add, hzero, zero_add] at h1
          exact h1
        rw [mem_inter, mem_product]
        exact ⟨by simp [E_CD, hid, hA], hy, hz⟩
      · rintro ⟨x₁, y₁, z₁⟩ h₁ ⟨x₂, y₂, z₂⟩ h₂ heq
        simp only [parts, mem_biUnion, mem_univ, true_and, mem_filter, mem_product] at h₁ h₂
        rcases h₁ with ⟨_, _, hz₁, _⟩
        rcases h₂ with ⟨_, _, hz₂, _⟩
        have hy : y₁ = y₂ := congrArg Prod.fst heq
        have hz : z₁ = z₂ := congrArg Prod.snd heq
        subst hy hz
        have hx : x₁ = x₂ := by
          have hsub : x₁ + x₂ = 0 := by
            have h0 : (x₁ + y₁ + z₁) + (x₂ + y₁ + z₁) = (x₁ + x₂) + (y₁ + y₁) + (z₁ + z₁) := by abel
            rw [hz₁, hz₂, f2_add_self y₁, f2_add_self z₁] at h0
            simp only [add_zero] at h0
            exact h0.symm
          calc x₁ = x₁ + (x₂ + x₂) := by rw [f2_add_self, add_zero]
            _ = (x₁ + x₂) + x₂ := by abel
            _ = x₂ := by rw [hsub, zero_add]
        subst hx
        rfl
      · rintro ⟨y, z⟩ hyz
        rw [mem_inter, mem_product] at hyz
        rcases hyz with ⟨hE, hy, hz⟩
        simp only [E_CD, mem_filter, mem_univ, true_and] at hE
        have hy_fib : y ∈ fiber B.proj v := (filter_subset _ _ hy)
        have hz_fib : z ∈ fiber B.proj (u + v) := (filter_subset _ _ hz)
        rw [mem_fiber] at hy_fib hz_fib
        have hx_fib : y + z ∈ fiber B.proj u := by
          rw [mem_fiber, map_add, hy_fib, hz_fib]
          calc v + (u + v) = u + (v + v) := by abel
            _ = u := by rw [f2_add_self, add_zero]
        refine ⟨(y + z, y, z), ?_, rfl⟩
        simp only [parts, mem_biUnion, mem_univ, true_and, mem_filter, mem_product, Bpart]
        refine ⟨B.bCol u v (y + z), ⟨⟨hx_fib, rfl⟩, hy, hz⟩, ?_, hE⟩
        calc (y + z) + y + z = (y + y) + (z + z) := by abel
          _ = 0 := by rw [f2_add_self, f2_add_self, add_zero]
    rw [hcard_eq, ← card_mul_densBip]
    have h2 : ((Cpart B u v j).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hjne
    have h3 : ((Dpart B u v k).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hkne
    field_simp [h2, h3]

private lemma capDens_marg₂ {n : ℕ} (A : Finset (𝔽₂ n × 𝔽₂ n)) (B : Boxing n)
    (u v : 𝔽₂ B.r) (i k : Fin B.m) :
    ∑ j : Fin B.m, pC B u v j * capDens A B u v i j k =
      densBip (E_BD A) (Bpart B u v i) (Dpart B u v k) := by
  classical
  have hW_pos : (0 : ℝ) < (2 ^ (n - B.r) : ℝ) := by positivity
  by_cases hik : (Bpart B u v i).card * (Dpart B u v k).card = 0
  · have h0 : ∀ j, pC B u v j * capDens A B u v i j k = 0 := fun j => by
      dsimp only [capDens]
      have hzero : (Bpart B u v i).card * (Cpart B u v j).card * (Dpart B u v k).card = 0 := by
        calc (Bpart B u v i).card * (Cpart B u v j).card * (Dpart B u v k).card
            = ((Bpart B u v i).card * (Dpart B u v k).card) * (Cpart B u v j).card := by ring
          _ = 0 := by rw [hik, zero_mul]
      simp [hzero]
    rw [sum_eq_zero fun j _ => h0 j]
    unfold densBip setDens
    rw [card_product, hik]
    simp
  · have hine : (Bpart B u v i).card ≠ 0 := fun h => hik (by simp [h])
    have hkne : (Dpart B u v k).card ≠ 0 := fun h => hik (by simp [h])
    have hterm : ∀ j, pC B u v j * capDens A B u v i j k =
        (((Bpart B u v i ×ˢ (Cpart B u v j ×ˢ Dpart B u v k)).filter
          (fun p => p.1 + p.2.1 + p.2.2 = 0 ∧ (p.1, p.2.1) ∈ A)).card : ℝ) /
          (((Bpart B u v i).card : ℝ) * ((Dpart B u v k).card : ℝ)) := by
      intro j
      by_cases hj : (Cpart B u v j).card = 0
      · dsimp only [capDens]
        have hzero : (Bpart B u v i).card * (Cpart B u v j).card * (Dpart B u v k).card = 0 := by
          simp [hj]
        simp only [hzero, ↓reduceIte, mul_zero]
        simp [Finset.card_eq_zero.mp hj]
      · have hzero : (Bpart B u v i).card * (Cpart B u v j).card * (Dpart B u v k).card ≠ 0 :=
          mul_ne_zero (mul_ne_zero hine hj) hkne
        dsimp only [capDens, pC]
        simp only [hzero, ↓reduceIte]
        have h1 : ((Bpart B u v i).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hine
        have h2 : ((Cpart B u v j).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hj
        have h3 : ((Dpart B u v k).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hkne
        field_simp [hW_pos.ne', h1, h2, h3]
    simp_rw [hterm, ← sum_div, ← Nat.cast_sum]
    have hcard_eq :
        (∑ j : Fin B.m, ((Bpart B u v i ×ˢ (Cpart B u v j ×ˢ Dpart B u v k)).filter
          (fun p => p.1 + p.2.1 + p.2.2 = 0 ∧ (p.1, p.2.1) ∈ A)).card) =
        (E_BD A ∩ (Bpart B u v i ×ˢ Dpart B u v k)).card := by
      let parts := fun j : Fin B.m =>
        (Bpart B u v i ×ˢ (Cpart B u v j ×ˢ Dpart B u v k)).filter
          (fun p => p.1 + p.2.1 + p.2.2 = 0 ∧ (p.1, p.2.1) ∈ A)
      have hdisj : ((univ : Finset (Fin B.m)) : Set (Fin B.m)).PairwiseDisjoint parts := by
        intro j₁ _ j₂ _ hne
        refine Finset.disjoint_left.mpr ?_
        rintro ⟨x, y, z⟩ h₁ h₂
        simp only [parts, mem_filter, mem_product, Cpart] at h₁ h₂
        exact hne (h₁.1.2.1.2.symm.trans h₂.1.2.1.2)
      have hsum : (∑ j : Fin B.m, (parts j).card) = (univ.biUnion parts).card :=
        (card_biUnion hdisj).symm
      rw [hsum]
      refine Finset.card_bij (fun p _ => (p.1, p.2.2)) ?_ ?_ ?_
      · rintro ⟨x, y, z⟩ hp
        simp only [parts, mem_biUnion, mem_univ, true_and, mem_filter, mem_product] at hp
        rcases hp with ⟨_, ⟨hx, _, hz⟩, hzero, hA⟩
        have hid : x + z = y := by
          have h1 : (y + y) + (x + z) = (x + y + z) + y := by abel
          rw [f2_add_self y, zero_add, hzero, zero_add] at h1
          exact h1
        rw [mem_inter, mem_product]
        exact ⟨by simp [E_BD, hid, hA], hx, hz⟩
      · rintro ⟨x₁, y₁, z₁⟩ h₁ ⟨x₂, y₂, z₂⟩ h₂ heq
        simp only [parts, mem_biUnion, mem_univ, true_and, mem_filter, mem_product] at h₁ h₂
        rcases h₁ with ⟨_, _, hz₁, _⟩
        rcases h₂ with ⟨_, _, hz₂, _⟩
        have hx : x₁ = x₂ := congrArg Prod.fst heq
        have hz : z₁ = z₂ := congrArg Prod.snd heq
        subst hx hz
        have hy : y₁ = y₂ := by
          have hsub : y₁ + y₂ = 0 := by
            have h0 : (x₁ + y₁ + z₁) + (x₁ + y₂ + z₁) = (y₁ + y₂) + (x₁ + x₁) + (z₁ + z₁) := by abel
            rw [hz₁, hz₂, f2_add_self x₁, f2_add_self z₁] at h0
            simp only [add_zero] at h0
            exact h0.symm
          calc y₁ = y₁ + (y₂ + y₂) := by rw [f2_add_self, add_zero]
            _ = (y₁ + y₂) + y₂ := by abel
            _ = y₂ := by rw [hsub, zero_add]
        subst hy
        rfl
      · rintro ⟨x, z⟩ hxz
        rw [mem_inter, mem_product] at hxz
        rcases hxz with ⟨hE, hx, hz⟩
        simp only [E_BD, mem_filter, mem_univ, true_and] at hE
        have hx_fib : x ∈ fiber B.proj u := (filter_subset _ _ hx)
        have hz_fib : z ∈ fiber B.proj (u + v) := (filter_subset _ _ hz)
        rw [mem_fiber] at hx_fib hz_fib
        have hy_fib : x + z ∈ fiber B.proj v := by
          rw [mem_fiber, map_add, hx_fib, hz_fib]
          calc u + (u + v) = (u + u) + v := by abel
            _ = v := by rw [f2_add_self, zero_add]
        refine ⟨(x, x + z, z), ?_, rfl⟩
        simp only [parts, mem_biUnion, mem_univ, true_and, mem_filter, mem_product, Cpart]
        refine ⟨B.cCol u v (x + z), ⟨hx, ⟨hy_fib, rfl⟩, hz⟩, ?_, hE⟩
        calc x + (x + z) + z = (x + x) + (z + z) := by abel
          _ = 0 := by rw [f2_add_self, f2_add_self, add_zero]
    rw [hcard_eq, ← card_mul_densBip]
    have h1 : ((Bpart B u v i).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hine
    have h3 : ((Dpart B u v k).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hkne
    field_simp [h1, h3]

private lemma capDens_marg₃ {n : ℕ} (A : Finset (𝔽₂ n × 𝔽₂ n)) (B : Boxing n)
    (u v : 𝔽₂ B.r) (i j : Fin B.m) :
    ∑ k : Fin B.m, pD B u v k * capDens A B u v i j k =
      densBip (E_BC A) (Bpart B u v i) (Cpart B u v j) := by
  classical
  have hW_pos : (0 : ℝ) < (2 ^ (n - B.r) : ℝ) := by positivity
  by_cases hij : (Bpart B u v i).card * (Cpart B u v j).card = 0
  · have h0 : ∀ k, pD B u v k * capDens A B u v i j k = 0 := fun k => by
      dsimp only [capDens]
      have hzero : (Bpart B u v i).card * (Cpart B u v j).card * (Dpart B u v k).card = 0 := by
        rw [hij, zero_mul]
      simp [hzero]
    rw [sum_eq_zero fun k _ => h0 k]
    unfold densBip setDens
    rw [card_product, hij]
    simp
  · have hine : (Bpart B u v i).card ≠ 0 := fun h => hij (by simp [h])
    have hjne : (Cpart B u v j).card ≠ 0 := fun h => hij (by simp [h])
    have hterm : ∀ k, pD B u v k * capDens A B u v i j k =
        (((Bpart B u v i ×ˢ (Cpart B u v j ×ˢ Dpart B u v k)).filter
          (fun p => p.1 + p.2.1 + p.2.2 = 0 ∧ (p.1, p.2.1) ∈ A)).card : ℝ) /
          (((Bpart B u v i).card : ℝ) * ((Cpart B u v j).card : ℝ)) := by
      intro k
      by_cases hk : (Dpart B u v k).card = 0
      · dsimp only [capDens]
        have hzero : (Bpart B u v i).card * (Cpart B u v j).card * (Dpart B u v k).card = 0 := by
          simp [hk]
        simp only [hzero, ↓reduceIte, mul_zero]
        simp [Finset.card_eq_zero.mp hk]
      · have hzero : (Bpart B u v i).card * (Cpart B u v j).card * (Dpart B u v k).card ≠ 0 :=
          mul_ne_zero (mul_ne_zero hine hjne) hk
        dsimp only [capDens, pD]
        simp only [hzero, ↓reduceIte]
        have h1 : ((Bpart B u v i).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hine
        have h2 : ((Cpart B u v j).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hjne
        have h3 : ((Dpart B u v k).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
        field_simp [hW_pos.ne', h1, h2, h3]
    simp_rw [hterm, ← sum_div, ← Nat.cast_sum]
    have hcard_eq :
        (∑ k : Fin B.m, ((Bpart B u v i ×ˢ (Cpart B u v j ×ˢ Dpart B u v k)).filter
          (fun p => p.1 + p.2.1 + p.2.2 = 0 ∧ (p.1, p.2.1) ∈ A)).card) =
        (E_BC A ∩ (Bpart B u v i ×ˢ Cpart B u v j)).card := by
      let parts := fun k : Fin B.m =>
        (Bpart B u v i ×ˢ (Cpart B u v j ×ˢ Dpart B u v k)).filter
          (fun p => p.1 + p.2.1 + p.2.2 = 0 ∧ (p.1, p.2.1) ∈ A)
      have hdisj : ((univ : Finset (Fin B.m)) : Set (Fin B.m)).PairwiseDisjoint parts := by
        intro k₁ _ k₂ _ hne
        refine Finset.disjoint_left.mpr ?_
        rintro ⟨x, y, z⟩ h₁ h₂
        simp only [parts, mem_filter, mem_product, Dpart] at h₁ h₂
        exact hne (h₁.1.2.2.2.symm.trans h₂.1.2.2.2)
      have hsum : (∑ k : Fin B.m, (parts k).card) = (univ.biUnion parts).card :=
        (card_biUnion hdisj).symm
      rw [hsum]
      refine Finset.card_bij (fun p _ => (p.1, p.2.1)) ?_ ?_ ?_
      · rintro ⟨x, y, z⟩ hp
        simp only [parts, mem_biUnion, mem_univ, true_and, mem_filter, mem_product] at hp
        rcases hp with ⟨_, ⟨hx, hy, _⟩, _, hA⟩
        exact mem_inter.mpr ⟨hA, mem_product.mpr ⟨hx, hy⟩⟩
      · rintro ⟨x₁, y₁, z₁⟩ h₁ ⟨x₂, y₂, z₂⟩ h₂ heq
        simp only [parts, mem_biUnion, mem_univ, true_and, mem_filter, mem_product] at h₁ h₂
        rcases h₁ with ⟨_, _, hz₁, _⟩
        rcases h₂ with ⟨_, _, hz₂, _⟩
        have hx : x₁ = x₂ := congrArg Prod.fst heq
        have hy : y₁ = y₂ := congrArg Prod.snd heq
        subst hx hy
        have hz : z₁ = z₂ := by
          calc z₁ = (x₁ + y₁) + (x₁ + y₁ + z₁) := by rw [← add_assoc, f2_add_self, zero_add]
            _ = x₁ + y₁ := by rw [hz₁, add_zero]
            _ = (x₁ + y₁) + (x₁ + y₁ + z₂) := by rw [hz₂, add_zero]
            _ = z₂ := by rw [← add_assoc, f2_add_self, zero_add]
        subst hz
        rfl
      · rintro ⟨x, y⟩ hxy
        rw [mem_inter, mem_product] at hxy
        rcases hxy with ⟨hE, hx, hy⟩
        have hx_fib : x ∈ fiber B.proj u := (filter_subset _ _ hx)
        have hy_fib : y ∈ fiber B.proj v := (filter_subset _ _ hy)
        rw [mem_fiber] at hx_fib hy_fib
        have hz_fib : x + y ∈ fiber B.proj (u + v) := by
          rw [mem_fiber, map_add, hx_fib, hy_fib]
        refine ⟨(x, y, x + y), ?_, rfl⟩
        simp only [parts, mem_biUnion, mem_univ, true_and, mem_filter, mem_product, Dpart]
        refine ⟨B.dCol u v (x + y), ⟨hx, hy, ⟨hz_fib, rfl⟩⟩, ?_, hE⟩
        rw [f2_add_self]
    rw [hcard_eq, ← card_mul_densBip]
    have h1 : ((Bpart B u v i).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hine
    have h2 : ((Cpart B u v j).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hjne
    field_simp [h1, h2]

open scoped Classical in
private lemma regular_outer_box_term_count {n : ℕ} (A : Finset (𝔽₂ n × 𝔽₂ n)) (B : Boxing n)
    {η : ℝ} (hη0 : 0 ≤ η) (u v : 𝔽₂ B.r) (i j k : Fin B.m) :
    (2 ^ (n - B.r) : ℝ) ^ 3 *
      (pB B u v i * pC B u v j * pD B u v k *
        densBip (E_CD A) (Cpart B u v j) (Dpart B u v k) *
        densBip (E_BD A) (Bpart B u v i) (Dpart B u v k) *
        densBip (E_BC A) (Bpart B u v i) (Cpart B u v j) -
        2 * η * (pB B u v i * pC B u v j * pD B u v k) -
        ((if IsQuasirandom (E_BC A) (Bpart B u v i) (Cpart B u v j) η then 0
            else pB B u v i * pC B u v j * pD B u v k) +
         (if IsQuasirandom (E_BD A) (Bpart B u v i) (Dpart B u v k) η then 0
            else pB B u v i * pC B u v j * pD B u v k) +
         (if IsQuasirandom (E_CD A) (Cpart B u v j) (Dpart B u v k) η then 0
            else pB B u v i * pC B u v j * pD B u v k))) ≤
    (((Bpart B u v i ×ˢ (Cpart B u v j ×ˢ Dpart B u v k)).filter (fun p =>
      (p.1, p.2.1) ∈ E_BC A ∧ (p.1, p.2.2) ∈ E_BD A ∧ (p.2.1, p.2.2) ∈ E_CD A)).card : ℝ) := by
  classical
  have hW_pos : (0 : ℝ) < (2 ^ (n - B.r) : ℝ) := by positivity
  have hprod_card :
      ((Bpart B u v i).card : ℝ) * ((Cpart B u v j).card : ℝ) * ((Dpart B u v k).card : ℝ) =
        (2 ^ (n - B.r) : ℝ) ^ 3 * (pB B u v i * pC B u v j * pD B u v k) := by
    simp only [pB, pC, pD]
    have hW_ne : (2 ^ (n - B.r) : ℝ) ≠ 0 := hW_pos.ne'
    calc ((Bpart B u v i).card : ℝ) * ((Cpart B u v j).card : ℝ) * ((Dpart B u v k).card : ℝ)
        = (((2 ^ (n - B.r) : ℝ) * (((Bpart B u v i).card : ℝ) / (2 ^ (n - B.r) : ℝ))) *
            ((2 ^ (n - B.r) : ℝ) * (((Cpart B u v j).card : ℝ) / (2 ^ (n - B.r) : ℝ)))) *
            ((2 ^ (n - B.r) : ℝ) * (((Dpart B u v k).card : ℝ) / (2 ^ (n - B.r) : ℝ))) := by
            rw [mul_div_cancel₀ _ hW_ne, mul_div_cancel₀ _ hW_ne, mul_div_cancel₀ _ hW_ne]
      _ = _ := by ring
  by_cases hqr : IsQuasirandom (E_BC A) (Bpart B u v i) (Cpart B u v j) η ∧
      IsQuasirandom (E_BD A) (Bpart B u v i) (Dpart B u v k) η ∧
      IsQuasirandom (E_CD A) (Cpart B u v j) (Dpart B u v k) η
  · simp only [hqr.1, hqr.2.1, hqr.2.2, ↓reduceIte, add_zero, sub_zero]
    have htc := triangle_counting_lemma (Bpart B u v i) (Cpart B u v j) (Dpart B u v k)
      (E_BC A) (E_BD A) (E_CD A) hη0 hqr.1 hqr.2.1 hqr.2.2
    have hlow := (abs_le.mp htc).1
    have hrw1 :
        densBip (E_BC A) (Bpart B u v i) (Cpart B u v j) *
          densBip (E_BD A) (Bpart B u v i) (Dpart B u v k) *
          densBip (E_CD A) (Cpart B u v j) (Dpart B u v k) *
          ((Bpart B u v i).card : ℝ) * ((Cpart B u v j).card : ℝ) * ((Dpart B u v k).card : ℝ) -
        2 * η * ((Bpart B u v i).card : ℝ) * ((Cpart B u v j).card : ℝ) * ((Dpart B u v k).card : ℝ) =
        (2 ^ (n - B.r) : ℝ) ^ 3 *
          (pB B u v i * pC B u v j * pD B u v k *
            densBip (E_CD A) (Cpart B u v j) (Dpart B u v k) *
            densBip (E_BD A) (Bpart B u v i) (Dpart B u v k) *
            densBip (E_BC A) (Bpart B u v i) (Cpart B u v j) -
            2 * η * (pB B u v i * pC B u v j * pD B u v k)) := by
      calc _ = (densBip (E_BC A) (Bpart B u v i) (Cpart B u v j) *
                densBip (E_BD A) (Bpart B u v i) (Dpart B u v k) *
                densBip (E_CD A) (Cpart B u v j) (Dpart B u v k) - 2 * η) *
                (((Bpart B u v i).card : ℝ) * ((Cpart B u v j).card : ℝ) * ((Dpart B u v k).card : ℝ)) := by ring
        _ = (densBip (E_BC A) (Bpart B u v i) (Cpart B u v j) *
                densBip (E_BD A) (Bpart B u v i) (Dpart B u v k) *
                densBip (E_CD A) (Cpart B u v j) (Dpart B u v k) - 2 * η) *
                ((2 ^ (n - B.r) : ℝ) ^ 3 * (pB B u v i * pC B u v j * pD B u v k)) := by rw [hprod_card]
        _ = _ := by ring
    linarith
  · have hp_nn : 0 ≤ pB B u v i * pC B u v j * pD B u v k :=
      mul_nonneg (mul_nonneg (pB_nonneg _ _ _ _) (pC_nonneg _ _ _ _)) (pD_nonneg _ _ _ _)
    have hd1 : densBip (E_CD A) (Cpart B u v j) (Dpart B u v k) ≤ 1 := densBip_le_one _ _ _
    have hd2 : densBip (E_BD A) (Bpart B u v i) (Dpart B u v k) ≤ 1 := densBip_le_one _ _ _
    have hd3 : densBip (E_BC A) (Bpart B u v i) (Cpart B u v j) ≤ 1 := densBip_le_one _ _ _
    have hd10 := densBip_nonneg (E_CD A) (Cpart B u v j) (Dpart B u v k)
    have hd20 := densBip_nonneg (E_BD A) (Bpart B u v i) (Dpart B u v k)
    have hd30 := densBip_nonneg (E_BC A) (Bpart B u v i) (Cpart B u v j)
    have hprod_d : densBip (E_CD A) (Cpart B u v j) (Dpart B u v k) *
        densBip (E_BD A) (Bpart B u v i) (Dpart B u v k) *
        densBip (E_BC A) (Bpart B u v i) (Cpart B u v j) ≤ 1 :=
      mul_le_one₀ (mul_le_one₀ hd1 hd20 hd2) hd30 hd3
    have hbad_ge : pB B u v i * pC B u v j * pD B u v k ≤
        (if IsQuasirandom (E_BC A) (Bpart B u v i) (Cpart B u v j) η then 0
          else pB B u v i * pC B u v j * pD B u v k) +
        (if IsQuasirandom (E_BD A) (Bpart B u v i) (Dpart B u v k) η then 0
          else pB B u v i * pC B u v j * pD B u v k) +
        (if IsQuasirandom (E_CD A) (Cpart B u v j) (Dpart B u v k) η then 0
          else pB B u v i * pC B u v j * pD B u v k) := by
      by_cases h1 : IsQuasirandom (E_BC A) (Bpart B u v i) (Cpart B u v j) η <;>
        by_cases h2 : IsQuasirandom (E_BD A) (Bpart B u v i) (Dpart B u v k) η <;>
        by_cases h3 : IsQuasirandom (E_CD A) (Cpart B u v j) (Dpart B u v k) η
      · exact absurd ⟨h1, h2, h3⟩ hqr
      · simp [h1, h2, h3]
      · simp [h1, h2, h3]
      · simp [h1, h2, h3]; linarith
      · simp [h1, h2, h3]
      · simp [h1, h2, h3]; linarith
      · simp [h1, h2, h3]; linarith
      · simp [h1, h2, h3]; linarith
    have hnonpos :
        pB B u v i * pC B u v j * pD B u v k *
          densBip (E_CD A) (Cpart B u v j) (Dpart B u v k) *
          densBip (E_BD A) (Bpart B u v i) (Dpart B u v k) *
          densBip (E_BC A) (Bpart B u v i) (Cpart B u v j) -
          2 * η * (pB B u v i * pC B u v j * pD B u v k) -
          ((if IsQuasirandom (E_BC A) (Bpart B u v i) (Cpart B u v j) η then 0
              else pB B u v i * pC B u v j * pD B u v k) +
           (if IsQuasirandom (E_BD A) (Bpart B u v i) (Dpart B u v k) η then 0
              else pB B u v i * pC B u v j * pD B u v k) +
           (if IsQuasirandom (E_CD A) (Cpart B u v j) (Dpart B u v k) η then 0
              else pB B u v i * pC B u v j * pD B u v k)) ≤ 0 := by
      have h1 : pB B u v i * pC B u v j * pD B u v k *
          densBip (E_CD A) (Cpart B u v j) (Dpart B u v k) *
          densBip (E_BD A) (Bpart B u v i) (Dpart B u v k) *
          densBip (E_BC A) (Bpart B u v i) (Cpart B u v j) ≤
          pB B u v i * pC B u v j * pD B u v k := by
        calc _ = (pB B u v i * pC B u v j * pD B u v k) *
              (densBip (E_CD A) (Cpart B u v j) (Dpart B u v k) *
               densBip (E_BD A) (Bpart B u v i) (Dpart B u v k) *
               densBip (E_BC A) (Bpart B u v i) (Cpart B u v j)) := by ring
          _ ≤ (pB B u v i * pC B u v j * pD B u v k) * 1 :=
              mul_le_mul_of_nonneg_left hprod_d hp_nn
          _ = _ := mul_one _
      have h2 : 0 ≤ 2 * η * (pB B u v i * pC B u v j * pD B u v k) := by positivity
      linarith
    have hcard_nn : (0 : ℝ) ≤ (((Bpart B u v i ×ˢ (Cpart B u v j ×ˢ Dpart B u v k)).filter (fun p =>
      (p.1, p.2.1) ∈ E_BC A ∧ (p.1, p.2.2) ∈ E_BD A ∧ (p.2.1, p.2.2) ∈ E_CD A)).card : ℝ) :=
      Nat.cast_nonneg _
    have hlhs_np : (2 ^ (n - B.r) : ℝ) ^ 3 * _ ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hnonpos
    linarith

private lemma regular_outer_box_corners {n : ℕ} (A : Finset (𝔽₂ n × 𝔽₂ n)) (B : Boxing n)
    {η : ℝ} (hη0 : 0 ≤ η) (_hη1 : η ≤ 1)
    (u v : 𝔽₂ B.r) (hreg1 : OuterBoxReg1 B η u v) (hreg2 : OuterBoxReg2 A B η u v) :
    (2 ^ (n - B.r) : ℝ) ^ 3 * (alphaBox A B u v ^ 4 - 9 * η) ≤
      ∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
        (((Bpart B u v i ×ˢ (Cpart B u v j ×ˢ Dpart B u v k)).filter (fun p =>
          (p.1, p.2.1) ∈ E_BC A ∧ (p.1, p.2.2) ∈ E_BD A ∧ (p.2.1, p.2.2) ∈ E_CD A)).card : ℝ) := by
  classical
  let f' : Fin B.m → Fin B.m → Fin B.m → ℝ := capDens A B u v
  let f : Fin B.m → Fin B.m → Fin B.m → ℝ := fun i j k => min (f' i j k) 1
  have hf0 : ∀ i j k, 0 ≤ f i j k := fun i j k => le_min (capDens_nonneg A B u v i j k) zero_le_one
  have hf1 : ∀ i j k, f i j k ≤ 1 := fun i j k => min_le_right _ _
  have hf_le_f' : ∀ i j k, f i j k ≤ f' i j k := fun i j k => min_le_left _ _
  have hmean_diff :
      ∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
        pB B u v i * pC B u v j * pD B u v k * (f' i j k - f i j k) ≤ η :=
    regular_outer_box_cap_le A B hη0 u v hreg1 f'
      (fun i j k hzero => capDens_eq_zero A B u v hzero)
      (capDens_p_mul A B u v)
  have hmean_f : alphaBox A B u v - η ≤
      ∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
        pB B u v i * pC B u v j * pD B u v k * f i j k := by
    have hsplit :
        ∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
            pB B u v i * pC B u v j * pD B u v k * (f' i j k - f i j k) =
          alphaBox A B u v -
          ∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
            pB B u v i * pC B u v j * pD B u v k * f i j k := by
      dsimp only [f']
      rw [← capDens_mean A B u v]
      simp_rw [mul_sub, sum_sub_distrib]
    linarith
  have htri_mono : weightedTriforce (pB B u v) (pC B u v) (pD B u v) f ≤
      weightedTriforce (pB B u v) (pC B u v) (pD B u v) f' := by
    unfold weightedTriforce
    refine sum_le_sum fun i _ => sum_le_sum fun j _ => sum_le_sum fun k _ => ?_
    have hw : 0 ≤ pB B u v i * pC B u v j * pD B u v k :=
      mul_nonneg (mul_nonneg (pB_nonneg _ _ _ _) (pC_nonneg _ _ _ _)) (pD_nonneg _ _ _ _)
    have h1 : ∑ i', pB B u v i' * f i' j k ≤ ∑ i', pB B u v i' * f' i' j k :=
      sum_le_sum fun i' _ => mul_le_mul_of_nonneg_left (hf_le_f' i' j k) (pB_nonneg _ _ _ _)
    have h2 : ∑ j', pC B u v j' * f i j' k ≤ ∑ j', pC B u v j' * f' i j' k :=
      sum_le_sum fun j' _ => mul_le_mul_of_nonneg_left (hf_le_f' i j' k) (pC_nonneg _ _ _ _)
    have h3 : ∑ k', pD B u v k' * f i j k' ≤ ∑ k', pD B u v k' * f' i j k' :=
      sum_le_sum fun k' _ => mul_le_mul_of_nonneg_left (hf_le_f' i j k') (pD_nonneg _ _ _ _)
    have h10 : 0 ≤ ∑ i', pB B u v i' * f i' j k :=
      sum_nonneg fun i' _ => mul_nonneg (pB_nonneg _ _ _ _) (hf0 i' j k)
    have h20 : 0 ≤ ∑ j', pC B u v j' * f i j' k :=
      sum_nonneg fun j' _ => mul_nonneg (pC_nonneg _ _ _ _) (hf0 i j' k)
    have h30 : 0 ≤ ∑ k', pD B u v k' * f i j k' :=
      sum_nonneg fun k' _ => mul_nonneg (pD_nonneg _ _ _ _) (hf0 i j k')
    have h1'0 := h10.trans h1
    have h2'0 := h20.trans h2
    calc pB B u v i * pC B u v j * pD B u v k *
            (∑ i', pB B u v i' * f i' j k) * (∑ j', pC B u v j' * f i j' k) *
            (∑ k', pD B u v k' * f i j k')
        = (pB B u v i * pC B u v j * pD B u v k) *
            (((∑ i', pB B u v i' * f i' j k) * (∑ j', pC B u v j' * f i j' k)) *
              (∑ k', pD B u v k' * f i j k')) := by ring
      _ ≤ (pB B u v i * pC B u v j * pD B u v k) *
            (((∑ i', pB B u v i' * f' i' j k) * (∑ j', pC B u v j' * f' i j' k)) *
              (∑ k', pD B u v k' * f' i j k')) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul (mul_le_mul h1 h2 h20 h1'0) h3 h30 (mul_nonneg h1'0 h2'0)) hw
      _ = _ := by ring
  have htri_f : (∑ i, ∑ j, ∑ k, pB B u v i * pC B u v j * pD B u v k * f i j k) ^ 4 ≤
      weightedTriforce (pB B u v) (pC B u v) (pD B u v) f :=
    weightedTriforce_ge_pow_four (pB B u v) (pC B u v) (pD B u v)
      (pB_nonneg B u v) (pC_nonneg B u v) (pD_nonneg B u v)
      (sum_pB_eq_one B u v) (sum_pC_eq_one B u v) (sum_pD_eq_one B u v)
      f hf0 hf1
  have hpow4_lb : alphaBox A B u v ^ 4 - 4 * η ≤
      (∑ i, ∑ j, ∑ k, pB B u v i * pC B u v j * pD B u v k * f i j k) ^ 4 := by
    have ha0 := alphaBox_nonneg A B u v
    have ha1 := alphaBox_le_one A B u v
    have hm0 : 0 ≤ ∑ i, ∑ j, ∑ k, pB B u v i * pC B u v j * pD B u v k * f i j k :=
      sum_nonneg fun i _ => sum_nonneg fun j _ => sum_nonneg fun k _ =>
        mul_nonneg (mul_nonneg (mul_nonneg (pB_nonneg _ _ _ _) (pC_nonneg _ _ _ _))
          (pD_nonneg _ _ _ _)) (hf0 i j k)
    by_cases hle : alphaBox A B u v ≤ η
    · have ha4 : alphaBox A B u v ^ 4 ≤ alphaBox A B u v := by
        calc alphaBox A B u v ^ 4 = alphaBox A B u v * alphaBox A B u v ^ 3 := by ring
          _ ≤ alphaBox A B u v * 1 := mul_le_mul_of_nonneg_left
              (pow_le_one₀ ha0 ha1) ha0
          _ = alphaBox A B u v := mul_one _
      have hsub : alphaBox A B u v ^ 4 - 4 * η ≤ 0 := by linarith
      exact hsub.trans (pow_nonneg hm0 4)
    · have hlt : η < alphaBox A B u v := not_le.mp hle
      set y := alphaBox A B u v - η
      have hy0 : 0 ≤ y := sub_nonneg.mpr hlt.le
      have hy1 : y ≤ 1 := by linarith
      have hy_pow : y ^ 4 ≤ (∑ i, ∑ j, ∑ k, pB B u v i * pC B u v j * pD B u v k * f i j k) ^ 4 :=
        pow_le_pow_left₀ hy0 hmean_f 4
      have hdiff4 : alphaBox A B u v ^ 4 - y ^ 4 ≤ 4 * η := by
        have hfac : alphaBox A B u v ^ 4 - y ^ 4 =
            η * (alphaBox A B u v ^ 3 + alphaBox A B u v ^ 2 * y +
              alphaBox A B u v * y ^ 2 + y ^ 3) := by
          dsimp only [y]; ring
        have hsum_le : alphaBox A B u v ^ 3 + alphaBox A B u v ^ 2 * y +
            alphaBox A B u v * y ^ 2 + y ^ 3 ≤ 4 := by
          have ha3 : alphaBox A B u v ^ 3 ≤ 1 := pow_le_one₀ ha0 ha1
          have ha2y : alphaBox A B u v ^ 2 * y ≤ 1 :=
            mul_le_one₀ (pow_le_one₀ ha0 ha1) hy0 hy1
          have hay2 : alphaBox A B u v * y ^ 2 ≤ 1 :=
            mul_le_one₀ ha1 (sq_nonneg y) (pow_le_one₀ hy0 hy1)
          have hy3 : y ^ 3 ≤ 1 := pow_le_one₀ hy0 hy1
          linarith
        rw [hfac]
        nlinarith
      linarith
  have htri_f'_eq : weightedTriforce (pB B u v) (pC B u v) (pD B u v) f' =
      ∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
        pB B u v i * pC B u v j * pD B u v k *
          densBip (E_CD A) (Cpart B u v j) (Dpart B u v k) *
          densBip (E_BD A) (Bpart B u v i) (Dpart B u v k) *
          densBip (E_BC A) (Bpart B u v i) (Cpart B u v j) := by
    unfold weightedTriforce
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
    rw [capDens_marg₁ A B u v j k, capDens_marg₂ A B u v i k, capDens_marg₃ A B u v i j]
  have hsum_count := sum_le_sum fun i (_ : i ∈ univ) =>
    sum_le_sum fun j (_ : j ∈ univ) =>
    sum_le_sum fun k (_ : k ∈ univ) => regular_outer_box_term_count A B hη0 u v i j k
  simp_rw [← mul_sum] at hsum_count
  have hsum_badBC : (∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
      if IsQuasirandom (E_BC A) (Bpart B u v i) (Cpart B u v j) η then 0
      else pB B u v i * pC B u v j * pD B u v k) = badWeightBC A B η u v := by
    have hf : ∀ i j k,
        (if IsQuasirandom (E_BC A) (Bpart B u v i) (Cpart B u v j) η then 0
         else pB B u v i * pC B u v j * pD B u v k) =
        (if IsQuasirandom (E_BC A) (Bpart B u v i) (Cpart B u v j) η then 0
         else pB B u v i * pC B u v j) * pD B u v k := fun i j k => by split_ifs <;> ring
    simp_rw [hf, ← mul_sum, sum_pD_eq_one, mul_one]
    rfl
  have hsum_badBD : (∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
      if IsQuasirandom (E_BD A) (Bpart B u v i) (Dpart B u v k) η then 0
      else pB B u v i * pC B u v j * pD B u v k) = badWeightBD A B η u v := by
    let wBD : Fin B.m → Fin B.m → ℝ := fun i k =>
      if IsQuasirandom (E_BD A) (Bpart B u v i) (Dpart B u v k) η then 0
      else pB B u v i * pD B u v k
    have hf : ∀ i j k,
        (if IsQuasirandom (E_BD A) (Bpart B u v i) (Dpart B u v k) η then 0
         else pB B u v i * pC B u v j * pD B u v k) =
        pC B u v j * wBD i k := fun i j k => by dsimp only [wBD]; split_ifs <;> ring
    simp_rw [hf]
    calc ∑ i, ∑ j, ∑ k, pC B u v j * wBD i k
        = ∑ i, ∑ k, ∑ j, pC B u v j * wBD i k := sum_congr rfl fun i _ => sum_comm
      _ = ∑ i, ∑ k, (∑ j, pC B u v j) * wBD i k :=
          sum_congr rfl fun i _ => sum_congr rfl fun k _ => (sum_mul _ _ _).symm
      _ = badWeightBD A B η u v := by simp_rw [sum_pC_eq_one, one_mul]; rfl
  have hsum_badCD : (∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
      if IsQuasirandom (E_CD A) (Cpart B u v j) (Dpart B u v k) η then 0
      else pB B u v i * pC B u v j * pD B u v k) = badWeightCD A B η u v := by
    let wCD : Fin B.m → Fin B.m → ℝ := fun j k =>
      if IsQuasirandom (E_CD A) (Cpart B u v j) (Dpart B u v k) η then 0
      else pC B u v j * pD B u v k
    have hf : ∀ i j k,
        (if IsQuasirandom (E_CD A) (Cpart B u v j) (Dpart B u v k) η then 0
         else pB B u v i * pC B u v j * pD B u v k) =
        pB B u v i * wCD j k := fun i j k => by dsimp only [wCD]; split_ifs <;> ring
    simp_rw [hf]
    calc ∑ i, ∑ j, ∑ k, pB B u v i * wCD j k
        = ∑ j, ∑ i, ∑ k, pB B u v i * wCD j k := sum_comm
      _ = ∑ j, ∑ k, ∑ i, pB B u v i * wCD j k := sum_congr rfl fun j _ => sum_comm
      _ = ∑ j, ∑ k, (∑ i, pB B u v i) * wCD j k :=
          sum_congr rfl fun j _ => sum_congr rfl fun k _ => (sum_mul _ _ _).symm
      _ = badWeightCD A B η u v := by simp_rw [sum_pB_eq_one, one_mul]; rfl
  simp only [sum_sub_distrib, sum_add_distrib, ← mul_sum, sum_pD_eq_one, mul_one,
    sum_pC_eq_one, sum_pB_eq_one] at hsum_count
  rw [← htri_f'_eq, hsum_badBC, hsum_badBD, hsum_badCD] at hsum_count
  have hbad_sum : badWeightBC A B η u v + badWeightBD A B η u v + badWeightCD A B η u v ≤ 3 * η := by
    linarith [hreg2.1, hreg2.2.1, hreg2.2.2]
  have hinner_lb : alphaBox A B u v ^ 4 - 9 * η ≤
      weightedTriforce (pB B u v) (pC B u v) (pD B u v) f' - 2 * η -
        (badWeightBC A B η u v + badWeightBD A B η u v + badWeightCD A B η u v) := by
    linarith [hpow4_lb, htri_f, htri_mono]
  calc (2 ^ (n - B.r) : ℝ) ^ 3 * (alphaBox A B u v ^ 4 - 9 * η)
      ≤ (2 ^ (n - B.r) : ℝ) ^ 3 *
          (weightedTriforce (pB B u v) (pC B u v) (pD B u v) f' - 2 * η -
            (badWeightBC A B η u v + badWeightBD A B η u v + badWeightCD A B η u v)) :=
          mul_le_mul_of_nonneg_left hinner_lb (by positivity)
    _ ≤ _ := hsum_count

private lemma sum_pow4_ge_pow4_sum {ι : Type*} (s : Finset ι) (g : ι → ℝ) :
    (∑ x ∈ s, g x) ^ 4 ≤ (s.card : ℝ) ^ 3 * ∑ x ∈ s, g x ^ 4 := by
  have h1 : (∑ x ∈ s, g x) ^ 2 ≤ (s.card : ℝ) * ∑ x ∈ s, g x ^ 2 := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) g
    simpa using hcs
  have h2 : (∑ x ∈ s, g x ^ 2) ^ 2 ≤ (s.card : ℝ) * ∑ x ∈ s, g x ^ 4 := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun x => g x ^ 2)
    have hsq : ∀ x, (g x ^ 2) ^ 2 = g x ^ 4 := fun x => by ring
    simpa [hsq] using hcs
  have h1sq : (∑ x ∈ s, g x) ^ 4 ≤ ((s.card : ℝ) * ∑ x ∈ s, g x ^ 2) ^ 2 := by
    have hpow := pow_le_pow_left₀ (sq_nonneg _) h1 2
    calc (∑ x ∈ s, g x) ^ 4 = ((∑ x ∈ s, g x) ^ 2) ^ 2 := by ring
      _ ≤ _ := hpow
  calc (∑ x ∈ s, g x) ^ 4
      ≤ (s.card : ℝ) ^ 2 * (∑ x ∈ s, g x ^ 2) ^ 2 := by nlinarith
    _ ≤ (s.card : ℝ) ^ 2 * ((s.card : ℝ) * ∑ x ∈ s, g x ^ 4) :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    _ = (s.card : ℝ) ^ 3 * ∑ x ∈ s, g x ^ 4 := by ring

private lemma S_zero_card {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (A : Finset (G × G)) : (S 0 A).card = A.card := by
  classical
  have heq : S (0 : G) A = A := by
    ext ⟨x, y⟩
    simp [S, IsCorner]
  rw [heq]

/-- Mandache's popular-corners theorem on $\mathbb{F}_2^n \times \mathbb{F}_2^n$ with exponent $4$. -/
theorem popular_corner_f2_pow_four (α ε : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ A : Finset (𝔽₂ n × 𝔽₂ n),
        let N : ℝ := (Fintype.card (𝔽₂ n) : ℝ)
        (A.card : ℝ) ≥ α * N^2 →
        ∃ d : 𝔽₂ n, d ≠ 0 ∧ ((S d A).card : ℝ) ≥ (α^4 - ε) * N^2 := by
  classical
  let _ := hα1
  let η : ℝ := min (ε / 22) (1 / 2)
  have hη0 : 0 < η := lt_min (by positivity) (by norm_num)
  have hη1 : η ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hη_eps : 11 * η ≤ ε / 2 := by linarith [min_le_left (ε / 22) (1 / 2)]
  obtain ⟨R_max, hreg⟩ := regularity_lemma hη0
  let k₀ : ℕ := Nat.floor (max 2 (2 / ε)) + 1
  have hk₀_gt : max 2 (2 / ε) < (2 ^ k₀ : ℝ) := by
    have hfl : max 2 (2 / ε) < (k₀ : ℝ) := by
      dsimp only [k₀]
      push_cast
      exact Nat.lt_floor_add_one _
    have hpow : (k₀ : ℝ) < (2 ^ k₀ : ℝ) := by
      exact_mod_cast Nat.lt_two_pow_self
    exact hfl.trans hpow
  rw [Filter.eventually_atTop]
  refine ⟨R_max + k₀, fun n hn A => ?_⟩
  dsimp only
  intro hA
  let N : ℝ := (Fintype.card (𝔽₂ n) : ℝ)
  obtain ⟨B, hc1, hc2, hBr⟩ := hreg n A
  have hW_ge_max : max 2 (2 / ε) ≤ (2 ^ (n - B.r) : ℝ) := by
    have hk_le : k₀ ≤ n - B.r := by omega
    have h2 : (2 ^ k₀ : ℝ) ≤ (2 ^ (n - B.r) : ℝ) := by
      exact_mod_cast Nat.pow_le_pow_right (by norm_num) hk_le
    exact hk₀_gt.le.trans h2
  have hW_ge_2 : (2 : ℝ) ≤ (2 ^ (n - B.r) : ℝ) := (le_max_left _ _).trans hW_ge_max
  have hW_ge_eps : 2 / ε ≤ (2 ^ (n - B.r) : ℝ) := (le_max_right _ _).trans hW_ge_max
  have hW_nat_ge_2 : 2 ≤ (fiber B.proj 0).card := by
    rw [fiber_card B.proj B.hsurj 0]
    exact_mod_cast hW_ge_2
  let W₀ := (fiber B.proj 0).erase 0
  have hW₀_ne : W₀.Nonempty := by
    have hcard : 0 < W₀.card := by
      rw [card_erase_of_mem (mem_fiber.mpr (map_zero B.proj))]
      omega
    exact Finset.card_pos.mp hcard
  by_cases hneg : α ^ 4 - ε ≤ 0
  · obtain ⟨d, hd⟩ := hW₀_ne
    have hd0 : d ≠ 0 := (mem_erase.mp hd).1
    refine ⟨d, hd0, ?_⟩
    have hN2 : 0 ≤ N ^ 2 := sq_nonneg N
    have hS0 : (0 : ℝ) ≤ ((S d A).card : ℝ) := Nat.cast_nonneg _
    nlinarith
  · have hpos_diff : 0 < α ^ 4 - ε := not_le.mp hneg
    let bad1 : Finset (𝔽₂ B.r × 𝔽₂ B.r) :=
      univ.filter (fun p : 𝔽₂ B.r × 𝔽₂ B.r => ¬ OuterBoxReg1 B η p.1 p.2)
    let bad2 : Finset (𝔽₂ B.r × 𝔽₂ B.r) :=
      univ.filter (fun p : 𝔽₂ B.r × 𝔽₂ B.r => ¬ OuterBoxReg2 A B η p.1 p.2)
    have hbox_lb : ∀ u v : 𝔽₂ B.r,
        (2 ^ (n - B.r) : ℝ) ^ 3 *
          (alphaBox A B u v ^ 4 - 9 * η -
            (if (u, v) ∈ bad1 then 1 else 0) - (if (u, v) ∈ bad2 then 1 else 0)) ≤
        ∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
          (((Bpart B u v i ×ˢ (Cpart B u v j ×ˢ Dpart B u v k)).filter (fun p =>
            (p.1, p.2.1) ∈ E_BC A ∧ (p.1, p.2.2) ∈ E_BD A ∧ (p.2.1, p.2.2) ∈ E_CD A)).card : ℝ) := by
      intro u v
      by_cases hb1 : (u, v) ∈ bad1
      · have ha1 : alphaBox A B u v ^ 4 ≤ 1 :=
          pow_le_one₀ (alphaBox_nonneg A B u v) (alphaBox_le_one A B u v)
        have hb2_nn : (0 : ℝ) ≤ if (u, v) ∈ bad2 then 1 else 0 := by split_ifs <;> norm_num
        have hnp : alphaBox A B u v ^ 4 - 9 * η - (if (u, v) ∈ bad1 then 1 else 0) -
            (if (u, v) ∈ bad2 then 1 else 0) ≤ 0 := by
          simp only [hb1, ↓reduceIte]; linarith
        have hsum_nn : (0 : ℝ) ≤ ∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
            (((Bpart B u v i ×ˢ (Cpart B u v j ×ˢ Dpart B u v k)).filter (fun p =>
              (p.1, p.2.1) ∈ E_BC A ∧ (p.1, p.2.2) ∈ E_BD A ∧ (p.2.1, p.2.2) ∈ E_CD A)).card : ℝ) :=
          sum_nonneg fun i _ => sum_nonneg fun j _ => sum_nonneg fun k _ => Nat.cast_nonneg _
        have hleft : (2 ^ (n - B.r) : ℝ) ^ 3 * _ ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) hnp
        linarith
      · by_cases hb2 : (u, v) ∈ bad2
        · have ha1 : alphaBox A B u v ^ 4 ≤ 1 :=
            pow_le_one₀ (alphaBox_nonneg A B u v) (alphaBox_le_one A B u v)
          have hnp : alphaBox A B u v ^ 4 - 9 * η - (if (u, v) ∈ bad1 then 1 else 0) -
              (if (u, v) ∈ bad2 then 1 else 0) ≤ 0 := by
            simp only [hb1, hb2, ↓reduceIte]; linarith
          have hsum_nn : (0 : ℝ) ≤ ∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
              (((Bpart B u v i ×ˢ (Cpart B u v j ×ˢ Dpart B u v k)).filter (fun p =>
                (p.1, p.2.1) ∈ E_BC A ∧ (p.1, p.2.2) ∈ E_BD A ∧ (p.2.1, p.2.2) ∈ E_CD A)).card : ℝ) :=
            sum_nonneg fun i _ => sum_nonneg fun j _ => sum_nonneg fun k _ => Nat.cast_nonneg _
          have hleft : (2 ^ (n - B.r) : ℝ) ^ 3 * _ ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (by positivity) hnp
          linarith
        · have hr1 : OuterBoxReg1 B η u v := by
            by_contra hn; exact hb1 (mem_filter.mpr ⟨mem_univ _, hn⟩)
          have hr2 : OuterBoxReg2 A B η u v := by
            by_contra hn; exact hb2 (mem_filter.mpr ⟨mem_univ _, hn⟩)
          simp only [hb1, hb2, ↓reduceIte, sub_zero]
          exact regular_outer_box_corners A B hη0.le hη1 u v hr1 hr2
    have hsum_boxes := sum_le_sum fun u (_ : u ∈ univ) => sum_le_sum fun v (_ : v ∈ univ) => hbox_lb u v
    simp_rw [← mul_sum] at hsum_boxes
    have hcorners_eq :
        (∑ d ∈ fiber B.proj 0, ((S d A).card : ℝ)) =
          ∑ u : 𝔽₂ B.r, ∑ v : 𝔽₂ B.r, ∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
            (((Bpart B u v i ×ˢ (Cpart B u v j ×ˢ Dpart B u v k)).filter (fun p =>
              (p.1, p.2.1) ∈ E_BC A ∧ (p.1, p.2.2) ∈ E_BD A ∧ (p.2.1, p.2.2) ∈ E_CD A)).card : ℝ) := by
      exact_mod_cast sum_corners_ker_eq A B
    rw [← hcorners_eq] at hsum_boxes
    have hbad1_sum : (∑ u : 𝔽₂ B.r, ∑ v : 𝔽₂ B.r, if (u, v) ∈ bad1 then (1 : ℝ) else 0) =
        (bad1.card : ℝ) := by
      calc (∑ u : 𝔽₂ B.r, ∑ v : 𝔽₂ B.r, if (u, v) ∈ bad1 then (1 : ℝ) else 0)
          = ∑ p : 𝔽₂ B.r × 𝔽₂ B.r, if p ∈ bad1 then (1 : ℝ) else 0 :=
            (Fintype.sum_prod_type (fun p : 𝔽₂ B.r × 𝔽₂ B.r =>
              if p ∈ bad1 then (1 : ℝ) else 0)).symm
        _ = (bad1.card : ℝ) := by
            rw [← Finset.sum_filter]
            simp
    have hbad2_sum : (∑ u : 𝔽₂ B.r, ∑ v : 𝔽₂ B.r, if (u, v) ∈ bad2 then (1 : ℝ) else 0) =
        (bad2.card : ℝ) := by
      calc (∑ u : 𝔽₂ B.r, ∑ v : 𝔽₂ B.r, if (u, v) ∈ bad2 then (1 : ℝ) else 0)
          = ∑ p : 𝔽₂ B.r × 𝔽₂ B.r, if p ∈ bad2 then (1 : ℝ) else 0 :=
            (Fintype.sum_prod_type (fun p : 𝔽₂ B.r × 𝔽₂ B.r =>
              if p ∈ bad2 then (1 : ℝ) else 0)).symm
        _ = (bad2.card : ℝ) := by
            rw [← Finset.sum_filter]
            simp
    have hconst_sum : (∑ _u : 𝔽₂ B.r, ∑ _v : 𝔽₂ B.r, 9 * η) = (4 ^ B.r : ℝ) * (9 * η) := by
      simp only [sum_const, card_univ, nsmul_eq_mul, f2_card, Nat.cast_pow, Nat.cast_ofNat]
      rw [← mul_assoc, ← sq, four_pow_eq_real]
    have hpow4_jensen : (4 ^ B.r : ℝ) * α ^ 4 ≤
        ∑ u : 𝔽₂ B.r, ∑ v : 𝔽₂ B.r, alphaBox A B u v ^ 4 := by
      have hcs := sum_pow4_ge_pow4_sum (univ : Finset (𝔽₂ B.r × 𝔽₂ B.r))
        (fun p => alphaBox A B p.1 p.2)
      have hcard4 : ((univ : Finset (𝔽₂ B.r × 𝔽₂ B.r)).card : ℝ) = (4 ^ B.r : ℝ) := by
        simp only [card_univ, Fintype.card_prod, f2_card, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
        rw [← sq, four_pow_eq_real]
      have hsum_α : (4 ^ B.r : ℝ) * α ≤
          ∑ p ∈ (univ : Finset (𝔽₂ B.r × 𝔽₂ B.r)), alphaBox A B p.1 p.2 := by
        rw [Fintype.sum_prod_type]
        have hmean := sum_alphaBox_eq A B
        have hN_pos : 0 < N := by
          dsimp only [N]; rw [f2_card]; positivity
        have hα_le : α ≤ (A.card : ℝ) / N ^ 2 := (le_div_iff₀ (sq_pos_of_pos hN_pos)).mpr hA
        have h4pos : (0 : ℝ) < (4 ^ B.r : ℝ) := by positivity
        rw [← hmean, le_div_iff₀ h4pos] at hα_le
        linarith
      have hpow4 : ((4 ^ B.r : ℝ) * α) ^ 4 ≤
          (∑ p ∈ (univ : Finset (𝔽₂ B.r × 𝔽₂ B.r)), alphaBox A B p.1 p.2) ^ 4 :=
        pow_le_pow_left₀ (by positivity) hsum_α 4
      rw [hcard4] at hcs
      have hcomb : (4 ^ B.r : ℝ) ^ 4 * α ^ 4 ≤
          (4 ^ B.r : ℝ) ^ 3 * ∑ u : 𝔽₂ B.r, ∑ v : 𝔽₂ B.r, alphaBox A B u v ^ 4 := by
        calc (4 ^ B.r : ℝ) ^ 4 * α ^ 4 = ((4 ^ B.r : ℝ) * α) ^ 4 := by ring
          _ ≤ (∑ p ∈ (univ : Finset (𝔽₂ B.r × 𝔽₂ B.r)), alphaBox A B p.1 p.2) ^ 4 := hpow4
          _ ≤ (4 ^ B.r : ℝ) ^ 3 * ∑ p ∈ (univ : Finset (𝔽₂ B.r × 𝔽₂ B.r)), alphaBox A B p.1 p.2 ^ 4 := hcs
          _ = _ := by rw [Fintype.sum_prod_type]
      have h3pos : (0 : ℝ) < (4 ^ B.r : ℝ) ^ 3 := by positivity
      nlinarith
    have hinner_sum_lb : (4 ^ B.r : ℝ) * (α ^ 4 - ε / 2) ≤
        ∑ u : 𝔽₂ B.r, ∑ v : 𝔽₂ B.r,
          (alphaBox A B u v ^ 4 - 9 * η -
            (if (u, v) ∈ bad1 then 1 else 0) - (if (u, v) ∈ bad2 then 1 else 0)) := by
      simp only [sum_sub_distrib]
      rw [hbad1_sum, hbad2_sum, hconst_sum]
      have hc1' : (bad1.card : ℝ) ≤ η * (4 ^ B.r : ℝ) := hc1
      have hc2' : (bad2.card : ℝ) ≤ η * (4 ^ B.r : ℝ) := hc2
      have h4pos : (0 : ℝ) ≤ (4 ^ B.r : ℝ) := by positivity
      nlinarith [hη_eps, hpow4_jensen]
    have hWN2 : (2 ^ (n - B.r) : ℝ) ^ 3 * (4 ^ B.r : ℝ) = (2 ^ (n - B.r) : ℝ) * N ^ 2 := by
      have hrn : B.r ≤ n := codim_le B.proj B.hsurj
      dsimp only [N]
      rw [f2_card]
      norm_cast
      rw [← four_pow_eq]
      calc (2 ^ (n - B.r)) ^ 3 * (2 ^ B.r) ^ 2
          = 2 ^ (n - B.r) * (2 ^ (n - B.r) * 2 ^ B.r) ^ 2 := by ring
        _ = 2 ^ (n - B.r) * (2 ^ n) ^ 2 := by
            rw [← pow_add, Nat.sub_add_cancel hrn]
    have hker_sum_lb : (2 ^ (n - B.r) : ℝ) * (α ^ 4 - ε / 2) * N ^ 2 ≤
        ∑ d ∈ fiber B.proj 0, ((S d A).card : ℝ) := by
      calc (2 ^ (n - B.r) : ℝ) * (α ^ 4 - ε / 2) * N ^ 2
          = (2 ^ (n - B.r) : ℝ) ^ 3 * ((4 ^ B.r : ℝ) * (α ^ 4 - ε / 2)) := by
              rw [← mul_assoc, hWN2]; ring
        _ ≤ (2 ^ (n - B.r) : ℝ) ^ 3 *
              ∑ u : 𝔽₂ B.r, ∑ v : 𝔽₂ B.r,
                (alphaBox A B u v ^ 4 - 9 * η -
                  (if (u, v) ∈ bad1 then 1 else 0) - (if (u, v) ∈ bad2 then 1 else 0)) :=
              mul_le_mul_of_nonneg_left hinner_sum_lb (by positivity)
        _ ≤ _ := hsum_boxes
    have hS0_le : ((S (0 : 𝔽₂ n) A).card : ℝ) ≤ N ^ 2 := by
      rw [S_zero_card]
      have hle : A.card ≤ Fintype.card (𝔽₂ n × 𝔽₂ n) := Finset.card_le_univ A
      have hcard : (Fintype.card (𝔽₂ n × 𝔽₂ n) : ℝ) = N ^ 2 := by
        dsimp only [N]; rw [Fintype.card_prod, Nat.cast_mul, sq]
      rw [← hcard]
      exact_mod_cast hle
    have hW₀_sum_split : ∑ d ∈ fiber B.proj 0, ((S d A).card : ℝ) =
        ((S (0 : 𝔽₂ n) A).card : ℝ) + ∑ d ∈ W₀, ((S d A).card : ℝ) :=
      (add_sum_erase (fiber B.proj 0) (fun d => ((S d A).card : ℝ))
        (mem_fiber.mpr (map_zero B.proj))).symm
    have hW₀_card : (W₀.card : ℝ) = (2 ^ (n - B.r) : ℝ) - 1 := by
      rw [card_erase_of_mem (mem_fiber.mpr (map_zero B.proj)), fiber_card B.proj B.hsurj 0]
      have hpos : 1 ≤ 2 ^ (n - B.r) := Nat.one_le_pow _ _ (by norm_num)
      rw [Nat.cast_sub hpos]
      norm_num
    have hW₀_sum_lb : (W₀.card : ℝ) * ((α ^ 4 - ε) * N ^ 2) ≤ ∑ d ∈ W₀, ((S d A).card : ℝ) := by
      have hN2 : 0 ≤ N ^ 2 := sq_nonneg N
      have hWε : 1 ≤ (2 ^ (n - B.r) : ℝ) * (ε / 2) := by
        calc (1 : ℝ) = (2 / ε) * (ε / 2) := by field_simp [hε.ne']
          _ ≤ (2 ^ (n - B.r) : ℝ) * (ε / 2) := mul_le_mul_of_nonneg_right hW_ge_eps (by positivity)
      calc (W₀.card : ℝ) * ((α ^ 4 - ε) * N ^ 2)
          = ((2 ^ (n - B.r) : ℝ) - 1) * ((α ^ 4 - ε) * N ^ 2) := by rw [hW₀_card]
        _ ≤ (2 ^ (n - B.r) : ℝ) * ((α ^ 4 - ε) * N ^ 2) := by
            nlinarith [mul_nonneg hpos_diff.le hN2]
        _ ≤ ((2 ^ (n - B.r) : ℝ) * (α ^ 4 - ε / 2) - 1) * N ^ 2 := by
            nlinarith
        _ = (2 ^ (n - B.r) : ℝ) * (α ^ 4 - ε / 2) * N ^ 2 - N ^ 2 := by ring
        _ ≤ (∑ d ∈ fiber B.proj 0, ((S d A).card : ℝ)) - ((S (0 : 𝔽₂ n) A).card : ℝ) := by
            linarith
        _ = ∑ d ∈ W₀, ((S d A).card : ℝ) := by linarith [hW₀_sum_split]
    by_contra hnone
    push Not at hnone
    have hlt : ∑ d ∈ W₀, ((S d A).card : ℝ) < (W₀.card : ℝ) * ((α ^ 4 - ε) * N ^ 2) := by
      calc ∑ d ∈ W₀, ((S d A).card : ℝ)
          < ∑ _d ∈ W₀, (α ^ 4 - ε) * N ^ 2 :=
            Finset.sum_lt_sum (fun d hd => (hnone d (mem_erase.mp hd).1).le)
              (by obtain ⟨d, hd⟩ := hW₀_ne; exact ⟨d, hd, hnone d (mem_erase.mp hd).1⟩)
        _ = (W₀.card : ℝ) * ((α ^ 4 - ε) * N ^ 2) := by simp
    linarith

/-- Mandache's theorem: $4$ is a valid exponent for Ben Green's Open Problem 19. -/
theorem validExponent_four : ValidExponent 4 := by
  refine ⟨1 / 2, by norm_num, fun α hα0 hα1 => ?_⟩
  have hpop := popular_corner_f2_pow_four α (α ^ 4 / 2) hα0 hα1.le (by positivity)
  refine hpop.mono fun n hn A hA => ?_
  obtain ⟨d, hd0, hdcard⟩ := hn A hA
  refine ⟨d, hd0, ?_⟩
  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  linarith

/-- Monotonicity of `ValidExponent`: any $c \ge 4$ is a valid exponent. -/
theorem validExponent_of_ge_four {c : ℝ} (hc : 4 ≤ c) : ValidExponent c := by
  obtain ⟨K, hK0, hK⟩ := validExponent_four
  refine ⟨K, hK0, fun α hα0 hα1 => ?_⟩
  refine (hK α hα0 hα1).mono fun n hn A hA => ?_
  obtain ⟨d, hd0, hdcard⟩ := hn A hA
  refine ⟨d, hd0, ?_⟩
  have hrpow : α ^ c ≤ α ^ (4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hα0 hα1.le hc
  have hN2 : 0 ≤ (Fintype.card (𝔽₂ n) : ℝ) ^ 2 := sq_nonneg _
  calc K * α ^ c * (Fintype.card (𝔽₂ n) : ℝ) ^ 2
      ≤ K * α ^ (4 : ℝ) * (Fintype.card (𝔽₂ n) : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrpow hK0.le) hN2
    _ ≤ ((S d A).card : ℝ) := hdcard

end TriangleCountingAndMain



/- ### 1. Mandache's Explicit 2 × 2 × 2 Kernel -/

/-- Mandache's 2×2×2 kernel `g(i, j, k) = 0` iff `i = j = k`. -/
def mandacheKernel (i j k : Fin 2) : ℝ :=
  if i = j ∧ j = k then 0 else 1

/-- Mandache's 2×2×2 kernel has exact triforce density `13 / 32`. -/
theorem mandacheKernel_triforce :
    weightedTriforce (fun _ => (1 / 2 : ℝ)) (fun _ => (1 / 2 : ℝ))
      (fun _ => (1 / 2 : ℝ)) mandacheKernel = 13 / 32 := by
  simp [weightedTriforce, mandacheKernel, Fin.sum_univ_two]
  norm_num

/- ### 2. Constructive Behrend 3-AP-Free Sphere Construction -/

private lemma evalBase_lt (d b : ℕ) (u : Fin d → ℕ) (hu : ∀ j, u j < b) :
    ∑ j : Fin d, u j * b ^ (j : ℕ) < b ^ d := by
  induction d with
  | zero =>
    simp
  | succ d ih =>
    rw [Fin.sum_univ_succ]
    have htail : ∑ j : Fin d, u j.succ * b ^ (j.succ : ℕ) =
        b * ∑ j : Fin d, u j.succ * b ^ (j : ℕ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Fin.val_succ, pow_succ']
      ring
    have hrec : ∑ j : Fin d, u j.succ * b ^ (j : ℕ) < b ^ d :=
      ih (fun j => u j.succ) (fun j => hu j.succ)
    have hstep : ∑ j : Fin d, u j.succ * b ^ (j : ℕ) + 1 ≤ b ^ d := hrec
    simp only [Fin.val_zero, pow_zero, mul_one]
    rw [htail, pow_succ']
    calc
      u 0 + b * ∑ j : Fin d, u j.succ * b ^ (j : ℕ)
          < b + b * ∑ j : Fin d, u j.succ * b ^ (j : ℕ) := Nat.add_lt_add_right (hu 0) _
      _ = b * (∑ j : Fin d, u j.succ * b ^ (j : ℕ) + 1) := by ring
      _ ≤ b * b ^ d := Nat.mul_le_mul_left b hstep

private lemma base_digits_unique (d b : ℕ) (hb : 0 < b) (u v : Fin d → ℕ)
    (hu : ∀ j, u j < b) (hv : ∀ j, v j < b)
    (heq : ∑ j : Fin d, u j * b ^ (j : ℕ) = ∑ j : Fin d, v j * b ^ (j : ℕ)) :
    ∀ j, u j = v j := by
  induction d with
  | zero =>
    intro j
    exact Fin.elim0 j
  | succ d ih =>
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at heq
    have hu_tail : ∑ j : Fin d, u j.succ * b ^ (j.succ : ℕ) =
        b * ∑ j : Fin d, u j.succ * b ^ (j : ℕ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Fin.val_succ, pow_succ']
      ring
    have hv_tail : ∑ j : Fin d, v j.succ * b ^ (j.succ : ℕ) =
        b * ∑ j : Fin d, v j.succ * b ^ (j : ℕ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Fin.val_succ, pow_succ']
      ring
    simp only [Fin.val_zero, pow_zero, mul_one] at heq
    rw [hu_tail, hv_tail] at heq
    have hmod : u 0 = v 0 := by
      have h1 := congrArg (· % b) heq
      rwa [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt (hu 0), Nat.mod_eq_of_lt (hv 0)] at h1
    have htail_eq : ∑ j : Fin d, u j.succ * b ^ (j : ℕ) =
        ∑ j : Fin d, v j.succ * b ^ (j : ℕ) := by
      rw [hmod] at heq
      have hmul := Nat.add_left_cancel heq
      exact Nat.mul_left_cancel hb hmul
    have hsucc := ih (fun j => u j.succ) (fun j => v j.succ)
      (fun j => hu j.succ) (fun j => hv j.succ) htail_eq
    intro j
    refine Fin.cases hmod hsucc j

/-- Behrend's constructive 3-AP-free set on a sphere in `{0, ..., m-1}^d` encoded in base `2m - 1`. -/
theorem behrend_ap3_free (d m : ℕ) (hd : 1 ≤ d) (hm : 2 ≤ m) :
    ∃ B : Finset ℕ,
      (∀ x ∈ B, x < (2 * m - 1) ^ d) ∧
      (∀ x ∈ B, ∀ y ∈ B, ∀ z ∈ B, x + z = 2 * y → x = y ∧ y = z) ∧
      (m ^ d : ℝ) / ((d * (m - 1) ^ 2 + 1 : ℕ) : ℝ) ≤ (B.card : ℝ) := by
  let _ := hd
  let b : ℕ := 2 * m - 1
  have hb : 0 < b := by omega
  let evalBase : (Fin d → Fin m) → ℕ :=
    fun v => ∑ j : Fin d, (v j : ℕ) * b ^ (j : ℕ)
  let sqNorm : (Fin d → Fin m) → ℕ :=
    fun v => ∑ j : Fin d, (v j : ℕ) ^ 2
  have heval_lt : ∀ v : Fin d → Fin m, evalBase v < b ^ d := by
    intro v
    apply evalBase_lt d b (fun j => (v j : ℕ))
    intro j
    exact lt_of_lt_of_le (v j).isLt (by omega)
  have heval_inj : Function.Injective evalBase := by
    intro v₁ v₂ hv
    have hdigits := base_digits_unique d b hb (fun j => (v₁ j : ℕ)) (fun j => (v₂ j : ℕ))
      (fun j => lt_of_lt_of_le (v₁ j).isLt (by omega))
      (fun j => lt_of_lt_of_le (v₂ j).isLt (by omega)) hv
    funext j
    exact Fin.ext (hdigits j)
  let R : Finset ℕ := Finset.range (d * (m - 1) ^ 2 + 1)
  have hsq_mem : ∀ v : Fin d → Fin m, sqNorm v ∈ R := by
    intro v
    rw [Finset.mem_range, Nat.lt_succ_iff]
    calc
      sqNorm v = ∑ j : Fin d, (v j : ℕ) ^ 2 := rfl
      _ ≤ ∑ _j : Fin d, (m - 1) ^ 2 := by
        refine Finset.sum_le_sum fun j _ => ?_
        have hj : (v j : ℕ) ≤ m - 1 := Nat.le_sub_one_of_lt (v j).isLt
        exact Nat.pow_le_pow_left hj 2
      _ = d * (m - 1) ^ 2 := by simp
  have hsum_fibers : (∑ r ∈ R, ((Finset.univ.filter (fun v : Fin d → Fin m => sqNorm v = r)).card : ℝ)) =
      ((m ^ d : ℕ) : ℝ) := by
    have hnat : (Finset.univ : Finset (Fin d → Fin m)).card =
        ∑ r ∈ R, (Finset.univ.filter (fun v : Fin d → Fin m => sqNorm v = r)).card :=
      Finset.card_eq_sum_card_fiberwise (fun v _ => hsq_mem v)
    have hcard : (Finset.univ : Finset (Fin d → Fin m)).card = m ^ d := by
      simp
    rw [← hcard, hnat]
    push_cast
    rfl
  have hR_nonempty : R.Nonempty := ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩
  have hex_r : ∃ r ∈ R, (m ^ d : ℝ) / ((d * (m - 1) ^ 2 + 1 : ℕ) : ℝ) ≤
      ((Finset.univ.filter (fun v : Fin d → Fin m => sqNorm v = r)).card : ℝ) := by
    by_contra! hlt
    have hsum_lt : (∑ r ∈ R, ((Finset.univ.filter (fun v : Fin d → Fin m => sqNorm v = r)).card : ℝ)) <
        ∑ _r ∈ R, (m ^ d : ℝ) / ((d * (m - 1) ^ 2 + 1 : ℕ) : ℝ) :=
      Finset.sum_lt_sum_of_nonempty hR_nonempty hlt
    have hR_card : (R.card : ℝ) = ((d * (m - 1) ^ 2 + 1 : ℕ) : ℝ) := by
      simp [R]
    have hR_pos : ((d * (m - 1) ^ 2 + 1 : ℕ) : ℝ) ≠ 0 := by
      positivity
    rw [Finset.sum_const, nsmul_eq_mul, hR_card, mul_div_cancel₀ _ hR_pos] at hsum_lt
    rw [hsum_fibers] at hsum_lt
    push_cast at hsum_lt
    exact lt_irrefl _ hsum_lt
  rcases hex_r with ⟨r, _, hr_card⟩
  let F : Finset (Fin d → Fin m) := Finset.univ.filter (fun v => sqNorm v = r)
  let B : Finset ℕ := F.image evalBase
  refine ⟨B, ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨v, _, rfl⟩
    exact heval_lt v
  · intro x hx y hy z hz hap
    rcases Finset.mem_image.mp hx with ⟨v₁, hv₁, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨v₂, hv₂, rfl⟩
    rcases Finset.mem_image.mp hz with ⟨v₃, hv₃, rfl⟩
    have hsq₁ : sqNorm v₁ = r := (Finset.mem_filter.mp hv₁).2
    have hsq₂ : sqNorm v₂ = r := (Finset.mem_filter.mp hv₂).2
    have hsq₃ : sqNorm v₃ = r := (Finset.mem_filter.mp hv₃).2
    have hsum_eq : ∑ j : Fin d, ((v₁ j : ℕ) + (v₃ j : ℕ)) * b ^ (j : ℕ) =
        ∑ j : Fin d, (2 * (v₂ j : ℕ)) * b ^ (j : ℕ) := by
      calc
        ∑ j : Fin d, ((v₁ j : ℕ) + (v₃ j : ℕ)) * b ^ (j : ℕ)
            = evalBase v₁ + evalBase v₃ := by
          simp only [evalBase, add_mul, Finset.sum_add_distrib]
        _ = 2 * evalBase v₂ := hap
        _ = ∑ j : Fin d, (2 * (v₂ j : ℕ)) * b ^ (j : ℕ) := by
          simp only [evalBase, Finset.mul_sum, mul_assoc]
    have hdigits : ∀ j : Fin d, (v₁ j : ℕ) + (v₃ j : ℕ) = 2 * (v₂ j : ℕ) := by
      apply base_digits_unique d b hb _ _ _ _ hsum_eq
      · intro j
        have h1 : (v₁ j : ℕ) ≤ m - 1 := Nat.le_sub_one_of_lt (v₁ j).isLt
        have h3 : (v₃ j : ℕ) ≤ m - 1 := Nat.le_sub_one_of_lt (v₃ j).isLt
        omega
      · intro j
        have h2 : (v₂ j : ℕ) ≤ m - 1 := Nat.le_sub_one_of_lt (v₂ j).isLt
        omega
    have hpara_zero : (∑ j : Fin d, ((v₁ j : ℤ) - (v₃ j : ℤ)) ^ 2) = 0 := by
      have hterm : ∀ j : Fin d, ((v₁ j : ℤ) - (v₃ j : ℤ)) ^ 2 =
          2 * (v₁ j : ℤ) ^ 2 + 2 * (v₃ j : ℤ) ^ 2 - 4 * (v₂ j : ℤ) ^ 2 := by
        intro j
        have hj : (v₁ j : ℤ) + (v₃ j : ℤ) = 2 * (v₂ j : ℤ) := by
          exact_mod_cast hdigits j
        linear_combination (-(v₁ j : ℤ) - (v₃ j : ℤ) - 2 * (v₂ j : ℤ)) * hj
      calc
        ∑ j : Fin d, ((v₁ j : ℤ) - (v₃ j : ℤ)) ^ 2
            = ∑ j : Fin d, (2 * (v₁ j : ℤ) ^ 2 + 2 * (v₃ j : ℤ) ^ 2 - 4 * (v₂ j : ℤ) ^ 2) :=
          Finset.sum_congr rfl fun j _ => hterm j
        _ = 2 * (∑ j : Fin d, (v₁ j : ℤ) ^ 2) + 2 * (∑ j : Fin d, (v₃ j : ℤ) ^ 2) -
              4 * (∑ j : Fin d, (v₂ j : ℤ) ^ 2) := by
          simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
        _ = 2 * (r : ℤ) + 2 * (r : ℤ) - 4 * (r : ℤ) := by
          have hs1 : ∑ j : Fin d, (v₁ j : ℤ) ^ 2 = (r : ℤ) := by exact_mod_cast hsq₁
          have hs2 : ∑ j : Fin d, (v₂ j : ℤ) ^ 2 = (r : ℤ) := by exact_mod_cast hsq₂
          have hs3 : ∑ j : Fin d, (v₃ j : ℤ) ^ 2 = (r : ℤ) := by exact_mod_cast hsq₃
          rw [hs1, hs2, hs3]
        _ = 0 := by ring
    have hdiff_zero : ∀ j : Fin d, ((v₁ j : ℤ) - (v₃ j : ℤ)) ^ 2 = 0 := by
      have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ((v₁ j : ℤ) - (v₃ j : ℤ)))).mp hpara_zero
      intro j
      exact hall j (Finset.mem_univ j)
    have hv13 : v₁ = v₃ := by
      funext j
      have hsqz := sq_eq_zero_iff.mp (hdiff_zero j)
      have hz : (v₁ j : ℤ) = (v₃ j : ℤ) := sub_eq_zero.mp hsqz
      exact Fin.ext (by exact_mod_cast hz)
    have hv12 : v₁ = v₂ := by
      funext j
      have hj := hdigits j
      have h13 : (v₁ j : ℕ) = (v₃ j : ℕ) := congrArg Fin.val (congrFun hv13 j)
      exact Fin.ext (by omega)
    constructor
    · rw [hv12]
    · rw [← hv12, hv13]
  · rw [Finset.card_image_of_injective F heval_inj]
    simpa [F] using hr_card

/- ### 3. Ruzsa–Szemerédi Tripartite Triforce Hypergraph Identity -/

private lemma weightedTriforce_unif {α : Type*} [Fintype α] (q : ℝ) (W : α → α → α → ℝ) :
    weightedTriforce (fun _ => 1 / q) (fun _ => 1 / q) (fun _ => 1 / q) W =
      (1 / q) ^ 6 *
        ∑ u : α, ∑ v : α, ∑ w : α,
          ∑ u' : α, ∑ v' : α, ∑ w' : α,
            W u' v w * W u v' w * W u v w' := by
  simp only [weightedTriforce]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h12 :
      (∑ u' : α, W u' v w) * (∑ v' : α, W u v' w) =
        ∑ u' : α, ∑ v' : α, W u' v w * W u v' w := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun u' _ => Finset.mul_sum ..
  have h123 :
      (∑ u' : α, W u' v w) * (∑ v' : α, W u v' w) * (∑ w' : α, W u v w') =
        ∑ u' : α, ∑ v' : α, ∑ w' : α,
          W u' v w * W u v' w * W u v w' := by
    rw [h12, Finset.sum_mul]
    refine Finset.sum_congr rfl fun u' _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun v' _ => Finset.mul_sum ..
  calc
    (1 / q) * (1 / q) * (1 / q) *
        (∑ u' : α, (1 / q) * W u' v w) *
        (∑ v' : α, (1 / q) * W u v' w) *
        (∑ w' : α, (1 / q) * W u v w')
        = (1 / q) ^ 6 *
            ((∑ u' : α, W u' v w) * (∑ v' : α, W u v' w) * (∑ w' : α, W u v w')) := by
      simp only [← Finset.mul_sum]
      ring
    _ = (1 / q) ^ 6 *
          ∑ u' : α, ∑ v' : α, ∑ w' : α,
            W u' v w * W u v' w * W u v w' := by
      rw [h123]

/-- Exact edge density and triforce density of the Ruzsa–Szemerédi hypergraph from a 3-AP-free set. -/
theorem ruzsa_szemeredi_triforce_density (M : ℕ) (hM : 1 ≤ M) (B : Finset ℕ)
    (hBM : ∀ b ∈ B, b < M)
    (hAP : ∀ x ∈ B, ∀ y ∈ B, ∀ z ∈ B, x + z = 2 * y → x = y ∧ y = z) :
    let q := 2 * M - 1
    let _ : NeZero q := ⟨by omega⟩
    ∃ W : ZMod q → ZMod q → ZMod q → ℝ,
      (∀ u v w, W u v w = 0 ∨ W u v w = 1) ∧
      (∑ u : ZMod q, ∑ v : ZMod q, ∑ w : ZMod q,
        (1 / (q : ℝ)) * (1 / (q : ℝ)) * (1 / (q : ℝ)) * W u v w =
          (B.card : ℝ) / (q : ℝ) ^ 2) ∧
      weightedTriforce (fun _ => 1 / (q : ℝ)) (fun _ => 1 / (q : ℝ))
        (fun _ => 1 / (q : ℝ)) W = (B.card : ℝ) / (q : ℝ) ^ 5 := by
  intro q hq_nz
  have hq_ne : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  open scoped Classical in
  let inH : ZMod q → ZMod q → ZMod q → Prop :=
    fun u v w => ∃ b ∈ B, v = u + (b : ZMod q) ∧ w = u + 2 * (b : ZMod q)
  open scoped Classical in
  let W : ZMod q → ZMod q → ZMod q → ℝ :=
    fun u v w => if inH u v w then 1 else 0
  have hval_lt : ∀ b ∈ B, b < q := fun b hb => lt_of_lt_of_le (hBM b hb) (by omega)
  have hcast_inj : ∀ b₁ ∈ B, ∀ b₂ ∈ B, (b₁ : ZMod q) = (b₂ : ZMod q) → b₁ = b₂ := by
    intro b₁ hb₁ b₂ hb₂ heq
    have h1 : (b₁ : ZMod q).val = b₁ := ZMod.val_natCast_of_lt (hval_lt b₁ hb₁)
    have h2 : (b₂ : ZMod q).val = b₂ := ZMod.val_natCast_of_lt (hval_lt b₂ hb₂)
    rw [← h1, ← h2, heq]
  open scoped Classical in
  let H : Finset (ZMod q × ZMod q × ZMod q) :=
    Finset.univ.filter (fun t => inH t.1 t.2.1 t.2.2)
  have hH_eq : H = (Finset.univ ×ˢ B).image
      (fun p : ZMod q × ℕ => (p.1, p.1 + (p.2 : ZMod q), p.1 + 2 * (p.2 : ZMod q))) := by
    ext ⟨u, v, w⟩
    simp only [H, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Finset.mem_product, Prod.mk.injEq, inH]
    constructor
    · rintro ⟨b, hb, rfl, rfl⟩
      exact ⟨(u, b), hb, rfl, rfl, rfl⟩
    · rintro ⟨⟨u', b⟩, hb, rfl, rfl, rfl⟩
      exact ⟨b, hb, rfl, rfl⟩
  have hH_card : H.card = q * B.card := by
    rw [hH_eq, Finset.card_image_of_injOn]
    · rw [Finset.card_product, Finset.card_univ, ZMod.card q]
    · rintro ⟨u₁, b₁⟩ hp₁ ⟨u₂, b₂⟩ hp₂ heq
      simp only [Finset.coe_product, Finset.coe_univ, Set.mem_prod, Set.mem_univ,
        Finset.mem_coe, true_and] at hp₁ hp₂
      simp only [Prod.mk.injEq] at heq
      rcases heq with ⟨rfl, hv, _⟩
      have hb_eq : (b₁ : ZMod q) = (b₂ : ZMod q) := add_left_cancel hv
      exact Prod.ext rfl (hcast_inj b₁ hp₁ b₂ hp₂ hb_eq)
  have hW_sum : (∑ u : ZMod q, ∑ v : ZMod q, ∑ w : ZMod q, W u v w) = (H.card : ℝ) := by
    have h1 : (∑ u : ZMod q, ∑ v : ZMod q, ∑ w : ZMod q, W u v w) =
        ∑ t : ZMod q × ZMod q × ZMod q, if inH t.1 t.2.1 t.2.2 then (1 : ℝ) else 0 := by
      simp only [Fintype.sum_prod_type, W]
    rw [h1, Finset.sum_boole]
  open scoped Classical in
  let Tri : Finset ((ZMod q × ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q)) :=
    Finset.univ.filter (fun t =>
      inH t.2.1 t.1.2.1 t.1.2.2 ∧ inH t.1.1 t.2.2.1 t.1.2.2 ∧ inH t.1.1 t.1.2.1 t.2.2.2)
  have hTri_eq : Tri = (Finset.univ ×ˢ B).image
      (fun p : ZMod q × ℕ =>
        ((p.1, p.1 + (p.2 : ZMod q), p.1 + 2 * (p.2 : ZMod q)),
         (p.1, p.1 + (p.2 : ZMod q), p.1 + 2 * (p.2 : ZMod q)))) := by
    ext ⟨⟨u, v, w⟩, ⟨u', v', w'⟩⟩
    simp only [Tri, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Finset.mem_product, Prod.mk.injEq, inH]
    constructor
    · rintro ⟨⟨b₁, hb₁, hv₁, hw₁⟩, ⟨b₂, hb₂, hv₂, hw₂⟩, ⟨b₃, hb₃, hv₃, hw₃⟩⟩
      have hb1_eq : w - v = (b₁ : ZMod q) := by rw [hw₁, hv₁]; ring
      have hb2_eq : w - u = 2 * (b₂ : ZMod q) := by rw [hw₂]; ring
      have hb3_eq : v - u = (b₃ : ZMod q) := by rw [hv₃]; ring
      have hmod : ((b₁ + b₃ : ℕ) : ZMod q) = ((2 * b₂ : ℕ) : ZMod q) := by
        push_cast
        rw [← hb1_eq, ← hb3_eq, ← hb2_eq]
        ring
      have hlt13 : b₁ + b₃ < q := by
        have := hBM b₁ hb₁
        have := hBM b₃ hb₃
        omega
      have hlt2 : 2 * b₂ < q := by
        have := hBM b₂ hb₂
        omega
      have hap : b₁ + b₃ = 2 * b₂ := by
        have h1 := ZMod.val_natCast_of_lt hlt13
        have h2 := ZMod.val_natCast_of_lt hlt2
        rw [← h1, ← h2, hmod]
      rcases hAP b₁ hb₁ b₂ hb₂ b₃ hb₃ hap with ⟨rfl, rfl⟩
      refine ⟨(u, b₁), hb₁, ⟨rfl, hv₃.symm, hw₂.symm⟩, ⟨?_, hv₂.symm, hw₃.symm⟩⟩
      calc
        (u, b₁).1 = u := rfl
        _ = v - (b₁ : ZMod q) := by rw [hv₃]; ring
        _ = u' := by rw [hv₁]; ring
    · rintro ⟨⟨u₀, b⟩, hb, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩
      exact ⟨⟨b, hb, rfl, rfl⟩, ⟨b, hb, rfl, rfl⟩, ⟨b, hb, rfl, rfl⟩⟩
  have hTri_card : Tri.card = q * B.card := by
    rw [hTri_eq, Finset.card_image_of_injOn]
    · rw [Finset.card_product, Finset.card_univ, ZMod.card q]
    · rintro ⟨u₁, b₁⟩ hp₁ ⟨u₂, b₂⟩ hp₂ heq
      simp only [Finset.coe_product, Finset.coe_univ, Set.mem_prod, Set.mem_univ,
        Finset.mem_coe, true_and] at hp₁ hp₂
      simp only [Prod.mk.injEq] at heq
      rcases heq with ⟨⟨rfl, hv, _⟩, _⟩
      have hb_eq : (b₁ : ZMod q) = (b₂ : ZMod q) := add_left_cancel hv
      exact Prod.ext rfl (hcast_inj b₁ hp₁ b₂ hp₂ hb_eq)
  refine ⟨W, ?_, ?_, ?_⟩
  · intro u v w
    dsimp [W]
    split_ifs <;> simp
  · calc
      ∑ u : ZMod q, ∑ v : ZMod q, ∑ w : ZMod q,
          (1 / (q : ℝ)) * (1 / (q : ℝ)) * (1 / (q : ℝ)) * W u v w
          = (1 / (q : ℝ)) ^ 3 * ∑ u : ZMod q, ∑ v : ZMod q, ∑ w : ZMod q, W u v w := by
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun u _ =>
          Finset.sum_congr rfl fun v _ =>
            Finset.sum_congr rfl fun w _ => by ring
      _ = (1 / (q : ℝ)) ^ 3 * ((q : ℝ) * (B.card : ℝ)) := by
        rw [hW_sum, hH_card]
        push_cast
        rfl
      _ = (B.card : ℝ) / (q : ℝ) ^ 2 := by
        field_simp [hq_ne]
  · have htri_sum := weightedTriforce_unif (q : ℝ) W
    have htri_count :
        (∑ u : ZMod q, ∑ v : ZMod q, ∑ w : ZMod q,
          ∑ u' : ZMod q, ∑ v' : ZMod q, ∑ w' : ZMod q,
            W u' v w * W u v' w * W u v w') = (Tri.card : ℝ) := by
      have hterm : ∀ u v w u' v' w' : ZMod q,
          W u' v w * W u v' w * W u v w' =
            if inH u' v w ∧ inH u v' w ∧ inH u v w' then (1 : ℝ) else 0 := by
        intro u v w u' v' w'
        dsimp [W]
        by_cases h1 : inH u' v w <;> by_cases h2 : inH u v' w <;> by_cases h3 : inH u v w' <;>
          simp [h1, h2, h3]
      simp only [hterm]
      have hprod :
          (∑ u : ZMod q, ∑ v : ZMod q, ∑ w : ZMod q,
            ∑ u' : ZMod q, ∑ v' : ZMod q, ∑ w' : ZMod q,
              if inH u' v w ∧ inH u v' w ∧ inH u v w' then (1 : ℝ) else 0) =
          ∑ t : (ZMod q × ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q),
            if inH t.2.1 t.1.2.1 t.1.2.2 ∧ inH t.1.1 t.2.2.1 t.1.2.2 ∧
               inH t.1.1 t.1.2.1 t.2.2.2 then (1 : ℝ) else 0 := by
        simp only [Fintype.sum_prod_type]
      rw [hprod, Finset.sum_boole]
    rw [htri_sum, htri_count, hTri_card]
    push_cast
    rw [one_div, inv_pow, mul_comm ((q : ℝ) ^ 6)⁻¹, ← div_eq_mul_inv,
      show (q : ℝ) * (B.card : ℝ) = (B.card : ℝ) * (q : ℝ) by ring,
      show (q : ℝ) ^ 6 = (q : ℝ) ^ 5 * (q : ℝ) by ring, mul_div_mul_right _ _ hq_ne]

/- ### 4. Finite-Product Hoeffding Concentration and Random Corner Construction -/

private lemma hoeffding_oneD (μ t : ℝ) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    (1 - μ) * Real.exp (-t * μ) + μ * Real.exp (t * (1 - μ)) ≤ Real.exp (t ^ 2 / 8) := by
  by_cases h0 : μ = 0
  · subst h0
    simp only [sub_zero, one_mul, mul_zero, Real.exp_zero, zero_mul, add_zero]
    exact Real.one_le_exp (by positivity)
  by_cases h1 : μ = 1
  · subst h1
    simp only [sub_self, zero_mul, one_mul, mul_zero, Real.exp_zero, zero_add]
    exact Real.one_le_exp (by positivity)
  have hμ_pos : 0 < μ := lt_of_le_of_ne hμ0 (Ne.symm h0)
  have hμ_lt : μ < 1 := lt_of_le_of_ne hμ1 h1
  let D : ℝ → ℝ := fun s => (1 - μ) + μ * Real.exp s
  have hD_pos : ∀ s, 0 < D s := fun s => by
    have : 0 < μ * Real.exp s := mul_pos hμ_pos (Real.exp_pos s)
    linarith
  let p : ℝ → ℝ := fun s => (μ * Real.exp s) / D s
  have hp_nonneg : ∀ s, 0 ≤ p s := fun s =>
    div_nonneg (mul_nonneg hμ0 (Real.exp_pos s).le) (hD_pos s).le
  have hp_le_one : ∀ s, p s ≤ 1 := fun s => by
    rw [div_le_one (hD_pos s)]
    dsimp [D]
    linarith
  let φ : ℝ → ℝ := fun s => Real.log (D s) - μ * s - s ^ 2 / 8
  let ψ : ℝ → ℝ := fun s => p s - μ - s / 4
  have hD_deriv : ∀ s, HasDerivAt D (μ * Real.exp s) s := fun s => by
    simpa [D] using ((hasDerivAt_exp s).const_mul μ).const_add (1 - μ)
  have hφ_deriv : ∀ s, HasDerivAt φ (ψ s) s := fun s => by
    have hlog := (hD_deriv s).log (hD_pos s).ne'
    have hlin := (hasDerivAt_id s).const_mul μ
    have hsq := ((hasDerivAt_pow 2 s).div_const 8)
    have hsub := (hlog.fun_sub hlin).fun_sub hsq
    have hval : (μ * Real.exp s) / D s - μ * 1 - ((2 : ℕ) : ℝ) * s ^ (2 - 1) / 8 = ψ s := by
      dsimp [ψ, p]
      ring
    rw [hval] at hsub
    exact hsub
  have hp_deriv : ∀ s, HasDerivAt p (p s * (1 - p s)) s := fun s => by
    have hnum : HasDerivAt (fun x => μ * Real.exp x) (μ * Real.exp s) s :=
      (hasDerivAt_exp s).const_mul μ
    have hdiv := hnum.div (hD_deriv s) (hD_pos s).ne'
    have heq : (μ * Real.exp s * D s - μ * Real.exp s * (μ * Real.exp s)) / (D s) ^ 2 =
        p s * (1 - p s) := by
      dsimp [p]
      field_simp [(hD_pos s).ne']
    rwa [heq] at hdiv
  have hψ_deriv : ∀ s, HasDerivAt ψ (p s * (1 - p s) - 1 / 4) s := fun s => by
    have hlin := ((hasDerivAt_id s).div_const 4)
    have h := ((hp_deriv s).fun_sub (hasDerivAt_const s μ)).fun_sub hlin
    have hval : p s * (1 - p s) - 0 - 1 / 4 = p s * (1 - p s) - 1 / 4 := by ring
    rw [hval] at h
    exact h
  have hψ_anti : Antitone ψ := by
    apply antitone_of_deriv_nonpos
    · exact fun s => (hψ_deriv s).differentiableAt
    · intro s
      rw [(hψ_deriv s).deriv]
      nlinarith [sq_nonneg (p s - 1 / 2)]
  have hψ0 : ψ 0 = 0 := by
    simp [ψ, p, D]
  have hφ0 : φ 0 = 0 := by
    simp [φ, D]
  have hφ_nonpos : φ t ≤ 0 := by
    have hφ_diff : Differentiable ℝ φ := fun s => (hφ_deriv s).differentiableAt
    rcases le_total t 0 with ht | ht
    · have hmono : MonotoneOn φ (Set.Iic 0) := by
        apply monotoneOn_of_deriv_nonneg (convex_Iic 0) hφ_diff.continuous.continuousOn
          hφ_diff.differentiableOn
        intro x hx
        rw [(hφ_deriv x).deriv]
        have hx0 : x ≤ 0 := by
          rw [interior_Iic] at hx
          exact hx.le
        rw [← hψ0]
        exact hψ_anti hx0
      rw [← hφ0]
      exact hmono ht (Set.mem_Iic.mpr le_rfl) ht
    · have hanti : AntitoneOn φ (Set.Ici 0) := by
        apply antitoneOn_of_deriv_nonpos (convex_Ici 0) hφ_diff.continuous.continuousOn
          hφ_diff.differentiableOn
        intro x hx
        rw [(hφ_deriv x).deriv]
        have hx0 : 0 ≤ x := by
          rw [interior_Ici] at hx
          exact hx.le
        rw [← hψ0]
        exact hψ_anti hx0
      rw [← hφ0]
      exact hanti (Set.mem_Ici.mpr le_rfl) ht ht
  have hlog_le : Real.log (D t) ≤ μ * t + t ^ 2 / 8 := by
    dsimp [φ] at hφ_nonpos
    linarith
  have hD_le : D t ≤ Real.exp (μ * t + t ^ 2 / 8) := by
    calc
      D t = Real.exp (Real.log (D t)) := (Real.exp_log (hD_pos t)).symm
      _ ≤ Real.exp (μ * t + t ^ 2 / 8) := Real.exp_le_exp.mpr hlog_le
  have hmul := mul_le_mul_of_nonneg_left hD_le (Real.exp_pos (-t * μ)).le
  calc
    (1 - μ) * Real.exp (-t * μ) + μ * Real.exp (t * (1 - μ))
        = Real.exp (-t * μ) * ((1 - μ) + μ * Real.exp t) := by
      have hexp : Real.exp (-t * μ) * Real.exp t = Real.exp (t * (1 - μ)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [mul_add, ← mul_assoc, mul_comm (Real.exp (-t * μ)) μ, mul_assoc, hexp]
      ring
    _ = Real.exp (-t * μ) * D t := rfl
    _ ≤ Real.exp (-t * μ) * Real.exp (μ * t + t ^ 2 / 8) := hmul
    _ = Real.exp (t ^ 2 / 8) := by
      rw [← Real.exp_add]
      congr 1
      ring

private def DependsOnlyOn {Idx A α : Type*} (K : Finset Idx) (F : (Idx → A) → α) : Prop :=
  ∀ ω₁ ω₂ : Idx → A, (∀ i ∈ K, ω₁ i = ω₂ i) → F ω₁ = F ω₂

private lemma dependsOnlyOn_mul {Idx A : Type*} [DecidableEq Idx] {K₁ K₂ : Finset Idx}
    {F G : (Idx → A) → ℝ} (hF : DependsOnlyOn K₁ F) (hG : DependsOnlyOn K₂ G) :
    DependsOnlyOn (K₁ ∪ K₂) (fun ω => F ω * G ω) := by
  intro ω₁ ω₂ hω
  dsimp only
  have h1 : F ω₁ = F ω₂ := hF ω₁ ω₂ (fun i hi => hω i (Finset.mem_union_left K₂ hi))
  have h2 : G ω₁ = G ω₂ := hG ω₁ ω₂ (fun i hi => hω i (Finset.mem_union_right K₁ hi))
  rw [h1, h2]

private lemma dependsOnlyOn_prod {Idx A β : Type*} [DecidableEq Idx]
    (T : Finset β) (S : β → Finset Idx) (f : β → (Idx → A) → ℝ)
    (hf : ∀ b ∈ T, DependsOnlyOn (S b) (f b)) :
    DependsOnlyOn (T.biUnion S) (fun ω => ∏ b ∈ T, f b ω) := by
  intro ω₁ ω₂ hω
  refine Finset.prod_congr rfl fun b hb => ?_
  exact hf b hb ω₁ ω₂ (fun i hi => hω i (Finset.mem_biUnion.mpr ⟨b, hb, hi⟩))

private lemma sum_mul_eq_of_disjoint_support {Idx A : Type*}
    [Fintype Idx] [DecidableEq Idx] [Fintype A] [Nonempty A]
    (K₁ K₂ : Finset Idx) (hdisj : Disjoint K₁ K₂)
    (F G : (Idx → A) → ℝ) (hF : DependsOnlyOn K₁ F) (hG : DependsOnlyOn K₂ G) :
    (∑ ω : Idx → A, F ω * G ω) * (Fintype.card (Idx → A) : ℝ) =
      (∑ ω : Idx → A, F ω) * (∑ ω : Idx → A, G ω) := by
  open scoped Classical in
  let a₀ : A := Classical.arbitrary A
  let e : (Idx → A) ≃ ({i : Idx // i ∈ K₁} → A) × ({i : Idx // i ∉ K₁} → A) :=
    Equiv.piEquivPiSubtypeProd (fun i => i ∈ K₁) (fun _ => A)
  let ext₁ : ({i : Idx // i ∈ K₁} → A) → (Idx → A) :=
    fun ω₁ i => if hi : i ∈ K₁ then ω₁ ⟨i, hi⟩ else a₀
  let ext₂ : ({i : Idx // i ∉ K₁} → A) → (Idx → A) :=
    fun ω₂ i => if hi : i ∉ K₁ then ω₂ ⟨i, hi⟩ else a₀
  have hF_ext : ∀ (ω₁ : {i : Idx // i ∈ K₁} → A) (ω₂ : {i : Idx // i ∉ K₁} → A),
      F (e.symm (ω₁, ω₂)) = F (ext₁ ω₁) := by
    intro ω₁ ω₂
    refine hF _ _ fun i hi => ?_
    simp [e, ext₁, hi]
  have hG_ext : ∀ (ω₁ : {i : Idx // i ∈ K₁} → A) (ω₂ : {i : Idx // i ∉ K₁} → A),
      G (e.symm (ω₁, ω₂)) = G (ext₂ ω₂) := by
    intro ω₁ ω₂
    refine hG _ _ fun i hi => ?_
    have hi1 : i ∉ K₁ := Finset.disjoint_right.mp hdisj hi
    simp [e, ext₂, hi1]
  have hsum_FG :
      (∑ ω : Idx → A, F ω * G ω) =
        (∑ ω₁ : {i : Idx // i ∈ K₁} → A, F (ext₁ ω₁)) *
          (∑ ω₂ : {i : Idx // i ∉ K₁} → A, G (ext₂ ω₂)) := by
    rw [← Equiv.sum_comp e.symm]
    rw [Fintype.sum_prod_type]
    simp_rw [hF_ext, hG_ext]
    rw [Finset.sum_mul_sum]
  have hsum_F :
      (∑ ω : Idx → A, F ω) =
        (∑ ω₁ : {i : Idx // i ∈ K₁} → A, F (ext₁ ω₁)) *
          (Fintype.card ({i : Idx // i ∉ K₁} → A) : ℝ) := by
    rw [← Equiv.sum_comp e.symm]
    rw [Fintype.sum_prod_type]
    simp_rw [hF_ext]
    simp_rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← Finset.mul_sum, mul_comm]
  have hsum_G :
      (∑ ω : Idx → A, G ω) =
        (Fintype.card ({i : Idx // i ∈ K₁} → A) : ℝ) *
          (∑ ω₂ : {i : Idx // i ∉ K₁} → A, G (ext₂ ω₂)) := by
    rw [← Equiv.sum_comp e.symm]
    rw [Fintype.sum_prod_type]
    simp_rw [hG_ext]
    simp_rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard :
      (Fintype.card (Idx → A) : ℝ) =
        (Fintype.card ({i : Idx // i ∈ K₁} → A) : ℝ) *
          (Fintype.card ({i : Idx // i ∉ K₁} → A) : ℝ) := by
    have hc := Fintype.card_congr e
    rw [Fintype.card_prod] at hc
    exact_mod_cast hc
  rw [hsum_FG, hsum_F, hsum_G, hcard]
  ring

private lemma sum_prod_div_card_eq_of_pairwiseDisjoint {Idx A β : Type*}
    [Fintype Idx] [DecidableEq Idx] [Fintype A] [Nonempty A] [DecidableEq β]
    (T : Finset β) (S : β → Finset Idx) (f : β → (Idx → A) → ℝ)
    (hf : ∀ b ∈ T, DependsOnlyOn (S b) (f b))
    (hdisj : ∀ b₁ ∈ T, ∀ b₂ ∈ T, b₁ ≠ b₂ → Disjoint (S b₁) (S b₂)) :
    (∑ ω : Idx → A, ∏ b ∈ T, f b ω) / (Fintype.card (Idx → A) : ℝ) =
      ∏ b ∈ T, ((∑ ω : Idx → A, f b ω) / (Fintype.card (Idx → A) : ℝ)) := by
  have hcard_ne : (Fintype.card (Idx → A) : ℝ) ≠ 0 := by positivity
  induction T using Finset.induction_on with
  | empty =>
    simp
  | @insert b₀ T hb₀ ih =>
    have hfT : ∀ b ∈ T, DependsOnlyOn (S b) (f b) := fun b hb =>
      hf b (Finset.mem_insert_of_mem hb)
    have hdisjT : ∀ b₁ ∈ T, ∀ b₂ ∈ T, b₁ ≠ b₂ → Disjoint (S b₁) (S b₂) :=
      fun b₁ hb₁ b₂ hb₂ hne =>
        hdisj b₁ (Finset.mem_insert_of_mem hb₁) b₂ (Finset.mem_insert_of_mem hb₂) hne
    have hdisj_b₀ : Disjoint (S b₀) (T.biUnion S) := by
      rw [Finset.disjoint_biUnion_right]
      intro b hb
      exact hdisj b₀ (Finset.mem_insert_self b₀ T) b (Finset.mem_insert_of_mem hb)
        (fun heq => hb₀ (heq ▸ hb))
    have hprod_dep : DependsOnlyOn (T.biUnion S) (fun ω => ∏ b ∈ T, f b ω) :=
      dependsOnlyOn_prod T S f hfT
    have hsplit := sum_mul_eq_of_disjoint_support (S b₀) (T.biUnion S) hdisj_b₀
      (f b₀) (fun ω => ∏ b ∈ T, f b ω) (hf b₀ (Finset.mem_insert_self b₀ T)) hprod_dep
    simp_rw [Finset.prod_insert hb₀]
    have hmul : (∑ ω : Idx → A, f b₀ ω * ∏ b ∈ T, f b ω) / (Fintype.card (Idx → A) : ℝ) =
        ((∑ ω : Idx → A, f b₀ ω) / (Fintype.card (Idx → A) : ℝ)) *
          ((∑ ω : Idx → A, ∏ b ∈ T, f b ω) / (Fintype.card (Idx → A) : ℝ)) := by
      rw [div_mul_div_comm, ← hsplit]
      field_simp [hcard_ne]
    rw [hmul, ih hfT hdisjT]

private lemma finite_product_hoeffding_mgf {Idx A β : Type*}
    [Fintype Idx] [DecidableEq Idx] [Fintype A] [Nonempty A] [DecidableEq β]
    (T : Finset β) (S : β → Finset Idx) (E : β → (Idx → A) → ℝ) (μ t : ℝ)
    (hE_dep : ∀ b ∈ T, DependsOnlyOn (S b) (E b))
    (hdisj : ∀ b₁ ∈ T, ∀ b₂ ∈ T, b₁ ≠ b₂ → Disjoint (S b₁) (S b₂))
    (hE_bool : ∀ b ∈ T, ∀ ω : Idx → A, E b ω = 0 ∨ E b ω = 1)
    (hE_mean : ∀ b ∈ T, (∑ ω : Idx → A, E b ω) / (Fintype.card (Idx → A) : ℝ) = μ) :
    (∑ ω : Idx → A, Real.exp (t * ∑ b ∈ T, (E b ω - μ))) / (Fintype.card (Idx → A) : ℝ) ≤
      Real.exp ((T.card : ℝ) * t ^ 2 / 8) := by
  have hcard_pos : (0 : ℝ) < (Fintype.card (Idx → A) : ℝ) := by positivity
  have hexp_eq : ∀ ω : Idx → A,
      Real.exp (t * ∑ b ∈ T, (E b ω - μ)) = ∏ b ∈ T, Real.exp (t * (E b ω - μ)) := by
    intro ω
    rw [Finset.mul_sum, Real.exp_sum]
  simp_rw [hexp_eq]
  have hf_dep : ∀ b ∈ T, DependsOnlyOn (S b) (fun ω => Real.exp (t * (E b ω - μ))) := by
    intro b hb ω₁ ω₂ hω
    dsimp only
    rw [hE_dep b hb ω₁ ω₂ hω]
  rw [sum_prod_div_card_eq_of_pairwiseDisjoint T S (fun b ω => Real.exp (t * (E b ω - μ)))
    hf_dep hdisj]
  have hsingle : ∀ b ∈ T,
      (∑ ω : Idx → A, Real.exp (t * (E b ω - μ))) / (Fintype.card (Idx → A) : ℝ) ≤
        Real.exp (t ^ 2 / 8) := by
    intro b hb
    open scoped Classical in
    let Ω₁ : Finset (Idx → A) := Finset.univ.filter (fun ω => E b ω = 1)
    open scoped Classical in
    let Ω₀ : Finset (Idx → A) := Finset.univ.filter (fun ω => E b ω = 0)
    have hpart : Ω₁ ∪ Ω₀ = Finset.univ := by
      ext ω
      simp only [Ω₁, Ω₀, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro _; trivial
      · intro _; exact (hE_bool b hb ω).symm
    have hdisj_Ω : Disjoint Ω₁ Ω₀ := by
      rw [Finset.disjoint_left]
      intro ω h1 h0
      simp only [Ω₁, Finset.mem_filter] at h1
      simp only [Ω₀, Finset.mem_filter] at h0
      linarith
    have hcard_sum : (Ω₁.card : ℝ) + (Ω₀.card : ℝ) = (Fintype.card (Idx → A) : ℝ) := by
      have hnat : Ω₁.card + Ω₀.card = Fintype.card (Idx → A) := by
        rw [← Finset.card_union_of_disjoint hdisj_Ω, hpart, Finset.card_univ]
      exact_mod_cast hnat
    have hsum_E : (∑ ω : Idx → A, E b ω) = (Ω₁.card : ℝ) := by
      rw [← hpart, Finset.sum_union hdisj_Ω]
      have hs1 : ∑ ω ∈ Ω₁, E b ω = (Ω₁.card : ℝ) := by
        calc
          ∑ ω ∈ Ω₁, E b ω = ∑ _ω ∈ Ω₁, (1 : ℝ) :=
            Finset.sum_congr rfl fun ω hω => (Finset.mem_filter.mp hω).2
          _ = (Ω₁.card : ℝ) := by simp
      have hs0 : ∑ ω ∈ Ω₀, E b ω = 0 := by
        calc
          ∑ ω ∈ Ω₀, E b ω = ∑ _ω ∈ Ω₀, (0 : ℝ) :=
            Finset.sum_congr rfl fun ω hω => (Finset.mem_filter.mp hω).2
          _ = 0 := by simp
      rw [hs1, hs0, add_zero]
    have hμ_eq : (Ω₁.card : ℝ) / (Fintype.card (Idx → A) : ℝ) = μ := by
      rw [← hsum_E]
      exact hE_mean b hb
    have h1μ_eq : (Ω₀.card : ℝ) / (Fintype.card (Idx → A) : ℝ) = 1 - μ := by
      rw [← hμ_eq]
      have : (Ω₁.card : ℝ) + (Ω₀.card : ℝ) = (Fintype.card (Idx → A) : ℝ) := hcard_sum
      field_simp [hcard_pos.ne']
      linarith
    have hμ0 : 0 ≤ μ := by rw [← hμ_eq]; positivity
    have hμ1 : μ ≤ 1 := by
      have : 0 ≤ 1 - μ := by rw [← h1μ_eq]; positivity
      linarith
    have hsum_exp :
        (∑ ω : Idx → A, Real.exp (t * (E b ω - μ))) =
          (Ω₀.card : ℝ) * Real.exp (-t * μ) + (Ω₁.card : ℝ) * Real.exp (t * (1 - μ)) := by
      rw [← hpart, Finset.sum_union hdisj_Ω, add_comm]
      have hs1 : ∑ ω ∈ Ω₁, Real.exp (t * (E b ω - μ)) =
          (Ω₁.card : ℝ) * Real.exp (t * (1 - μ)) := by
        calc
          ∑ ω ∈ Ω₁, Real.exp (t * (E b ω - μ)) = ∑ _ω ∈ Ω₁, Real.exp (t * (1 - μ)) :=
            Finset.sum_congr rfl fun ω hω => by rw [(Finset.mem_filter.mp hω).2]
          _ = (Ω₁.card : ℝ) * Real.exp (t * (1 - μ)) := by simp
      have hs0 : ∑ ω ∈ Ω₀, Real.exp (t * (E b ω - μ)) =
          (Ω₀.card : ℝ) * Real.exp (-t * μ) := by
        calc
          ∑ ω ∈ Ω₀, Real.exp (t * (E b ω - μ)) = ∑ _ω ∈ Ω₀, Real.exp (-t * μ) :=
            Finset.sum_congr rfl fun ω hω => by
              rw [(Finset.mem_filter.mp hω).2]
              ring_nf
          _ = (Ω₀.card : ℝ) * Real.exp (-t * μ) := by simp
      rw [hs1, hs0]
    rw [hsum_exp, add_div, mul_div_right_comm, mul_div_right_comm, h1μ_eq, hμ_eq]
    exact hoeffding_oneD μ t hμ0 hμ1
  calc
    ∏ b ∈ T, (∑ ω : Idx → A, Real.exp (t * (E b ω - μ))) / (Fintype.card (Idx → A) : ℝ)
        ≤ ∏ _b ∈ T, Real.exp (t ^ 2 / 8) := by
      refine Finset.prod_le_prod (fun b _ => by positivity) (fun b hb => hsingle b hb)
    _ = (Real.exp (t ^ 2 / 8)) ^ T.card := by simp
    _ = Real.exp ((T.card : ℝ) * t ^ 2 / 8) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

private lemma finite_product_hoeffding_upper {Idx A β : Type*}
    [Fintype Idx] [DecidableEq Idx] [Fintype A] [Nonempty A] [DecidableEq β]
    (T : Finset β) (S : β → Finset Idx) (E : β → (Idx → A) → ℝ) (μ ε : ℝ) (hε : 0 ≤ ε)
    (hE_dep : ∀ b ∈ T, DependsOnlyOn (S b) (E b))
    (hdisj : ∀ b₁ ∈ T, ∀ b₂ ∈ T, b₁ ≠ b₂ → Disjoint (S b₁) (S b₂))
    (hE_bool : ∀ b ∈ T, ∀ ω : Idx → A, E b ω = 0 ∨ E b ω = 1)
    (hE_mean : ∀ b ∈ T, (∑ ω : Idx → A, E b ω) / (Fintype.card (Idx → A) : ℝ) = μ) :
    open scoped Classical in
    ((Finset.univ.filter (fun ω : Idx → A => (μ + ε) * (T.card : ℝ) ≤ ∑ b ∈ T, E b ω)).card : ℝ) /
        (Fintype.card (Idx → A) : ℝ) ≤
      Real.exp (-2 * ε ^ 2 * (T.card : ℝ)) := by
  open scoped Classical in
  let Bad := Finset.univ.filter (fun ω : Idx → A => (μ + ε) * (T.card : ℝ) ≤ ∑ b ∈ T, E b ω)
  have hcard_pos : (0 : ℝ) < (Fintype.card (Idx → A) : ℝ) := by positivity
  let t : ℝ := 4 * ε
  have hmgf := finite_product_hoeffding_mgf T S E μ t hE_dep hdisj hE_bool hE_mean
  have hbad_le : (Bad.card : ℝ) * Real.exp (4 * ε ^ 2 * (T.card : ℝ)) ≤
      ∑ ω : Idx → A, Real.exp (t * ∑ b ∈ T, (E b ω - μ)) := by
    calc
      (Bad.card : ℝ) * Real.exp (4 * ε ^ 2 * (T.card : ℝ))
          = ∑ _ω ∈ Bad, Real.exp (4 * ε ^ 2 * (T.card : ℝ)) := by simp
      _ ≤ ∑ ω ∈ Bad, Real.exp (t * ∑ b ∈ T, (E b ω - μ)) := by
        refine Finset.sum_le_sum fun ω hω => Real.exp_le_exp.mpr ?_
        have hbadω : (μ + ε) * (T.card : ℝ) ≤ ∑ b ∈ T, E b ω :=
          (Finset.mem_filter.mp hω).2
        have hsub : ε * (T.card : ℝ) ≤ ∑ b ∈ T, (E b ω - μ) := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
          linarith
        have ht0 : 0 ≤ t := by dsimp [t]; linarith
        calc
          4 * ε ^ 2 * (T.card : ℝ) = t * (ε * (T.card : ℝ)) := by dsimp [t]; ring
          _ ≤ t * ∑ b ∈ T, (E b ω - μ) := mul_le_mul_of_nonneg_left hsub ht0
      _ ≤ ∑ ω : Idx → A, Real.exp (t * ∑ b ∈ T, (E b ω - μ)) :=
        Finset.sum_le_univ_sum_of_nonneg (fun ω => (Real.exp_pos _).le)
  have hexp_pos : 0 < Real.exp (4 * ε ^ 2 * (T.card : ℝ)) := Real.exp_pos _
  have hdiv : (Bad.card : ℝ) / (Fintype.card (Idx → A) : ℝ) * Real.exp (4 * ε ^ 2 * (T.card : ℝ)) ≤
      Real.exp ((T.card : ℝ) * t ^ 2 / 8) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hcard_pos]
    calc
      (Bad.card : ℝ) * Real.exp (4 * ε ^ 2 * (T.card : ℝ))
          ≤ ∑ ω : Idx → A, Real.exp (t * ∑ b ∈ T, (E b ω - μ)) := hbad_le
      _ ≤ Real.exp ((T.card : ℝ) * t ^ 2 / 8) * (Fintype.card (Idx → A) : ℝ) :=
        (div_le_iff₀ hcard_pos).mp hmgf
  calc
    (Bad.card : ℝ) / (Fintype.card (Idx → A) : ℝ)
        ≤ Real.exp ((T.card : ℝ) * t ^ 2 / 8) / Real.exp (4 * ε ^ 2 * (T.card : ℝ)) :=
      (le_div_iff₀ hexp_pos).mpr hdiv
    _ = Real.exp (-2 * ε ^ 2 * (T.card : ℝ)) := by
      rw [← Real.exp_sub]
      congr 1
      dsimp [t]
      ring

private lemma finite_product_hoeffding_lower {Idx A β : Type*}
    [Fintype Idx] [DecidableEq Idx] [Fintype A] [Nonempty A] [DecidableEq β]
    (T : Finset β) (S : β → Finset Idx) (E : β → (Idx → A) → ℝ) (μ ε : ℝ) (hε : 0 ≤ ε)
    (hE_dep : ∀ b ∈ T, DependsOnlyOn (S b) (E b))
    (hdisj : ∀ b₁ ∈ T, ∀ b₂ ∈ T, b₁ ≠ b₂ → Disjoint (S b₁) (S b₂))
    (hE_bool : ∀ b ∈ T, ∀ ω : Idx → A, E b ω = 0 ∨ E b ω = 1)
    (hE_mean : ∀ b ∈ T, (∑ ω : Idx → A, E b ω) / (Fintype.card (Idx → A) : ℝ) = μ) :
    open scoped Classical in
    ((Finset.univ.filter (fun ω : Idx → A => ∑ b ∈ T, E b ω ≤ (μ - ε) * (T.card : ℝ))).card : ℝ) /
        (Fintype.card (Idx → A) : ℝ) ≤
      Real.exp (-2 * ε ^ 2 * (T.card : ℝ)) := by
  open scoped Classical in
  let Bad := Finset.univ.filter (fun ω : Idx → A => ∑ b ∈ T, E b ω ≤ (μ - ε) * (T.card : ℝ))
  have hcard_pos : (0 : ℝ) < (Fintype.card (Idx → A) : ℝ) := by positivity
  let t : ℝ := -(4 * ε)
  have hmgf := finite_product_hoeffding_mgf T S E μ t hE_dep hdisj hE_bool hE_mean
  have hbad_le : (Bad.card : ℝ) * Real.exp (4 * ε ^ 2 * (T.card : ℝ)) ≤
      ∑ ω : Idx → A, Real.exp (t * ∑ b ∈ T, (E b ω - μ)) := by
    calc
      (Bad.card : ℝ) * Real.exp (4 * ε ^ 2 * (T.card : ℝ))
          = ∑ _ω ∈ Bad, Real.exp (4 * ε ^ 2 * (T.card : ℝ)) := by simp
      _ ≤ ∑ ω ∈ Bad, Real.exp (t * ∑ b ∈ T, (E b ω - μ)) := by
        refine Finset.sum_le_sum fun ω hω => Real.exp_le_exp.mpr ?_
        have hbadω : ∑ b ∈ T, E b ω ≤ (μ - ε) * (T.card : ℝ) :=
          (Finset.mem_filter.mp hω).2
        have hsub : ∑ b ∈ T, (E b ω - μ) ≤ -(ε * (T.card : ℝ)) := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
          linarith
        have ht0 : t ≤ 0 := by dsimp [t]; linarith
        calc
          4 * ε ^ 2 * (T.card : ℝ) = t * (-(ε * (T.card : ℝ))) := by dsimp [t]; ring
          _ ≤ t * ∑ b ∈ T, (E b ω - μ) := mul_le_mul_of_nonpos_left hsub ht0
      _ ≤ ∑ ω : Idx → A, Real.exp (t * ∑ b ∈ T, (E b ω - μ)) :=
        Finset.sum_le_univ_sum_of_nonneg (fun ω => (Real.exp_pos _).le)
  have hexp_pos : 0 < Real.exp (4 * ε ^ 2 * (T.card : ℝ)) := Real.exp_pos _
  have hdiv : (Bad.card : ℝ) / (Fintype.card (Idx → A) : ℝ) * Real.exp (4 * ε ^ 2 * (T.card : ℝ)) ≤
      Real.exp ((T.card : ℝ) * t ^ 2 / 8) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hcard_pos]
    calc
      (Bad.card : ℝ) * Real.exp (4 * ε ^ 2 * (T.card : ℝ))
          ≤ ∑ ω : Idx → A, Real.exp (t * ∑ b ∈ T, (E b ω - μ)) := hbad_le
      _ ≤ Real.exp ((T.card : ℝ) * t ^ 2 / 8) * (Fintype.card (Idx → A) : ℝ) :=
        (div_le_iff₀ hcard_pos).mp hmgf
  calc
    (Bad.card : ℝ) / (Fintype.card (Idx → A) : ℝ)
        ≤ Real.exp ((T.card : ℝ) * t ^ 2 / 8) / Real.exp (4 * ε ^ 2 * (T.card : ℝ)) :=
      (le_div_iff₀ hexp_pos).mpr hdiv
    _ = Real.exp (-2 * ε ^ 2 * (T.card : ℝ)) := by
      rw [← Real.exp_sub]
      congr 1
      dsimp [t]
      ring

private lemma sum_eval_inj_div_card {Idx A : Type*} [Fintype Idx] [DecidableEq Idx]
    [Fintype A] [Nonempty A] {k : ℕ} (κ : Fin k → Idx) (hκ : Function.Injective κ)
    (Φ : (Fin k → A) → ℝ) :
    (∑ ω : Idx → A, Φ (fun j => ω (κ j))) / (Fintype.card (Idx → A) : ℝ) =
      (∑ v : Fin k → A, Φ v) / (Fintype.card A : ℝ) ^ k := by
  let S : Finset Idx := Finset.univ.image κ
  have heS_bij : Function.Bijective
      (fun j : Fin k => (⟨κ j, Finset.mem_image_of_mem κ (Finset.mem_univ j)⟩ : {i : Idx // i ∈ S})) := by
    constructor
    · intro j₁ j₂ heq
      apply hκ
      exact congrArg Subtype.val heq
    · rintro ⟨i, hi⟩
      rcases Finset.mem_image.mp hi with ⟨j, _, rfl⟩
      exact ⟨j, rfl⟩
  let eS : Fin k ≃ {i : Idx // i ∈ S} := Equiv.ofBijective _ heS_bij
  let eSplit : (Idx → A) ≃ ({i : Idx // i ∈ S} → A) × ({i : Idx // i ∉ S} → A) :=
    Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) (fun _ => A)
  let eArrow : ({i : Idx // i ∈ S} → A) ≃ (Fin k → A) :=
    Equiv.arrowCongr eS.symm (Equiv.refl A)
  let eIdx : (Idx → A) ≃ (Fin k → A) × ({i : Idx // i ∉ S} → A) :=
    eSplit.trans (Equiv.prodCongr eArrow (Equiv.refl _))
  have heval : ∀ (v : Fin k → A) (ω_out : {i : Idx // i ∉ S} → A) (j : Fin k),
      (eIdx.symm (v, ω_out)) (κ j) = v j := by
    intro v ω_out j
    have hmem : κ j ∈ S := Finset.mem_image_of_mem κ (Finset.mem_univ j)
    have heq : (⟨κ j, hmem⟩ : {i : Idx // i ∈ S}) = eS j := rfl
    change (eSplit.symm (eArrow.symm v, ω_out)) (κ j) = v j
    simp only [eSplit, Equiv.piEquivPiSubtypeProd_symm_apply, hmem, ↓reduceDIte]
    have ha : eArrow.symm v ⟨κ j, hmem⟩ = v (eS.symm ⟨κ j, hmem⟩) := rfl
    rw [ha, heq, eS.symm_apply_apply]
  have hsum : (∑ ω : Idx → A, Φ (fun j => ω (κ j))) =
      (∑ v : Fin k → A, Φ v) * (Fintype.card ({i : Idx // i ∉ S} → A) : ℝ) := by
    rw [← Equiv.sum_comp eIdx.symm]
    rw [Fintype.sum_prod_type]
    have hconst : ∀ v : Fin k → A,
        (∑ ω_out : {i : Idx // i ∉ S} → A, Φ (fun j => (eIdx.symm (v, ω_out)) (κ j))) =
          Φ v * (Fintype.card ({i : Idx // i ∉ S} → A) : ℝ) := by
      intro v
      calc
        ∑ ω_out : {i : Idx // i ∉ S} → A, Φ (fun j => (eIdx.symm (v, ω_out)) (κ j))
            = ∑ _ω_out : {i : Idx // i ∉ S} → A, Φ v := by
          refine Finset.sum_congr rfl fun ω_out _ => ?_
          congr 1
          funext j
          exact heval v ω_out j
        _ = Φ v * (Fintype.card ({i : Idx // i ∉ S} → A) : ℝ) := by
          simp [mul_comm]
    simp_rw [hconst, ← Finset.sum_mul]
  have hcard : (Fintype.card (Idx → A) : ℝ) =
      (Fintype.card A : ℝ) ^ k * (Fintype.card ({i : Idx // i ∉ S} → A) : ℝ) := by
    have hc := Fintype.card_congr eIdx
    have hfk : Fintype.card (Fin k → A) = Fintype.card A ^ k := by simp
    rw [Fintype.card_prod, hfk] at hc
    exact_mod_cast hc
  have hrest_ne : (Fintype.card ({i : Idx // i ∉ S} → A) : ℝ) ≠ 0 := by positivity
  rw [hsum, hcard]
  field_simp [hrest_ne]

private lemma exists_max_indep {α : Type*} [Fintype α] [DecidableEq α]
    (Conflict : α → α → Prop) [DecidableRel Conflict]
    (hRefl : ∀ x, Conflict x x)
    (hSymm : ∀ x y, Conflict x y → Conflict y x)
    (M : ℕ) (hDeg : ∀ y, (Finset.univ.filter (fun x => Conflict x y)).card ≤ M) :
    ∃ Q : Finset α,
      (∀ a ∈ Q, ∀ b ∈ Q, a ≠ b → ¬ Conflict a b) ∧
      Fintype.card α ≤ Q.card * M := by
  open scoped Classical in
  let Indep : Finset α → Prop := fun Q => ∀ a ∈ Q, ∀ b ∈ Q, a ≠ b → ¬ Conflict a b
  open scoped Classical in
  let Cands : Finset (Finset α) := Finset.univ.filter Indep
  have hCands_ne : Cands.Nonempty := ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [Indep]⟩⟩
  rcases Finset.exists_max_image Cands Finset.card hCands_ne with ⟨Q, hQ_mem, hQ_max⟩
  have hQ_indep : Indep Q := (Finset.mem_filter.mp hQ_mem).2
  have huniv_sub : (Finset.univ : Finset α) ⊆
      Q.biUnion (fun y => Finset.univ.filter (fun x => Conflict x y)) := by
    intro x _
    rw [Finset.mem_biUnion]
    by_cases hx : x ∈ Q
    · exact ⟨x, hx, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hRefl x⟩⟩
    · have hnot : ¬ Indep (insert x Q) := by
        intro hind
        have hmem : insert x Q ∈ Cands := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hind⟩
        have hle := hQ_max (insert x Q) hmem
        rw [Finset.card_insert_of_notMem hx] at hle
        omega
      dsimp [Indep] at hnot
      push Not at hnot
      rcases hnot with ⟨a, ha, b, hb, hab_ne, hconf⟩
      rcases Finset.mem_insert.mp ha with rfl | haQ
      · rcases Finset.mem_insert.mp hb with rfl | hbQ
        · exact (hab_ne rfl).elim
        · exact ⟨b, hbQ, Finset.mem_filter.mpr ⟨Finset.mem_univ a, hconf⟩⟩
      · rcases Finset.mem_insert.mp hb with rfl | hbQ
        · exact ⟨a, haQ, Finset.mem_filter.mpr ⟨Finset.mem_univ b, hSymm a b hconf⟩⟩
        · exact (hQ_indep a haQ b hbQ hab_ne hconf).elim
  have hcard_le : Fintype.card α ≤ Q.card * M := by
    calc
      Fintype.card α = (Finset.univ : Finset α).card := (Finset.card_univ).symm
      _ ≤ (Q.biUnion (fun y => Finset.univ.filter (fun x => Conflict x y))).card :=
        Finset.card_le_card huniv_sub
      _ ≤ ∑ y ∈ Q, (Finset.univ.filter (fun x => Conflict x y)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _y ∈ Q, M := Finset.sum_le_sum fun y _ => hDeg y
      _ = Q.card * M := by simp
  exact ⟨Q, hQ_indep, hcard_le⟩

private lemma double_counting_translate {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (Q E : Finset (G × G)) :
    (∑ p : G × G, (((Q.map (addRightEmbedding p)) ∩ E).card : ℝ)) =
      (Q.card : ℝ) * (E.card : ℝ) := by
  have hnat : (∑ p : G × G, ((Q.map (addRightEmbedding p)) ∩ E).card) = Q.card * E.card := by
    have hinner : ∀ p : G × G,
        ((Q.map (addRightEmbedding p)) ∩ E).card =
          (Q.filter (fun q => q + p ∈ E)).card := by
      intro p
      have himg : (Q.map (addRightEmbedding p)) ∩ E =
          (Q.filter (fun q => q + p ∈ E)).map (addRightEmbedding p) := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_map, addRightEmbedding_apply,
          Finset.mem_filter]
        constructor
        · rintro ⟨⟨q, hq, rfl⟩, hxE⟩
          exact ⟨q, ⟨hq, hxE⟩, rfl⟩
        · rintro ⟨q, ⟨hq, hxE⟩, rfl⟩
          exact ⟨⟨q, hq, rfl⟩, hxE⟩
      rw [himg, Finset.card_map]
    simp_rw [hinner, Finset.card_filter]
    rw [Finset.sum_comm]
    have hq_count : ∀ q : G × G,
        (∑ p : G × G, if q + p ∈ E then 1 else 0) = E.card := by
      intro q
      let e : G × G ≃ G × G := Equiv.addLeft q
      have he : (∑ p : G × G, if q + p ∈ E then 1 else 0) =
          ∑ x : G × G, if x ∈ E then 1 else 0 :=
        Fintype.sum_equiv e (fun p => if q + p ∈ E then 1 else 0)
          (fun x => if x ∈ E then 1 else 0) (fun _ => rfl)
      rw [he, Finset.sum_boole]
      simp
    calc
      ∑ q ∈ Q, ∑ p : G × G, (if q + p ∈ E then 1 else 0)
          = ∑ _q ∈ Q, E.card := Finset.sum_congr rfl fun q _ => hq_count q
      _ = Q.card * E.card := by simp
  exact_mod_cast hnat

private lemma f2n_add_self {n : ℕ} (x : 𝔽₂ n) : x + x = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (x i)

private lemma eventually_pow3_mul_exp_neg_lt (c : ℝ) (hc : 0 < c) :
    ∀ᶠ n : ℕ in Filter.atTop, (2 ^ n : ℝ) ^ 3 * Real.exp (-c * (2 ^ n : ℝ)) < 1 / 3 := by
  obtain ⟨M, hM⟩ := exists_nat_gt (72 / c ^ 4)
  rw [Filter.eventually_atTop]
  refine ⟨M, fun n hn => ?_⟩
  have hx_pos : (0 : ℝ) < (2 ^ n : ℝ) := by positivity
  have h2n_ge : (n : ℝ) < (2 ^ n : ℝ) := by
    have : n < 2 ^ n := Nat.lt_two_pow_self
    exact_mod_cast this
  have hM_le : (M : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hx_gt : 72 / c ^ 4 < (2 ^ n : ℝ) := lt_of_lt_of_le hM (hM_le.trans h2n_ge.le)
  let x : ℝ := (2 ^ n : ℝ)
  have hcx_nonneg : 0 ≤ c * x := mul_nonneg hc.le hx_pos.le
  have hsum_le : (c * x) ^ 4 / 24 ≤ Real.exp (c * x) := by
    have hs := Real.sum_le_exp_of_nonneg hcx_nonneg 5
    have h4 : (c * x) ^ 4 / (Nat.factorial 4 : ℝ) ≤
        ∑ i ∈ Finset.range 5, (c * x) ^ i / ↑i.factorial := by
      refine Finset.single_le_sum (f := fun i => (c * x) ^ i / (i.factorial : ℝ))
        (fun i _ => by positivity) (Finset.mem_range.mpr (by decide : 4 < 5))
    have hfact : (Nat.factorial 4 : ℝ) = 24 := by norm_num
    rw [hfact] at h4
    exact h4.trans hs
  have hexp_inv : Real.exp (-c * x) ≤ 24 / (c * x) ^ 4 := by
    rw [show -c * x = -(c * x) by ring, Real.exp_neg, inv_eq_one_div,
      div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
    linarith
  calc
    x ^ 3 * Real.exp (-c * x)
        ≤ x ^ 3 * (24 / (c * x) ^ 4) := mul_le_mul_of_nonneg_left hexp_inv (by positivity)
    _ = 24 / (c ^ 4 * x) := by
      field_simp [hc.ne', hx_pos.ne']
    _ < 1 / 3 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      have hc4_pos : 0 < c ^ 4 := by positivity
      have hmul := mul_lt_mul_of_pos_left hx_gt hc4_pos
      have heq : c ^ 4 * (72 / c ^ 4) = 72 := by field_simp [hc4_pos.ne']
      linarith

private lemma disjoint_S2_coords {G : Type*} [DecidableEq G]
    {x₁ x₁' x₂ x₂' y₁ y₁' y₂ y₂' z₁ z₁' z₂ z₂' : G}
    (hx00 : x₁ ≠ x₂) (hx01 : x₁ ≠ x₂') (hx10 : x₁' ≠ x₂) (hx11 : x₁' ≠ x₂')
    (hy00 : y₁ ≠ y₂) (hy01 : y₁ ≠ y₂') (hy10 : y₁' ≠ y₂) (hy11 : y₁' ≠ y₂')
    (hz00 : z₁ ≠ z₂) (hz01 : z₁ ≠ z₂') (hz10 : z₁' ≠ z₂) (hz11 : z₁' ≠ z₂') :
    Disjoint
      ({Sum.inl x₁, Sum.inl x₁', Sum.inr (Sum.inl y₁), Sum.inr (Sum.inl y₁'),
        Sum.inr (Sum.inr z₁), Sum.inr (Sum.inr z₁')} : Finset (G ⊕ G ⊕ G))
      ({Sum.inl x₂, Sum.inl x₂', Sum.inr (Sum.inl y₂), Sum.inr (Sum.inl y₂'),
        Sum.inr (Sum.inr z₂), Sum.inr (Sum.inr z₂')} : Finset (G ⊕ G ⊕ G)) := by
  simp only [Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton]
  rintro i (rfl | rfl | rfl | rfl | rfl | rfl) (h | h | h | h | h | h)
  · exact hx00 (Sum.inl.inj h)
  · exact hx01 (Sum.inl.inj h)
  · cases h
  · cases h
  · cases h
  · cases h
  · exact hx10 (Sum.inl.inj h)
  · exact hx11 (Sum.inl.inj h)
  · cases h
  · cases h
  · cases h
  · cases h
  · cases h
  · cases h
  · exact hy00 (Sum.inl.inj (Sum.inr.inj h))
  · exact hy01 (Sum.inl.inj (Sum.inr.inj h))
  · cases (Sum.inr.inj h)
  · cases (Sum.inr.inj h)
  · cases h
  · cases h
  · exact hy10 (Sum.inl.inj (Sum.inr.inj h))
  · exact hy11 (Sum.inl.inj (Sum.inr.inj h))
  · cases (Sum.inr.inj h)
  · cases (Sum.inr.inj h)
  · cases h
  · cases h
  · cases (Sum.inr.inj h)
  · cases (Sum.inr.inj h)
  · exact hz00 (Sum.inr.inj (Sum.inr.inj h))
  · exact hz01 (Sum.inr.inj (Sum.inr.inj h))
  · cases h
  · cases h
  · cases (Sum.inr.inj h)
  · cases (Sum.inr.inj h)
  · exact hz10 (Sum.inr.inj (Sum.inr.inj h))
  · exact hz11 (Sum.inr.inj (Sum.inr.inj h))

/-- Mandache's finite-product random corner construction on `𝔽₂ n × 𝔽₂ n`. -/
theorem mandache_random_corner_upper {q : ℕ} (hq : 1 ≤ q)
    (W : ZMod q → ZMod q → ZMod q → ℝ) (hW : ∀ u v w, W u v w = 0 ∨ W u v w = 1)
    (ε : ℝ) (hε : 0 < ε) :
    let _ : NeZero q := ⟨by omega⟩
    let α := ∑ u : ZMod q, ∑ v : ZMod q, ∑ w : ZMod q,
      (1 / (q : ℝ)) * (1 / (q : ℝ)) * (1 / (q : ℝ)) * W u v w
    let τ := weightedTriforce (fun _ => 1 / (q : ℝ)) (fun _ => 1 / (q : ℝ))
      (fun _ => 1 / (q : ℝ)) W
    ∀ᶠ n : ℕ in Filter.atTop,
      ∃ A : Finset (𝔽₂ n × 𝔽₂ n),
        let N : ℝ := (Fintype.card (𝔽₂ n) : ℝ)
        (A.card : ℝ) ≥ (α - ε) * N^2 ∧
        ∀ d : 𝔽₂ n, d ≠ 0 → ((S d A).card : ℝ) ≤ (τ + ε) * N^2 := by
  intro hq_nz α τ
  have hq_ne : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hq_card : (Fintype.card (ZMod q) : ℝ) = (q : ℝ) := by simp [ZMod.card]
  have hW_eq_ite : ∀ u v w, (if W u v w = 1 then (1 : ℝ) else 0) = W u v w := by
    intro u v w
    rcases hW u v w with h | h <;> simp [h]
  have hev1 := eventually_pow3_mul_exp_neg_lt (2 * ε ^ 2 / 3) (by positivity)
  have hev2 := eventually_pow3_mul_exp_neg_lt (2 * ε ^ 2 / 6) (by positivity)
  filter_upwards [hev1, hev2] with n hn1 hn2
  let G := 𝔽₂ n
  let N : ℝ := (Fintype.card G : ℝ)
  have hN_eq : N = (2 ^ n : ℝ) := by
    dsimp [N, G, 𝔽₂, 𝔽]
    simp [ZMod.card]
  have hN_pos : 0 < N := by rw [hN_eq]; positivity
  let Idx := Sum G (Sum G G)
  let Ω := Idx → ZMod q
  let X : Ω → G → ZMod q := fun ω x => ω (Sum.inl x)
  let Y : Ω → G → ZMod q := fun ω y => ω (Sum.inr (Sum.inl y))
  let Z : Ω → G → ZMod q := fun ω z => ω (Sum.inr (Sum.inr z))
  open scoped Classical in
  let A_of : Ω → Finset (G × G) :=
    fun ω => Finset.univ.filter (fun p : G × G => W (X ω p.1) (Y ω p.2) (Z ω (p.1 + p.2)) = 1)
  -- Step 1: Maximal 1-independent transversal Q for A_of
  let Conflict₁ : (G × G) → (G × G) → Prop :=
    fun p₁ p₂ => p₁.1 = p₂.1 ∨ p₁.2 = p₂.2 ∨ p₁.1 + p₁.2 = p₂.1 + p₂.2
  have hC1_refl : ∀ p, Conflict₁ p p := fun p => Or.inl rfl
  have hC1_symm : ∀ p₁ p₂, Conflict₁ p₁ p₂ → Conflict₁ p₂ p₁ := by
    rintro p₁ p₂ (h | h | h)
    · exact Or.inl h.symm
    · exact Or.inr (Or.inl h.symm)
    · exact Or.inr (Or.inr h.symm)
  have hC1_deg : ∀ p₂ : G × G,
      (Finset.univ.filter (fun p₁ : G × G => Conflict₁ p₁ p₂)).card ≤ 3 * Fintype.card G := by
    intro p₂
    let U₁ : Finset (G × G) := ({p₂.1} ×ˢ Finset.univ) ∪ (Finset.univ ×ˢ {p₂.2}) ∪
      ((Finset.univ : Finset G).image (fun x => (x, p₂.1 + p₂.2 - x)))
    have hsub : Finset.univ.filter (fun p₁ : G × G => Conflict₁ p₁ p₂) ⊆ U₁ := by
      rintro ⟨x, y⟩ hmem
      have hc : Conflict₁ (x, y) p₂ := (Finset.mem_filter.mp hmem).2
      simp only [U₁, Finset.mem_union, Finset.mem_product, Finset.mem_singleton,
        Finset.mem_univ, and_true, true_and, Finset.mem_image, Prod.mk.injEq]
      rcases hc with hx | hy | hxy
      · exact Or.inl (Or.inl hx)
      · exact Or.inl (Or.inr hy)
      · right
        refine ⟨x, rfl, ?_⟩
        calc
          p₂.1 + p₂.2 - x = (x + y) - x := by rw [← hxy]
          _ = y := by abel
    have hcard_U₁ : U₁.card ≤ 3 * Fintype.card G := by
      calc
        U₁.card ≤ (({p₂.1} ×ˢ Finset.univ) ∪ (Finset.univ ×ˢ {p₂.2})).card +
            ((Finset.univ : Finset G).image (fun x => (x, p₂.1 + p₂.2 - x))).card :=
          Finset.card_union_le _ _
        _ ≤ (({p₂.1} ×ˢ (Finset.univ : Finset G)).card +
              ((Finset.univ : Finset G) ×ˢ {p₂.2}).card) +
            (Finset.univ : Finset G).card := by
          gcongr
          · exact Finset.card_union_le _ _
          · exact Finset.card_image_le
        _ = 3 * Fintype.card G := by
          simp
          ring
    exact (Finset.card_le_card hsub).trans hcard_U₁
  rcases exists_max_indep Conflict₁ hC1_refl hC1_symm (3 * Fintype.card G) hC1_deg with
    ⟨Q, hQ_indep, hQ_card_nat⟩
  have hQ_card_ge : N / 3 ≤ (Q.card : ℝ) := by
    have hnat : Fintype.card G * Fintype.card G ≤ Q.card * (3 * Fintype.card G) := by
      simpa [Fintype.card_prod] using hQ_card_nat
    have hreal : N * N ≤ (Q.card : ℝ) * (3 * N) := by
      dsimp [N]
      exact_mod_cast hnat
    nlinarith
  have hQ_pos : (0 : ℝ) < (Q.card : ℝ) := lt_of_lt_of_le (by positivity) hQ_card_ge
  let S₁ : G × G → Finset Idx :=
    fun pt => {Sum.inl pt.1, Sum.inr (Sum.inl pt.2), Sum.inr (Sum.inr (pt.1 + pt.2))}
  let E₁ : (G × G) → Ω → ℝ :=
    fun pt ω => if W (X ω pt.1) (Y ω pt.2) (Z ω (pt.1 + pt.2)) = 1 then 1 else 0
  have hE₁_dep : ∀ pt : G × G, DependsOnlyOn (S₁ pt) (E₁ pt) := by
    intro pt ω₁ ω₂ hω
    have hx : X ω₁ pt.1 = X ω₂ pt.1 := hω _ (by simp [S₁])
    have hy : Y ω₁ pt.2 = Y ω₂ pt.2 := hω _ (by simp [S₁])
    have hz : Z ω₁ (pt.1 + pt.2) = Z ω₂ (pt.1 + pt.2) := hω _ (by simp [S₁])
    simp [E₁, hx, hy, hz]
  have hE₁_bool : ∀ pt : G × G, ∀ ω : Ω, E₁ pt ω = 0 ∨ E₁ pt ω = 1 := by
    intro pt ω
    dsimp [E₁]
    split_ifs <;> simp
  have hE₁_mean : ∀ pt : G × G,
      (∑ ω : Ω, E₁ pt ω) / (Fintype.card Ω : ℝ) = α := by
    intro pt
    let κ : Fin 3 → Idx := ![Sum.inl pt.1, Sum.inr (Sum.inl pt.2), Sum.inr (Sum.inr (pt.1 + pt.2))]
    have hκ : Function.Injective κ := by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        first
        | rfl
        | cases hij
    have hdiv := sum_eval_inj_div_card κ hκ (fun v : Fin 3 → ZMod q => W (v 0) (v 1) (v 2))
    have hsum_eq : (∑ ω : Ω, E₁ pt ω) / (Fintype.card Ω : ℝ) =
        (∑ ω : Idx → ZMod q,
          (fun v : Fin 3 → ZMod q => W (v 0) (v 1) (v 2)) (fun j => ω (κ j))) /
          (Fintype.card (Idx → ZMod q) : ℝ) := by
      congr 1
      refine Finset.sum_congr rfl fun ω _ => ?_
      dsimp [E₁, X, Y, Z, κ]
      exact hW_eq_ite _ _ _
    rw [hsum_eq, hdiv]
    let e3 : (Fin 3 → ZMod q) ≃ ZMod q × ZMod q × ZMod q :=
      { toFun := fun v => (v 0, v 1, v 2)
        invFun := fun t => ![t.1, t.2.1, t.2.2]
        left_inv := fun v => by funext i; fin_cases i <;> rfl
        right_inv := fun ⟨a, b, c⟩ => rfl }
    have hsum3 : (∑ v : Fin 3 → ZMod q, W (v 0) (v 1) (v 2)) =
        ∑ u : ZMod q, ∑ v : ZMod q, ∑ w : ZMod q, W u v w := by
      rw [← Equiv.sum_comp e3.symm]
      simp [Fintype.sum_prod_type, e3]
    rw [hsum3, hq_card]
    dsimp [α]
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [show W u v w / (q : ℝ) ^ 3 = (1 / (q : ℝ)) * (1 / (q : ℝ)) * (1 / (q : ℝ)) * W u v w by
      field_simp [hq_ne]]
  -- Bad₁(p) for p : G × G
  open scoped Classical in
  let Bad₁ : (G × G) → Finset Ω := fun p =>
    Finset.univ.filter (fun ω =>
      (((Q.map (addRightEmbedding p)) ∩ A_of ω).card : ℝ) < (α - ε) * (Q.card : ℝ))
  have hBad₁_prob : ∀ p : G × G,
      ((Bad₁ p).card : ℝ) / (Fintype.card Ω : ℝ) ≤ Real.exp (-2 * ε ^ 2 * (N / 3)) := by
    intro p
    let Qp : Finset (G × G) := Q.map (addRightEmbedding p)
    have hQp_card : (Qp.card : ℝ) = (Q.card : ℝ) := by simp [Qp]
    have hQp_disj : ∀ b₁ ∈ Qp, ∀ b₂ ∈ Qp, b₁ ≠ b₂ → Disjoint (S₁ b₁) (S₁ b₂) := by
      intro b₁ hb₁ b₂ hb₂ hne
      rcases Finset.mem_map.mp hb₁ with ⟨q₁, hq₁, rfl⟩
      rcases Finset.mem_map.mp hb₂ with ⟨q₂, hq₂, rfl⟩
      have hq_ne' : q₁ ≠ q₂ := fun h => hne (by subst h; rfl)
      have hnc : ¬ Conflict₁ q₁ q₂ := hQ_indep q₁ hq₁ q₂ hq₂ hq_ne'
      have h1 : q₁.1 + p.1 ≠ q₂.1 + p.1 := fun h => hnc (Or.inl (add_right_cancel h))
      have h2 : q₁.2 + p.2 ≠ q₂.2 + p.2 := fun h => hnc (Or.inr (Or.inl (add_right_cancel h)))
      have h3 : (q₁.1 + p.1) + (q₁.2 + p.2) ≠ (q₂.1 + p.1) + (q₂.2 + p.2) := by
        intro h
        apply hnc
        right; right
        have h' : (q₁.1 + q₁.2) + (p.1 + p.2) = (q₂.1 + q₂.2) + (p.1 + p.2) := by
          calc
            (q₁.1 + q₁.2) + (p.1 + p.2) = (q₁.1 + p.1) + (q₁.2 + p.2) := by abel
            _ = (q₂.1 + p.1) + (q₂.2 + p.2) := h
            _ = (q₂.1 + q₂.2) + (p.1 + p.2) := by abel
        exact add_right_cancel h'
      simp only [S₁, Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton,
        addRightEmbedding_apply, Prod.fst_add, Prod.snd_add]
      rintro i (rfl | rfl | rfl) (hi | hi | hi)
      · exact h1 (Sum.inl.inj hi)
      · cases hi
      · cases hi
      · cases hi
      · exact h2 (Sum.inl.inj (Sum.inr.inj hi))
      · cases (Sum.inr.inj hi)
      · cases hi
      · cases (Sum.inr.inj hi)
      · exact h3 (Sum.inr.inj (Sum.inr.inj hi))
    have hBad_sub : Bad₁ p ⊆
        Finset.univ.filter (fun ω : Ω => ∑ pt ∈ Qp, E₁ pt ω ≤ (α - ε) * (Qp.card : ℝ)) := by
      intro ω hω
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have hlt : ((Qp ∩ A_of ω).card : ℝ) < (α - ε) * (Q.card : ℝ) :=
        (Finset.mem_filter.mp hω).2
      have hsum_eq : ∑ pt ∈ Qp, E₁ pt ω = ((Qp ∩ A_of ω).card : ℝ) := by
        have h1 : ∀ pt ∈ Qp, E₁ pt ω = if pt ∈ A_of ω then (1 : ℝ) else 0 := by
          intro pt _
          simp [E₁, A_of]
        rw [Finset.sum_congr rfl h1, Finset.sum_boole, Finset.filter_mem_eq_inter]
      rw [hsum_eq, hQp_card]
      exact hlt.le
    calc
      ((Bad₁ p).card : ℝ) / (Fintype.card Ω : ℝ)
          ≤ ((Finset.univ.filter (fun ω : Ω =>
              ∑ pt ∈ Qp, E₁ pt ω ≤ (α - ε) * (Qp.card : ℝ))).card : ℝ) / (Fintype.card Ω : ℝ) := by
        gcongr
      _ ≤ Real.exp (-2 * ε ^ 2 * (Qp.card : ℝ)) :=
        finite_product_hoeffding_lower Qp S₁ E₁ α ε hε.le
          (fun b _ => hE₁_dep b) hQp_disj (fun b _ => hE₁_bool b) (fun b _ => hE₁_mean b)
      _ ≤ Real.exp (-2 * ε ^ 2 * (N / 3)) := by
        apply Real.exp_le_exp.mpr
        rw [hQp_card]
        nlinarith [sq_nonneg ε]
  -- Step 2: Maximal 2-independent transversal Q_d for S d (A_of ω) when d ≠ 0
  let S₂ : G → (G × G) → Finset Idx := fun d pt =>
    {Sum.inl pt.1, Sum.inl (pt.1 + d), Sum.inr (Sum.inl pt.2), Sum.inr (Sum.inl (pt.2 + d)),
     Sum.inr (Sum.inr (pt.1 + pt.2)), Sum.inr (Sum.inr (pt.1 + pt.2 + d))}
  let E₂ : G → (G × G) → Ω → ℝ := fun d pt ω =>
    W (X ω pt.1) (Y ω pt.2) (Z ω (pt.1 + pt.2)) *
      W (X ω (pt.1 + d)) (Y ω pt.2) (Z ω (pt.1 + pt.2 + d)) *
      W (X ω pt.1) (Y ω (pt.2 + d)) (Z ω (pt.1 + pt.2 + d))
  have hE₂_dep : ∀ d pt, DependsOnlyOn (S₂ d pt) (E₂ d pt) := by
    intro d pt ω₁ ω₂ hω
    have h1 : X ω₁ pt.1 = X ω₂ pt.1 := hω _ (by simp [S₂])
    have h2 : X ω₁ (pt.1 + d) = X ω₂ (pt.1 + d) := hω _ (by simp [S₂])
    have h3 : Y ω₁ pt.2 = Y ω₂ pt.2 := hω _ (by simp [S₂])
    have h4 : Y ω₁ (pt.2 + d) = Y ω₂ (pt.2 + d) := hω _ (by simp [S₂])
    have h5 : Z ω₁ (pt.1 + pt.2) = Z ω₂ (pt.1 + pt.2) := hω _ (by simp [S₂])
    have h6 : Z ω₁ (pt.1 + pt.2 + d) = Z ω₂ (pt.1 + pt.2 + d) := hω _ (by simp [S₂])
    simp [E₂, h1, h2, h3, h4, h5, h6]
  have hE₂_bool : ∀ d pt ω, E₂ d pt ω = 0 ∨ E₂ d pt ω = 1 := by
    intro d pt ω
    dsimp [E₂]
    rcases hW (X ω pt.1) (Y ω pt.2) (Z ω (pt.1 + pt.2)) with h1 | h1 <;>
    rcases hW (X ω (pt.1 + d)) (Y ω pt.2) (Z ω (pt.1 + pt.2 + d)) with h2 | h2 <;>
    rcases hW (X ω pt.1) (Y ω (pt.2 + d)) (Z ω (pt.1 + pt.2 + d)) with h3 | h3 <;>
    simp [h1, h2, h3]
  have hE₂_ind : ∀ d pt ω, E₂ d pt ω = (if pt ∈ S d (A_of ω) then (1 : ℝ) else 0) := by
    intro d pt ω
    have hmem : pt ∈ S d (A_of ω) ↔
        W (X ω pt.1) (Y ω pt.2) (Z ω (pt.1 + pt.2)) = 1 ∧
        W (X ω (pt.1 + d)) (Y ω pt.2) (Z ω (pt.1 + pt.2 + d)) = 1 ∧
        W (X ω pt.1) (Y ω (pt.2 + d)) (Z ω (pt.1 + pt.2 + d)) = 1 := by
      simp only [S, IsCorner, A_of, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [show (pt.1 + d) + pt.2 = pt.1 + pt.2 + d by abel,
          show pt.1 + (pt.2 + d) = pt.1 + pt.2 + d by abel]
    dsimp [E₂]
    rcases hW (X ω pt.1) (Y ω pt.2) (Z ω (pt.1 + pt.2)) with h1 | h1 <;>
    rcases hW (X ω (pt.1 + d)) (Y ω pt.2) (Z ω (pt.1 + pt.2 + d)) with h2 | h2 <;>
    rcases hW (X ω pt.1) (Y ω (pt.2 + d)) (Z ω (pt.1 + pt.2 + d)) with h3 | h3 <;>
    simp [hmem, h1, h2, h3]
  have hE₂_mean : ∀ d : G, d ≠ 0 → ∀ pt : G × G,
      (∑ ω : Ω, E₂ d pt ω) / (Fintype.card Ω : ℝ) = τ := by
    intro d hd pt
    let κ : Fin 6 → Idx :=
      ![Sum.inl pt.1, Sum.inl (pt.1 + d), Sum.inr (Sum.inl pt.2), Sum.inr (Sum.inl (pt.2 + d)),
        Sum.inr (Sum.inr (pt.1 + pt.2)), Sum.inr (Sum.inr (pt.1 + pt.2 + d))]
    have hκ : Function.Injective κ := by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        first
        | rfl
        | cases hij
        | exact (hd (by simpa using (add_left_cancel (show pt.1 + 0 = pt.1 + d by simpa using Sum.inl.inj hij)).symm)).elim
        | exact (hd (by simpa using add_left_cancel (show pt.1 + d = pt.1 + 0 by simpa using Sum.inl.inj hij))).elim
        | exact (hd (by simpa using (add_left_cancel (show pt.2 + 0 = pt.2 + d by simpa using Sum.inl.inj (Sum.inr.inj hij))).symm)).elim
        | exact (hd (by simpa using add_left_cancel (show pt.2 + d = pt.2 + 0 by simpa using Sum.inl.inj (Sum.inr.inj hij)))).elim
        | exact (hd (by simpa using (add_left_cancel (show (pt.1 + pt.2) + 0 = (pt.1 + pt.2) + d by simpa using Sum.inr.inj (Sum.inr.inj hij))).symm)).elim
    have hdiv := sum_eval_inj_div_card κ hκ
      (fun v : Fin 6 → ZMod q => W (v 0) (v 2) (v 4) * W (v 1) (v 2) (v 5) * W (v 0) (v 3) (v 5))
    have hsum_eq : (∑ ω : Ω, E₂ d pt ω) / (Fintype.card Ω : ℝ) =
        (∑ ω : Idx → ZMod q,
          (fun v : Fin 6 → ZMod q =>
            W (v 0) (v 2) (v 4) * W (v 1) (v 2) (v 5) * W (v 0) (v 3) (v 5))
            (fun j => ω (κ j))) / (Fintype.card (Idx → ZMod q) : ℝ) := rfl
    rw [hsum_eq, hdiv]
    let e6 : (Fin 6 → ZMod q) ≃ (ZMod q × ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q) :=
      { toFun := fun v => ((v 0, v 2, v 5), (v 1, v 3, v 4))
        invFun := fun t => ![t.1.1, t.2.1, t.1.2.1, t.2.2.1, t.2.2.2, t.1.2.2]
        left_inv := fun v => by funext i; fin_cases i <;> rfl
        right_inv := fun ⟨⟨u, v, w⟩, ⟨u', v', w'⟩⟩ => rfl }
    have hsum6 : (∑ v : Fin 6 → ZMod q,
          W (v 0) (v 2) (v 4) * W (v 1) (v 2) (v 5) * W (v 0) (v 3) (v 5)) =
        ∑ u : ZMod q, ∑ v : ZMod q, ∑ w : ZMod q,
          ∑ u' : ZMod q, ∑ v' : ZMod q, ∑ w' : ZMod q,
            W u' v w * W u v' w * W u v w' := by
      rw [← Equiv.sum_comp e6.symm]
      simp only [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun u _ =>
        Finset.sum_congr rfl fun v _ =>
          Finset.sum_congr rfl fun w _ =>
            Finset.sum_congr rfl fun u' _ =>
              Finset.sum_congr rfl fun v' _ =>
                Finset.sum_congr rfl fun w' _ => ?_
      change W u v w' * W u' v w * W u v' w = W u' v w * W u v' w * W u v w'
      ring
    rw [hsum6, hq_card]
    dsimp [τ]
    rw [weightedTriforce_unif (q : ℝ) W, one_div, inv_pow, mul_comm ((q : ℝ) ^ 6)⁻¹, ← div_eq_mul_inv]
  -- For each d ≠ 0, bound bad probability summed over p : G × G
  have hBad₂_for_d : ∀ d : G, d ≠ 0 →
      ∃ Bad_d : Finset Ω,
        ((Bad_d.card : ℝ) / (Fintype.card Ω : ℝ) ≤
          N ^ 2 * Real.exp (-2 * ε ^ 2 * (N / 6))) ∧
        (∀ ω : Ω, ω ∉ Bad_d → ((S d (A_of ω)).card : ℝ) ≤ (τ + ε) * N ^ 2) := by
    intro d hd
    let Conflict₂ : (G × G) → (G × G) → Prop := fun p₁ p₂ =>
      (p₁.1 = p₂.1 ∨ p₁.1 = p₂.1 + d) ∨
      (p₁.2 = p₂.2 ∨ p₁.2 = p₂.2 + d) ∨
      (p₁.1 + p₁.2 = p₂.1 + p₂.2 ∨ p₁.1 + p₁.2 = p₂.1 + p₂.2 + d)
    have hC2_refl : ∀ p, Conflict₂ p p := fun p => Or.inl (Or.inl rfl)
    have hC2_symm : ∀ p₁ p₂, Conflict₂ p₁ p₂ → Conflict₂ p₂ p₁ := by
      have hswap : ∀ a b : G, a = b + d → b = a + d := by
        intro a b hab
        calc
          b = b + (d + d) := by rw [f2n_add_self, add_zero]
          _ = (b + d) + d := by abel
          _ = a + d := by rw [← hab]
      rintro p₁ p₂ ((h | h) | (h | h) | (h | h))
      · exact Or.inl (Or.inl h.symm)
      · exact Or.inl (Or.inr (hswap _ _ h))
      · exact Or.inr (Or.inl (Or.inl h.symm))
      · exact Or.inr (Or.inl (Or.inr (hswap _ _ h)))
      · exact Or.inr (Or.inr (Or.inl h.symm))
      · exact Or.inr (Or.inr (Or.inr (hswap _ _ h)))
    have hC2_deg : ∀ p₂ : G × G,
        (Finset.univ.filter (fun p₁ : G × G => Conflict₂ p₁ p₂)).card ≤ 6 * Fintype.card G := by
      intro p₂
      let U₂ : Finset (G × G) :=
        ({p₂.1} ×ˢ Finset.univ) ∪ ({p₂.1 + d} ×ˢ Finset.univ) ∪
        (Finset.univ ×ˢ {p₂.2}) ∪ (Finset.univ ×ˢ {p₂.2 + d}) ∪
        ((Finset.univ : Finset G).image (fun x => (x, p₂.1 + p₂.2 - x))) ∪
        ((Finset.univ : Finset G).image (fun x => (x, p₂.1 + p₂.2 + d - x)))
      have hsub : Finset.univ.filter (fun p₁ : G × G => Conflict₂ p₁ p₂) ⊆ U₂ := by
        rintro ⟨x, y⟩ hmem
        have hc : Conflict₂ (x, y) p₂ := (Finset.mem_filter.mp hmem).2
        simp only [U₂, Finset.mem_union, Finset.mem_product, Finset.mem_singleton,
          Finset.mem_univ, and_true, true_and, Finset.mem_image, Prod.mk.injEq]
        rcases hc with (hx | hx) | (hy | hy) | (hxy | hxy)
        · left; left; left; left; left; exact hx
        · left; left; left; left; right; exact hx
        · left; left; left; right; exact hy
        · left; left; right; exact hy
        · left; right; refine ⟨x, rfl, ?_⟩; rw [← hxy]; abel
        · right; refine ⟨x, rfl, ?_⟩; rw [← hxy]; abel
      have hcard_U₂ : U₂.card ≤ 6 * Fintype.card G := by
        let S₁' : Finset (G × G) := {p₂.1} ×ˢ (Finset.univ : Finset G)
        let S₂' : Finset (G × G) := {p₂.1 + d} ×ˢ (Finset.univ : Finset G)
        let S₃' : Finset (G × G) := (Finset.univ : Finset G) ×ˢ {p₂.2}
        let S₄' : Finset (G × G) := (Finset.univ : Finset G) ×ˢ {p₂.2 + d}
        let S₅' : Finset (G × G) := (Finset.univ : Finset G).image (fun x => (x, p₂.1 + p₂.2 - x))
        let S₆' : Finset (G × G) := (Finset.univ : Finset G).image (fun x => (x, p₂.1 + p₂.2 + d - x))
        have hc1 : S₁'.card = Fintype.card G := by simp [S₁']
        have hc2 : S₂'.card = Fintype.card G := by simp [S₂']
        have hc3 : S₃'.card = Fintype.card G := by simp [S₃']
        have hc4 : S₄'.card = Fintype.card G := by simp [S₄']
        have hc5 : S₅'.card ≤ Fintype.card G := Finset.card_image_le.trans (by simp)
        have hc6 : S₆'.card ≤ Fintype.card G := Finset.card_image_le.trans (by simp)
        have hu1 := Finset.card_union_le S₁' S₂'
        have hu2 := Finset.card_union_le (S₁' ∪ S₂') S₃'
        have hu3 := Finset.card_union_le ((S₁' ∪ S₂') ∪ S₃') S₄'
        have hu4 := Finset.card_union_le (((S₁' ∪ S₂') ∪ S₃') ∪ S₄') S₅'
        have hu5 := Finset.card_union_le ((((S₁' ∪ S₂') ∪ S₃') ∪ S₄') ∪ S₅') S₆'
        change ((((S₁' ∪ S₂') ∪ S₃') ∪ S₄') ∪ S₅' ∪ S₆').card ≤ 6 * Fintype.card G
        omega
      exact (Finset.card_le_card hsub).trans hcard_U₂
    rcases exists_max_indep Conflict₂ hC2_refl hC2_symm (6 * Fintype.card G) hC2_deg with
      ⟨Q_d, hQd_indep, hQd_card_nat⟩
    have hQd_card_ge : N / 6 ≤ (Q_d.card : ℝ) := by
      have hnat : Fintype.card G * Fintype.card G ≤ Q_d.card * (6 * Fintype.card G) := by
        simpa [Fintype.card_prod] using hQd_card_nat
      have hreal : N * N ≤ (Q_d.card : ℝ) * (6 * N) := by
        dsimp [N]
        exact_mod_cast hnat
      nlinarith
    have hQd_pos : (0 : ℝ) < (Q_d.card : ℝ) := lt_of_lt_of_le (by positivity) hQd_card_ge
    open scoped Classical in
    let Bad_dp : (G × G) → Finset Ω := fun p =>
      Finset.univ.filter (fun ω =>
        (τ + ε) * (Q_d.card : ℝ) < (((Q_d.map (addRightEmbedding p)) ∩ S d (A_of ω)).card : ℝ))
    open scoped Classical in
    let Bad_d : Finset Ω := (Finset.univ : Finset (G × G)).biUnion Bad_dp
    refine ⟨Bad_d, ?_, ?_⟩
    · have hBad_dp_prob : ∀ p : G × G,
          ((Bad_dp p).card : ℝ) / (Fintype.card Ω : ℝ) ≤ Real.exp (-2 * ε ^ 2 * (N / 6)) := by
        intro p
        let Qp : Finset (G × G) := Q_d.map (addRightEmbedding p)
        have hQp_card : (Qp.card : ℝ) = (Q_d.card : ℝ) := by simp [Qp]
        have hQp_disj : ∀ b₁ ∈ Qp, ∀ b₂ ∈ Qp, b₁ ≠ b₂ → Disjoint (S₂ d b₁) (S₂ d b₂) := by
          intro b₁ hb₁ b₂ hb₂ hne
          rcases Finset.mem_map.mp hb₁ with ⟨q₁, hq₁, rfl⟩
          rcases Finset.mem_map.mp hb₂ with ⟨q₂, hq₂, rfl⟩
          have hq_ne' : q₁ ≠ q₂ := fun h => hne (by subst h; rfl)
          have hnc : ¬ Conflict₂ q₁ q₂ := hQd_indep q₁ hq₁ q₂ hq₂ hq_ne'
          have hnc' : ¬ Conflict₂ q₂ q₁ := fun h => hnc (hC2_symm q₂ q₁ h)
          have hx00 : q₁.1 + p.1 ≠ q₂.1 + p.1 := fun h =>
            hnc (Or.inl (Or.inl (add_right_cancel h)))
          have hx01 : q₁.1 + p.1 ≠ q₂.1 + p.1 + d := by
            intro h
            apply hnc; exact Or.inl (Or.inr (add_right_cancel (by rw [h]; abel)))
          have hx10 : q₁.1 + p.1 + d ≠ q₂.1 + p.1 := by
            intro h
            apply hnc'; exact Or.inl (Or.inr (add_right_cancel (by rw [← h]; abel)))
          have hx11 : q₁.1 + p.1 + d ≠ q₂.1 + p.1 + d := fun h =>
            hx00 (add_right_cancel h)
          have hy00 : q₁.2 + p.2 ≠ q₂.2 + p.2 := fun h =>
            hnc (Or.inr (Or.inl (Or.inl (add_right_cancel h))))
          have hy01 : q₁.2 + p.2 ≠ q₂.2 + p.2 + d := by
            intro h
            apply hnc; exact Or.inr (Or.inl (Or.inr (add_right_cancel (by rw [h]; abel))))
          have hy10 : q₁.2 + p.2 + d ≠ q₂.2 + p.2 := by
            intro h
            apply hnc'; exact Or.inr (Or.inl (Or.inr (add_right_cancel (by rw [← h]; abel))))
          have hy11 : q₁.2 + p.2 + d ≠ q₂.2 + p.2 + d := fun h =>
            hy00 (add_right_cancel h)
          have hz00 : (q₁.1 + p.1) + (q₁.2 + p.2) ≠ (q₂.1 + p.1) + (q₂.2 + p.2) := by
            intro h
            apply hnc; exact Or.inr (Or.inr (Or.inl (add_right_cancel (by
              calc
                (q₁.1 + q₁.2) + (p.1 + p.2) = (q₁.1 + p.1) + (q₁.2 + p.2) := by abel
                _ = (q₂.1 + p.1) + (q₂.2 + p.2) := h
                _ = (q₂.1 + q₂.2) + (p.1 + p.2) := by abel))))
          have hz01 : (q₁.1 + p.1) + (q₁.2 + p.2) ≠ (q₂.1 + p.1) + (q₂.2 + p.2) + d := by
            intro h
            apply hnc; exact Or.inr (Or.inr (Or.inr (add_right_cancel (by
              calc
                (q₁.1 + q₁.2) + (p.1 + p.2) = (q₁.1 + p.1) + (q₁.2 + p.2) := by abel
                _ = (q₂.1 + p.1) + (q₂.2 + p.2) + d := h
                _ = (q₂.1 + q₂.2 + d) + (p.1 + p.2) := by abel))))
          have hz10 : (q₁.1 + p.1) + (q₁.2 + p.2) + d ≠ (q₂.1 + p.1) + (q₂.2 + p.2) := by
            intro h
            apply hnc'; exact Or.inr (Or.inr (Or.inr (add_right_cancel (by
              calc
                (q₂.1 + q₂.2) + (p.1 + p.2) = (q₂.1 + p.1) + (q₂.2 + p.2) := by abel
                _ = (q₁.1 + p.1) + (q₁.2 + p.2) + d := h.symm
                _ = (q₁.1 + q₁.2 + d) + (p.1 + p.2) := by abel))))
          have hz11 : (q₁.1 + p.1) + (q₁.2 + p.2) + d ≠ (q₂.1 + p.1) + (q₂.2 + p.2) + d :=
            fun h => hz00 (add_right_cancel h)
          simp only [S₂, addRightEmbedding_apply, Prod.fst_add, Prod.snd_add]
          exact disjoint_S2_coords hx00 hx01 hx10 hx11 hy00 hy01 hy10 hy11 hz00 hz01 hz10 hz11
        have hBad_sub : Bad_dp p ⊆
            Finset.univ.filter (fun ω : Ω => (τ + ε) * (Qp.card : ℝ) ≤ ∑ pt ∈ Qp, E₂ d pt ω) := by
          intro ω hω
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          have hgt : (τ + ε) * (Q_d.card : ℝ) < ((Qp ∩ S d (A_of ω)).card : ℝ) :=
            (Finset.mem_filter.mp hω).2
          have hsum_eq : ∑ pt ∈ Qp, E₂ d pt ω = ((Qp ∩ S d (A_of ω)).card : ℝ) := by
            have h1 : ∀ pt ∈ Qp, E₂ d pt ω = if pt ∈ S d (A_of ω) then (1 : ℝ) else 0 := fun pt _ =>
              hE₂_ind d pt ω
            rw [Finset.sum_congr rfl h1, Finset.sum_boole, Finset.filter_mem_eq_inter]
          rw [hsum_eq, hQp_card]
          exact hgt.le
        calc
          ((Bad_dp p).card : ℝ) / (Fintype.card Ω : ℝ)
              ≤ ((Finset.univ.filter (fun ω : Ω =>
                  (τ + ε) * (Qp.card : ℝ) ≤ ∑ pt ∈ Qp, E₂ d pt ω)).card : ℝ) /
                  (Fintype.card Ω : ℝ) := by
            gcongr
          _ ≤ Real.exp (-2 * ε ^ 2 * (Qp.card : ℝ)) :=
            finite_product_hoeffding_upper Qp (S₂ d) (E₂ d) τ ε hε.le
              (fun b _ => hE₂_dep d b) hQp_disj (fun b _ => hE₂_bool d b)
              (fun b _ => hE₂_mean d hd b)
          _ ≤ Real.exp (-2 * ε ^ 2 * (N / 6)) := by
            apply Real.exp_le_exp.mpr
            rw [hQp_card]
            nlinarith [sq_nonneg ε]
      have hcard_Bad_d : (Bad_d.card : ℝ) ≤ ∑ p : G × G, ((Bad_dp p).card : ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le : Bad_d.card ≤ ∑ p : G × G, (Bad_dp p).card)
      calc
        (Bad_d.card : ℝ) / (Fintype.card Ω : ℝ)
            ≤ (∑ p : G × G, ((Bad_dp p).card : ℝ)) / (Fintype.card Ω : ℝ) := by
          gcongr
        _ = ∑ p : G × G, ((Bad_dp p).card : ℝ) / (Fintype.card Ω : ℝ) := Finset.sum_div _ _ _
        _ ≤ ∑ _p : G × G, Real.exp (-2 * ε ^ 2 * (N / 6)) :=
          Finset.sum_le_sum fun p _ => hBad_dp_prob p
        _ = N ^ 2 * Real.exp (-2 * ε ^ 2 * (N / 6)) := by
          simp [N, Fintype.card_prod]
          ring
    · intro ω hω_not
      have hall : ∀ p : G × G,
          (((Q_d.map (addRightEmbedding p)) ∩ S d (A_of ω)).card : ℝ) ≤ (τ + ε) * (Q_d.card : ℝ) := by
        intro p
        by_contra! hgt
        apply hω_not
        exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_univ p,
          Finset.mem_filter.mpr ⟨Finset.mem_univ ω, hgt⟩⟩
      have hdc := double_counting_translate Q_d (S d (A_of ω))
      have hsum_le : (Q_d.card : ℝ) * ((S d (A_of ω)).card : ℝ) ≤
          ∑ _p : G × G, (τ + ε) * (Q_d.card : ℝ) := by
        rw [← hdc]
        exact Finset.sum_le_sum fun p _ => hall p
      have hrhs : (∑ _p : G × G, (τ + ε) * (Q_d.card : ℝ)) =
          (Q_d.card : ℝ) * ((τ + ε) * N ^ 2) := by
        simp [N, Fintype.card_prod]
        ring
      rw [hrhs] at hsum_le
      exact le_of_mul_le_mul_left hsum_le hQd_pos
  -- Step 3: Choose Bad_d for each d ≠ 0 and combine via union bound
  open scoped Classical in
  let NZ : Finset G := Finset.univ.filter (fun d => d ≠ 0)
  have hBad₂_exists : ∃ Bad₂All : Finset Ω,
      ((Bad₂All.card : ℝ) / (Fintype.card Ω : ℝ) ≤
        N ^ 3 * Real.exp (-2 * ε ^ 2 * (N / 6))) ∧
      (∀ ω : Ω, ω ∉ Bad₂All → ∀ d : G, d ≠ 0 → ((S d (A_of ω)).card : ℝ) ≤ (τ + ε) * N ^ 2) := by
    choose Bad_fn hBad_prob hBad_ok using hBad₂_for_d
    let Bad₂All : Finset Ω := NZ.attach.biUnion (fun d => Bad_fn d.1 (Finset.mem_filter.mp d.2).2)
    refine ⟨Bad₂All, ?_, ?_⟩
    · have hle : (Bad₂All.card : ℝ) ≤
          ∑ d ∈ NZ.attach, ((Bad_fn d.1 (Finset.mem_filter.mp d.2).2).card : ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le : Bad₂All.card ≤ _)
      calc
        (Bad₂All.card : ℝ) / (Fintype.card Ω : ℝ)
            ≤ (∑ d ∈ NZ.attach, ((Bad_fn d.1 (Finset.mem_filter.mp d.2).2).card : ℝ)) /
                (Fintype.card Ω : ℝ) := by gcongr
        _ = ∑ d ∈ NZ.attach, ((Bad_fn d.1 (Finset.mem_filter.mp d.2).2).card : ℝ) /
              (Fintype.card Ω : ℝ) := Finset.sum_div _ _ _
        _ ≤ ∑ _d ∈ NZ.attach, N ^ 2 * Real.exp (-2 * ε ^ 2 * (N / 6)) :=
          Finset.sum_le_sum fun d _ => hBad_prob d.1 (Finset.mem_filter.mp d.2).2
        _ = (NZ.card : ℝ) * (N ^ 2 * Real.exp (-2 * ε ^ 2 * (N / 6))) := by simp
        _ ≤ N * (N ^ 2 * Real.exp (-2 * ε ^ 2 * (N / 6))) := by
          gcongr
          dsimp [N]
          exact_mod_cast (Finset.card_filter_le Finset.univ (fun d : G => d ≠ 0) :
            NZ.card ≤ Fintype.card G)
        _ = N ^ 3 * Real.exp (-2 * ε ^ 2 * (N / 6)) := by ring
    · intro ω hω d hd
      apply hBad_ok d hd ω
      intro hmem
      apply hω
      exact Finset.mem_biUnion.mpr
        ⟨⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ d, hd⟩⟩, Finset.mem_attach _ _, hmem⟩
  rcases hBad₂_exists with ⟨Bad₂All, hBad₂_prob, hBad₂_ok⟩
  open scoped Classical in
  let Bad₁All : Finset Ω := (Finset.univ : Finset (G × G)).biUnion Bad₁
  have hBad₁_prob : (Bad₁All.card : ℝ) / (Fintype.card Ω : ℝ) ≤
      N ^ 2 * Real.exp (-2 * ε ^ 2 * (N / 3)) := by
    have hle : (Bad₁All.card : ℝ) ≤ ∑ p : G × G, ((Bad₁ p).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le : Bad₁All.card ≤ _)
    calc
      (Bad₁All.card : ℝ) / (Fintype.card Ω : ℝ)
          ≤ (∑ p : G × G, ((Bad₁ p).card : ℝ)) / (Fintype.card Ω : ℝ) := by gcongr
      _ = ∑ p : G × G, ((Bad₁ p).card : ℝ) / (Fintype.card Ω : ℝ) := Finset.sum_div _ _ _
      _ ≤ ∑ _p : G × G, Real.exp (-2 * ε ^ 2 * (N / 3)) :=
        Finset.sum_le_sum fun p _ => hBad₁_prob p
      _ = N ^ 2 * Real.exp (-2 * ε ^ 2 * (N / 3)) := by
        simp [N, Fintype.card_prod]
        ring
  have hn1' : N ^ 2 * Real.exp (-2 * ε ^ 2 * (N / 3)) < 1 / 3 := by
    have h1 : N ^ 2 ≤ N ^ 3 := by
      have hN1 : 1 ≤ N := by rw [hN_eq]; exact_mod_cast Nat.one_le_pow n 2 (by omega)
      nlinarith
    have hexp_eq : -2 * ε ^ 2 * (N / 3) = -(2 * ε ^ 2 / 3) * N := by ring
    rw [hexp_eq]
    calc
      N ^ 2 * Real.exp (-(2 * ε ^ 2 / 3) * N)
          ≤ N ^ 3 * Real.exp (-(2 * ε ^ 2 / 3) * N) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ < 1 / 3 := by simpa [hN_eq] using hn1
  have hn2' : N ^ 3 * Real.exp (-2 * ε ^ 2 * (N / 6)) < 1 / 3 := by
    have hexp_eq : -2 * ε ^ 2 * (N / 6) = -(2 * ε ^ 2 / 6) * N := by ring
    rw [hexp_eq]
    simpa [hN_eq] using hn2
  have hcard_Ω_pos : (0 : ℝ) < (Fintype.card Ω : ℝ) := by positivity
  have htotal_lt : ((Bad₁All ∪ Bad₂All).card : ℝ) < (Fintype.card Ω : ℝ) := by
    have hdiv_lt : ((Bad₁All ∪ Bad₂All).card : ℝ) / (Fintype.card Ω : ℝ) < 1 := by
      calc
        ((Bad₁All ∪ Bad₂All).card : ℝ) / (Fintype.card Ω : ℝ)
            ≤ ((Bad₁All.card : ℝ) + (Bad₂All.card : ℝ)) / (Fintype.card Ω : ℝ) := by
          gcongr
          exact_mod_cast Finset.card_union_le Bad₁All Bad₂All
        _ = (Bad₁All.card : ℝ) / (Fintype.card Ω : ℝ) +
              (Bad₂All.card : ℝ) / (Fintype.card Ω : ℝ) := add_div _ _ _
        _ ≤ N ^ 2 * Real.exp (-2 * ε ^ 2 * (N / 3)) +
              N ^ 3 * Real.exp (-2 * ε ^ 2 * (N / 6)) := add_le_add hBad₁_prob hBad₂_prob
        _ < 1 / 3 + 1 / 3 := add_lt_add hn1' hn2'
        _ < 1 := by norm_num
    exact (div_lt_one hcard_Ω_pos).mp hdiv_lt
  have htotal_nat_lt : (Bad₁All ∪ Bad₂All).card < (Finset.univ : Finset Ω).card := by
    rw [Finset.card_univ]
    exact_mod_cast htotal_lt
  have hex_good : ∃ ω : Ω, ω ∉ Bad₁All ∪ Bad₂All := by
    by_contra! hsub
    have hle : (Finset.univ : Finset Ω).card ≤ (Bad₁All ∪ Bad₂All).card :=
      Finset.card_le_card (fun ω _ => hsub ω)
    omega
  rcases hex_good with ⟨ω, hω_good⟩
  have hω1 : ω ∉ Bad₁All := fun h => hω_good (Finset.mem_union_left Bad₂All h)
  have hω2 : ω ∉ Bad₂All := fun h => hω_good (Finset.mem_union_right Bad₁All h)
  refine ⟨A_of ω, ?_, hBad₂_ok ω hω2⟩
  have hall1 : ∀ p : G × G,
      (α - ε) * (Q.card : ℝ) ≤ (((Q.map (addRightEmbedding p)) ∩ A_of ω).card : ℝ) := by
    intro p
    by_contra! hlt
    apply hω1
    exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_univ p,
      Finset.mem_filter.mpr ⟨Finset.mem_univ ω, hlt⟩⟩
  have hdc1 := double_counting_translate Q (A_of ω)
  have hsum_ge : ∑ _p : G × G, (α - ε) * (Q.card : ℝ) ≤
      (Q.card : ℝ) * ((A_of ω).card : ℝ) := by
    rw [← hdc1]
    exact Finset.sum_le_sum fun p _ => hall1 p
  have hlhs : (∑ _p : G × G, (α - ε) * (Q.card : ℝ)) =
      (Q.card : ℝ) * ((α - ε) * N ^ 2) := by
    simp [N, Fintype.card_prod]
    ring
  rw [hlhs] at hsum_ge
  exact le_of_mul_le_mul_left hsum_ge hQ_pos

/- ### 5. Lower Bound and the Value `C = 4` in Ben Green's Open Problem 19 -/

private lemma ratio_eq_formula (B_card q c : ℝ) (hB_pos : 0 < B_card) (hq_pos : 0 < q) :
    (B_card / q ^ 5) / ((B_card / (2 * q ^ 2)) ^ c) =
      (2 : ℝ) ^ c * (q / B_card) ^ (c - 1) * q ^ (c - 4) := by
  rw [Real.div_rpow hB_pos.le (mul_nonneg zero_le_two (sq_nonneg q)),
    Real.mul_rpow (by norm_num) (sq_nonneg q),
    ← Real.rpow_natCast q 2, ← Real.rpow_mul hq_pos.le]
  have hb1 : B_card / B_card ^ c = B_card ^ (1 - c) := by
    rw [Real.rpow_sub hB_pos, Real.rpow_one]
  have hdiv_qb : (q / B_card) ^ (c - 1) = q ^ (c - 1) / B_card ^ (c - 1) :=
    Real.div_rpow hq_pos.le hB_pos.le (c - 1)
  have hb_neg : (B_card ^ (c - 1))⁻¹ = B_card ^ (1 - c) := by
    rw [← Real.rpow_neg hB_pos.le]
    congr 1
    ring
  have hq_comb : q ^ (c - 1) * q ^ (c - 4) = q ^ (2 * c - 5) := by
    rw [← Real.rpow_add hq_pos]
    congr 1
    ring
  have hq2c : q ^ ((2 : ℕ) * c) = q ^ (2 * c) := by norm_num
  have hq5 : q ^ (5 : ℕ) = q ^ (5 : ℝ) := (Real.rpow_natCast q 5).symm
  have hq_sub : q ^ (2 * c) / q ^ (5 : ℝ) = q ^ (2 * c - 5) :=
    (Real.rpow_sub hq_pos (2 * c) 5).symm
  calc
    (B_card / q ^ 5) / (B_card ^ c / ((2 : ℝ) ^ c * q ^ ((2 : ℕ) * c)))
        = (2 : ℝ) ^ c * (B_card / B_card ^ c) * (q ^ ((2 : ℕ) * c) / q ^ (5 : ℕ)) := by
      field_simp
    _ = (2 : ℝ) ^ c * B_card ^ (1 - c) * q ^ (2 * c - 5) := by
      rw [hb1, hq2c, hq5, hq_sub]
    _ = (2 : ℝ) ^ c * (q ^ (c - 1) / B_card ^ (c - 1)) * q ^ (c - 4) := by
      rw [← hq_comb, div_eq_mul_inv, hb_neg]
      ring
    _ = (2 : ℝ) ^ c * (q / B_card) ^ (c - 1) * q ^ (c - 4) := by
      rw [hdiv_qb]

private lemma ratio_bound_pow2 (c : ℝ) (hc : c < 4) (d : ℕ) (B_card q : ℝ)
    (hB_pos : 0 < B_card) (hq_pos : 0 < q)
    (hqB_ge1 : 1 ≤ q / B_card)
    (hqB_le : q / B_card ≤ (2 : ℝ) ^ (4 * (d : ℝ) + 1))
    (hq_low : (2 : ℝ) ^ ((d : ℝ) ^ 2) ≤ q) :
    (2 : ℝ) ^ c * (q / B_card) ^ (c - 1) * q ^ (c - 4) ≤
      (2 : ℝ) ^ (c + (4 * (d : ℝ) + 1) * |c - 1| - (4 - c) * (d : ℝ) ^ 2) := by
  have hc4_pos : 0 < 4 - c := by linarith
  have hqB_rpow : (q / B_card) ^ (c - 1) ≤ (2 : ℝ) ^ ((4 * (d : ℝ) + 1) * |c - 1|) := by
    have hpow_ge : (q / B_card) ^ (c - 1) ≤ (q / B_card) ^ |c - 1| :=
      Real.rpow_le_rpow_of_exponent_le hqB_ge1 (le_abs_self (c - 1))
    have hbase_le : (q / B_card) ^ |c - 1| ≤ ((2 : ℝ) ^ (4 * (d : ℝ) + 1)) ^ |c - 1| :=
      Real.rpow_le_rpow (div_nonneg hq_pos.le hB_pos.le) hqB_le (abs_nonneg _)
    calc
      (q / B_card) ^ (c - 1) ≤ ((2 : ℝ) ^ (4 * (d : ℝ) + 1)) ^ |c - 1| := hpow_ge.trans hbase_le
      _ = (2 : ℝ) ^ ((4 * (d : ℝ) + 1) * |c - 1|) := by rw [← Real.rpow_mul (by norm_num)]
  have hq_rpow : q ^ (c - 4) ≤ (2 : ℝ) ^ (-(4 - c) * (d : ℝ) ^ 2) := by
    have h1 : q ^ (c - 4) ≤ ((2 : ℝ) ^ ((d : ℝ) ^ 2)) ^ (c - 4) := by
      rw [show c - 4 = -(4 - c) by ring, Real.rpow_neg hq_pos.le,
        Real.rpow_neg (Real.rpow_pos_of_pos (by norm_num) _).le,
        inv_le_inv₀ (Real.rpow_pos_of_pos hq_pos _)
          (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos (by norm_num) _) _)]
      exact Real.rpow_le_rpow (Real.rpow_pos_of_pos (by norm_num) _).le hq_low hc4_pos.le
    calc
      q ^ (c - 4) ≤ ((2 : ℝ) ^ ((d : ℝ) ^ 2)) ^ (c - 4) := h1
      _ = (2 : ℝ) ^ (-(4 - c) * (d : ℝ) ^ 2) := by
        rw [← Real.rpow_mul (by norm_num)]
        congr 1
        ring
  have h2_pos : (0 : ℝ) < 2 := by norm_num
  have h2c_nn : (0 : ℝ) ≤ (2 : ℝ) ^ c := (Real.rpow_pos_of_pos h2_pos c).le
  have h12 : (2 : ℝ) ^ c * (q / B_card) ^ (c - 1) ≤
      (2 : ℝ) ^ c * (2 : ℝ) ^ ((4 * (d : ℝ) + 1) * |c - 1|) :=
    mul_le_mul_of_nonneg_left hqB_rpow h2c_nn
  have h123 : (2 : ℝ) ^ c * (q / B_card) ^ (c - 1) * q ^ (c - 4) ≤
      (2 : ℝ) ^ c * (2 : ℝ) ^ ((4 * (d : ℝ) + 1) * |c - 1|) *
        (2 : ℝ) ^ (-(4 - c) * (d : ℝ) ^ 2) :=
    mul_le_mul h12 hq_rpow (Real.rpow_pos_of_pos hq_pos _).le
      (mul_nonneg h2c_nn (Real.rpow_pos_of_pos h2_pos _).le)
  have hexp_eq :
      (2 : ℝ) ^ c * (2 : ℝ) ^ ((4 * (d : ℝ) + 1) * |c - 1|) *
          (2 : ℝ) ^ (-(4 - c) * (d : ℝ) ^ 2) =
        (2 : ℝ) ^ (c + (4 * (d : ℝ) + 1) * |c - 1| - (4 - c) * (d : ℝ) ^ 2) := by
    rw [← Real.rpow_add h2_pos, ← Real.rpow_add h2_pos]
    congr 1
    ring
  exact h123.trans_eq hexp_eq

/-- No exponent strictly less than 4 is valid. -/
theorem not_validExponent_of_lt_four {c : ℝ} (hc : c < 4) : ¬ ValidExponent c := by
  rintro ⟨K, hK, hValid⟩
  have hc4_pos : 0 < 4 - c := by linarith
  -- Pick k₀ : ℕ such that (2 : ℝ) ^ (-(k₀ : ℝ)) < K / 4
  have hK_pos : 0 < 4 / K := by positivity
  obtain ⟨k₀, hk₀⟩ := exists_nat_gt (4 / K)
  have hpow2_k0 : (2 : ℝ) ^ (-(k₀ : ℝ)) < K / 4 := by
    have hk₀_pos : (0 : ℝ) < (k₀ : ℝ) := by linarith
    have hk0_lt : (4 / K) < (2 : ℝ) ^ k₀ :=
      lt_of_lt_of_le hk₀ (by exact_mod_cast Nat.lt_two_pow_self.le)
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, inv_eq_one_div,
      div_lt_div_iff₀ (by positivity) (by norm_num)]
    calc
      1 * 4 = K * (4 / K) := by field_simp [hK.ne']
      _ < K * (2 : ℝ) ^ k₀ := mul_lt_mul_of_pos_left hk0_lt hK
  -- Pick d ≥ 3 large enough that (4 - c) * d^2 ≥ (4 * |c - 1|) * d + (c + |c - 1| + k₀)
  let A_lin : ℝ := 4 * |c - 1|
  let B_const : ℝ := c + |c - 1| + (k₀ : ℝ)
  obtain ⟨d, hd_gt⟩ := exists_nat_gt (max 3 ((A_lin + |B_const| + 1) / (4 - c)))
  have hd3 : 3 ≤ d := by
    have : (3 : ℝ) < (d : ℝ) := lt_of_le_of_lt (le_max_left _ _) hd_gt
    exact_mod_cast this.le
  have hd1 : 1 ≤ d := by omega
  have hd_quad : A_lin * (d : ℝ) + B_const ≤ (4 - c) * (d : ℝ) ^ 2 := by
    have hgt : (A_lin + |B_const| + 1) / (4 - c) < (d : ℝ) :=
      lt_of_le_of_lt (le_max_right _ _) hd_gt
    have h1 : A_lin + |B_const| + 1 < (d : ℝ) * (4 - c) := (div_lt_iff₀ hc4_pos).mp hgt
    have hd_ge1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
    have hmul : (A_lin + |B_const| + 1) * (d : ℝ) ≤ (4 - c) * (d : ℝ) ^ 2 := by
      nlinarith
    have hB : B_const ≤ |B_const| * (d : ℝ) := by
      calc
        B_const ≤ |B_const| := le_abs_self B_const
        _ = |B_const| * 1 := (mul_one _).symm
        _ ≤ |B_const| * (d : ℝ) := mul_le_mul_of_nonneg_left hd_ge1 (abs_nonneg _)
    nlinarith
  -- Instantiate Behrend with m = 2 ^ d
  let m : ℕ := 2 ^ d
  have hm2 : 2 ≤ m := by
    have : 2 ^ 1 ≤ 2 ^ d := Nat.pow_le_pow_right (by omega) hd1
    omega
  rcases behrend_ap3_free d m hd1 hm2 with ⟨B, hBM, hAP, hB_card⟩
  let M : ℕ := (2 * m - 1) ^ d
  have hM1 : 1 ≤ M := by
    have hbm : 1 ≤ 2 * m - 1 := by omega
    exact Nat.one_le_pow d (2 * m - 1) hbm
  let q : ℕ := 2 * M - 1
  have hq1 : 1 ≤ q := by omega
  have hq_nz : NeZero q := ⟨by omega⟩
  rcases ruzsa_szemeredi_triforce_density M hM1 B hBM hAP with ⟨W, hW, hα_eq, hτ_eq⟩
  let α : ℝ := ∑ u : ZMod q, ∑ v : ZMod q, ∑ w : ZMod q,
    (1 / (q : ℝ)) * (1 / (q : ℝ)) * (1 / (q : ℝ)) * W u v w
  let τ : ℝ := weightedTriforce (fun _ => 1 / (q : ℝ)) (fun _ => 1 / (q : ℝ))
    (fun _ => 1 / (q : ℝ)) W
  change α = (B.card : ℝ) / (q : ℝ) ^ 2 at hα_eq
  change τ = (B.card : ℝ) / (q : ℝ) ^ 5 at hτ_eq
  -- Bounds on B.card and q as powers of 2
  have hden_le : d * (m - 1) ^ 2 + 1 ≤ 2 ^ (3 * d) := by
    have h1 : m - 1 ≤ m := Nat.sub_le m 1
    have h2 : (m - 1) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left h1 2
    have h3 : d * (m - 1) ^ 2 + 1 ≤ d * m ^ 2 + m ^ 2 := by
      have hm_pos : 1 ≤ m ^ 2 := Nat.one_le_pow 2 m (by omega)
      nlinarith
    have hpow_add_le : ∀ k : ℕ, 1 ≤ k → k + 1 ≤ 2 ^ k := by
      intro k hk
      induction k with
      | zero => omega
      | succ t ih =>
        by_cases ht : t = 0
        · subst ht; omega
        · have ht1 : 1 ≤ t := Nat.one_le_iff_ne_zero.mpr ht
          have hih := ih ht1
          have : 1 ≤ 2 ^ t := Nat.one_le_pow t 2 (by omega)
          rw [pow_succ']
          omega
    have h4 : d + 1 ≤ 2 ^ d := hpow_add_le d hd1
    calc
      d * (m - 1) ^ 2 + 1 ≤ (d + 1) * m ^ 2 := by nlinarith
      _ ≤ 2 ^ d * m ^ 2 := Nat.mul_le_mul_right (m ^ 2) h4
      _ = 2 ^ (3 * d) := by
        dsimp [m]
        rw [← pow_mul, ← pow_add]
        congr 1
        ring
  have hB_low : (2 : ℝ) ^ ((d : ℝ) ^ 2 - 3 * (d : ℝ)) ≤ (B.card : ℝ) := by
    have hd2_ge_3d : 3 * d ≤ d ^ 2 := by nlinarith
    have hmd : m ^ d = 2 ^ (d ^ 2) := by
      dsimp [m]
      rw [← pow_mul, sq]
    have hden_real : ((d * (m - 1) ^ 2 + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (3 * d) := by
      exact_mod_cast hden_le
    have hden_pos : (0 : ℝ) < ((d * (m - 1) ^ 2 + 1 : ℕ) : ℝ) := by positivity
    calc
      (2 : ℝ) ^ ((d : ℝ) ^ 2 - 3 * (d : ℝ))
          = (2 : ℝ) ^ (d ^ 2) / (2 : ℝ) ^ (3 * d) := by
        rw [Real.rpow_sub (by norm_num)]
        norm_cast
      _ ≤ (2 : ℝ) ^ (d ^ 2) / ((d * (m - 1) ^ 2 + 1 : ℕ) : ℝ) := by
        gcongr
      _ = (m ^ d : ℝ) / ((d * (m - 1) ^ 2 + 1 : ℕ) : ℝ) := by
        have hmd_r : ((2 : ℝ) ^ (d ^ 2)) = (m ^ d : ℝ) := by exact_mod_cast hmd.symm
        rw [hmd_r]
      _ ≤ (B.card : ℝ) := hB_card
  have hB_pos : (0 : ℝ) < (B.card : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos (by norm_num) _) hB_low
  have hB_le_M : B.card ≤ M := by
    have hsub : B ⊆ Finset.range M := fun b hb => Finset.mem_range.mpr (hBM b hb)
    exact (Finset.card_le_card hsub).trans (by simp)
  have hM_le_q : M ≤ q := by omega
  have hB_le_q : (B.card : ℝ) ≤ (q : ℝ) := by exact_mod_cast hB_le_M.trans hM_le_q
  have hq_low_nat : 2 ^ (d ^ 2) ≤ q := by
    have h2 : m ≤ 2 * m - 1 := by omega
    have h3 : m ^ d ≤ M := Nat.pow_le_pow_left h2 d
    have hmd : m ^ d = 2 ^ (d ^ 2) := by
      dsimp [m]
      rw [← pow_mul, sq]
    omega
  have hq_low : (2 : ℝ) ^ ((d : ℝ) ^ 2) ≤ (q : ℝ) := by
    have h : ((2 ^ (d ^ 2) : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq_low_nat
    have h2 : (2 : ℝ) ^ ((d : ℝ) ^ 2) = ((2 ^ (d ^ 2) : ℕ) : ℝ) := by
      have : ((d : ℝ) ^ 2) = ((d ^ 2 : ℕ) : ℝ) := by push_cast; rfl
      rw [this, Real.rpow_natCast]
      push_cast; rfl
    linarith
  have hq_high_nat : q ≤ 2 ^ (d ^ 2 + d + 1) := by
    have h1 : 2 * m - 1 ≤ 2 ^ (d + 1) := by
      dsimp [m]
      rw [pow_succ']
      omega
    have h2 : M ≤ (2 ^ (d + 1)) ^ d := Nat.pow_le_pow_left h1 d
    have h3 : (2 ^ (d + 1)) ^ d = 2 ^ (d ^ 2 + d) := by
      rw [← pow_mul]
      congr 1
      ring
    have h4 : q ≤ 2 * 2 ^ (d ^ 2 + d) := by omega
    rwa [← pow_succ'] at h4
  have hq_high : (q : ℝ) ≤ (2 : ℝ) ^ ((d : ℝ) ^ 2 + (d : ℝ) + 1) := by
    have h : (q : ℝ) ≤ ((2 ^ (d ^ 2 + d + 1) : ℕ) : ℝ) := by exact_mod_cast hq_high_nat
    have h2 : (2 : ℝ) ^ ((d : ℝ) ^ 2 + (d : ℝ) + 1) = ((2 ^ (d ^ 2 + d + 1) : ℕ) : ℝ) := by
      have : ((d : ℝ) ^ 2 + (d : ℝ) + 1) = ((d ^ 2 + d + 1 : ℕ) : ℝ) := by push_cast; rfl
      rw [this, Real.rpow_natCast]
      push_cast; rfl
    linarith
  have hq_ge4 : 4 ≤ q := by
    have : 2 ^ 2 ≤ 2 ^ (d ^ 2) := Nat.pow_le_pow_right (by omega) (by nlinarith)
    omega
  have hq_pos : (0 : ℝ) < (q : ℝ) := by positivity
  -- Verify 0 < α / 2 < 1
  have hα_pos : 0 < α := by
    rw [hα_eq]
    exact div_pos hB_pos (sq_pos_of_pos hq_pos)
  have hα_lt_one : α < 1 := by
    rw [hα_eq, div_lt_one (sq_pos_of_pos hq_pos)]
    have hq_gt1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 1 < q)
    nlinarith
  let α' : ℝ := α / 2
  have hα'_pos : 0 < α' := half_pos hα_pos
  have hα'_lt : α' < 1 := by dsimp [α']; linarith
  -- Bound τ / (α' ^ c) < K / 4
  have hqB_ge1 : 1 ≤ (q : ℝ) / (B.card : ℝ) := (one_le_div hB_pos).mpr hB_le_q
  have hqB_le : (q : ℝ) / (B.card : ℝ) ≤ (2 : ℝ) ^ (4 * (d : ℝ) + 1) := by
    have h1 : (q : ℝ) / (B.card : ℝ) ≤
        (2 : ℝ) ^ ((d : ℝ) ^ 2 + (d : ℝ) + 1) / (B.card : ℝ) :=
      div_le_div_of_nonneg_right hq_high hB_pos.le
    have h2 : (2 : ℝ) ^ ((d : ℝ) ^ 2 + (d : ℝ) + 1) / (B.card : ℝ) ≤
        (2 : ℝ) ^ ((d : ℝ) ^ 2 + (d : ℝ) + 1) / (2 : ℝ) ^ ((d : ℝ) ^ 2 - 3 * (d : ℝ)) :=
      div_le_div_of_nonneg_left (Real.rpow_pos_of_pos (by norm_num) _).le
        (Real.rpow_pos_of_pos (by norm_num) _) hB_low
    calc
      (q : ℝ) / (B.card : ℝ)
          ≤ (2 : ℝ) ^ ((d : ℝ) ^ 2 + (d : ℝ) + 1) / (2 : ℝ) ^ ((d : ℝ) ^ 2 - 3 * (d : ℝ)) :=
        h1.trans h2
      _ = (2 : ℝ) ^ (4 * (d : ℝ) + 1) := by
        rw [← Real.rpow_sub (by norm_num)]
        congr 1
        ring
  have hα'_rpow_pos : 0 < α' ^ c := Real.rpow_pos_of_pos hα'_pos c
  have hτ_lt : τ < (K / 4) * α' ^ c := by
    have hα'_eq : α' = (B.card : ℝ) / (2 * (q : ℝ) ^ 2) := by
      dsimp [α']
      rw [hα_eq]
      ring
    have hratio : τ / α' ^ c =
        (2 : ℝ) ^ c * ((q : ℝ) / (B.card : ℝ)) ^ (c - 1) * (q : ℝ) ^ (c - 4) := by
      rw [hτ_eq, hα'_eq]
      exact ratio_eq_formula (B.card : ℝ) (q : ℝ) c hB_pos hq_pos
    have hbound : (2 : ℝ) ^ c * ((q : ℝ) / (B.card : ℝ)) ^ (c - 1) * (q : ℝ) ^ (c - 4) ≤
        (2 : ℝ) ^ (c + (4 * (d : ℝ) + 1) * |c - 1| - (4 - c) * (d : ℝ) ^ 2) :=
      ratio_bound_pow2 c hc d (B.card : ℝ) (q : ℝ) hB_pos hq_pos hqB_ge1 hqB_le hq_low
    have hpow_le : (2 : ℝ) ^ (c + (4 * (d : ℝ) + 1) * |c - 1| - (4 - c) * (d : ℝ) ^ 2) ≤
        (2 : ℝ) ^ (-(k₀ : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      dsimp [A_lin, B_const] at hd_quad
      linarith
    rw [← div_lt_iff₀ hα'_rpow_pos, hratio]
    exact lt_of_le_of_lt (hbound.trans hpow_le) hpow2_k0
  -- Apply Mandache random corner upper bound with ε₀ := min (α / 2) ((K / 4) * α' ^ c)
  let ε₀ : ℝ := min (α / 2) ((K / 4) * α' ^ c)
  have hε₀_pos : 0 < ε₀ := lt_min (half_pos hα_pos) (mul_pos (div_pos hK (by norm_num)) hα'_rpow_pos)
  have hMand := mandache_random_corner_upper hq1 W hW ε₀ hε₀_pos
  have hVal := hValid α' hα'_pos hα'_lt
  obtain ⟨n, hMand_n, hVal_n⟩ := (hMand.and hVal).exists
  rcases hMand_n with ⟨A, hA_card, hA_corners⟩
  have hA_ge : (A.card : ℝ) ≥ α' * (Fintype.card (𝔽₂ n) : ℝ) ^ 2 := by
    have h1 : α' ≤ α - ε₀ := by
      have : ε₀ ≤ α / 2 := min_le_left _ _
      dsimp [α']
      linarith
    have hN_sq_nn : 0 ≤ (Fintype.card (𝔽₂ n) : ℝ) ^ 2 := sq_nonneg _
    calc
      α' * (Fintype.card (𝔽₂ n) : ℝ) ^ 2 ≤ (α - ε₀) * (Fintype.card (𝔽₂ n) : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right h1 hN_sq_nn
      _ ≤ (A.card : ℝ) := hA_card
  rcases hVal_n A hA_ge with ⟨d_corner, hd_ne, hSd_ge⟩
  have hSd_le := hA_corners d_corner hd_ne
  have hN_pos : (0 : ℝ) < (Fintype.card (𝔽₂ n) : ℝ) := by
    have : 0 < Fintype.card (𝔽₂ n) := Fintype.card_pos
    exact_mod_cast this
  have hN_sq_pos : 0 < (Fintype.card (𝔽₂ n) : ℝ) ^ 2 := sq_pos_of_pos hN_pos
  have hcomb : K * α' ^ c ≤ τ + ε₀ := by
    have hmul : K * α' ^ c * (Fintype.card (𝔽₂ n) : ℝ) ^ 2 ≤
        (τ + ε₀) * (Fintype.card (𝔽₂ n) : ℝ) ^ 2 := hSd_ge.trans hSd_le
    exact le_of_mul_le_mul_right hmul hN_sq_pos
  have hε₀_le : ε₀ ≤ (K / 4) * α' ^ c := min_le_right _ _
  linarith

/-- Exact characterization of valid exponents for Green's Open Problem 19. -/
theorem validExponent_iff (c : ℝ) : ValidExponent c ↔ 4 ≤ c := by
  constructor
  · intro hv
    by_contra! hlt
    exact not_validExponent_of_lt_four hlt hv
  · exact validExponent_of_ge_four

/-- Ben Green's Open Problem 19, solved by Mandache and Fox–Sah–Sawhney–Stoner–Zhao: `C = 4`. -/
theorem green_19 : C = 4 := by
  have hset : {c : ℝ | ValidExponent c} = Set.Ici 4 := by
    ext c
    exact validExponent_iff c
  dsimp [C]
  rw [hset, csInf_Ici]

/-- Mandache's lower bound `C >= 3.13`, following from `green_19`. -/
theorem green_19.lower : C >= 3.13 := by
  rw [green_19]
  norm_num

/-- Upper bound `C <= 4`, following from `green_19`. -/
theorem green_19.upper : C <= 4 := by
  rw [green_19]

/- ### 6. Explicit Non-Vacuity & Sanity Witnesses -/

section NonVacuityExamples

/-- Non-zero vector `e₀ = (1, 0)` in `𝔽₂ 2`. -/
private def sampleD : 𝔽₂ 2 := ![1, 0]

private lemma sampleD_ne_zero : sampleD ≠ 0 := by
  intro h
  have h0 : sampleD 0 = (0 : 𝔽₂ 2) 0 := congrFun h 0
  simp [sampleD] at h0

/-- Explicit 3-element corner set in `𝔽₂ 2 × 𝔽₂ 2` with difference `sampleD`. -/
private def sampleCornerSet : Finset (𝔽₂ 2 × 𝔽₂ 2) :=
  {(![0, 0], ![0, 0]), (sampleD, ![0, 0]), (![0, 0], sampleD)}

example : IsCorner sampleCornerSet ![0, 0] ![0, 0] sampleD := by
  refine ⟨?_, ?_, ?_⟩
  · simp [sampleCornerSet]
  · simp only [sampleCornerSet, Finset.mem_insert, Finset.mem_singleton]
    right; left
    refine Prod.ext (funext fun i => by fin_cases i <;> simp [sampleD]) rfl
  · simp only [sampleCornerSet, Finset.mem_insert, Finset.mem_singleton]
    right; right
    refine Prod.ext rfl (funext fun i => by fin_cases i <;> simp [sampleD])

example : ¬ IsCorner sampleCornerSet ![1, 1] ![0, 0] sampleD := by
  intro ⟨h0, _, _⟩
  simp only [sampleCornerSet, Finset.mem_insert, Finset.mem_singleton] at h0
  rcases h0 with h | h | h
  · have := congrFun (congrArg Prod.fst h) 0; simp at this
  · have := congrFun (congrArg Prod.fst h) 1; simp [sampleD] at this
  · have := congrFun (congrArg Prod.fst h) 0; simp at this

example : ¬ IsCorner sampleCornerSet ![0, 0] ![0, 0] ![0, 1] := by
  intro ⟨_, h1, _⟩
  simp only [sampleCornerSet, Finset.mem_insert, Finset.mem_singleton] at h1
  rcases h1 with h | h | h
  · have := congrFun (congrArg Prod.fst h) 1; simp at this
  · have := congrFun (congrArg Prod.fst h) 1; simp [sampleD] at this
  · have := congrFun (congrArg Prod.fst h) 1; simp at this

example : 0 < (S sampleD sampleCornerSet).card := by
  rw [Finset.card_pos]
  refine ⟨(![0, 0], ![0, 0]), ?_⟩
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨by simp [sampleCornerSet], ?_, ?_⟩
  · simp only [sampleCornerSet, Finset.mem_insert, Finset.mem_singleton]
    right; left
    refine Prod.ext (funext fun i => by fin_cases i <;> simp [sampleD]) rfl
  · simp only [sampleCornerSet, Finset.mem_insert, Finset.mem_singleton]
    right; right
    refine Prod.ext rfl (funext fun i => by fin_cases i <;> simp [sampleD])

example : ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2,
    (1 / 2 : ℝ) * (1 / 2) * (1 / 2) * mandacheKernel i j k = 3 / 4 := by
  simp [mandacheKernel, Fin.sum_univ_two]
  norm_num

example : weightedTriforce (fun _ => (1 / 2 : ℝ)) (fun _ => (1 / 2 : ℝ))
    (fun _ => (1 / 2 : ℝ)) mandacheKernel = 13 / 32 :=
  mandacheKernel_triforce

example : (3 / 4 : ℝ) ^ 4 ≤ 13 / 32 := by
  have htri := weightedTriforce_ge_pow_four
    (fun _ : Fin 2 => (1 / 2 : ℝ)) (fun _ : Fin 2 => (1 / 2 : ℝ))
    (fun _ : Fin 2 => (1 / 2 : ℝ))
    (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num)
    (by simp) (by simp) (by simp)
    mandacheKernel
    (fun i j k => by dsimp [mandacheKernel]; split_ifs <;> norm_num)
    (fun i j k => by dsimp [mandacheKernel]; split_ifs <;> norm_num)
  have hmean : ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2,
      (1 / 2 : ℝ) * (1 / 2) * (1 / 2) * mandacheKernel i j k = 3 / 4 := by
    simp [mandacheKernel, Fin.sum_univ_two]
    norm_num
  rw [hmean, mandacheKernel_triforce] at htri
  exact htri

example : ∃ B : Finset ℕ,
    (∀ x ∈ B, x < 9) ∧
    (∀ x ∈ B, ∀ y ∈ B, ∀ z ∈ B, x + z = 2 * y → x = y ∧ y = z) ∧
    (4 : ℝ) / 3 ≤ (B.card : ℝ) := by
  have h := behrend_ap3_free 2 2 (by norm_num) (by norm_num)
  norm_num at h
  exact h

example :
    ∃ W : ZMod 9 → ZMod 9 → ZMod 9 → ℝ,
      (∀ u v w, W u v w = 0 ∨ W u v w = 1) ∧
      (∑ u : ZMod 9, ∑ v : ZMod 9, ∑ w : ZMod 9,
        (1 / (9 : ℝ)) * (1 / (9 : ℝ)) * (1 / (9 : ℝ)) * W u v w = 4 / 81) ∧
      weightedTriforce (fun _ => (1 / 9 : ℝ)) (fun _ => (1 / 9 : ℝ))
        (fun _ => (1 / 9 : ℝ)) W = 4 / 59049 := by
  have h := ruzsa_szemeredi_triforce_density 5 (by norm_num) {0, 1, 3, 4}
    (fun b hb => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl | rfl | rfl <;> omega)
    (fun x hx y hy z hz hap => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy hz
      rcases hx with rfl | rfl | rfl | rfl <;>
        rcases hy with rfl | rfl | rfl | rfl <;>
        rcases hz with rfl | rfl | rfl | rfl <;> omega)
  rcases h with ⟨W, hW01, hmean, htri⟩
  refine ⟨W, hW01, ?_, ?_⟩
  · norm_num at hmean ⊢
    exact hmean
  · norm_num at htri ⊢
    exact htri

example : ValidExponent 4 := (validExponent_iff 4).mpr le_rfl

example : ValidExponent 5 := validExponent_of_ge_four (by norm_num)

example : ¬ ValidExponent 3.99 := by
  intro h
  have h4 : (4 : ℝ) ≤ 3.99 := (validExponent_iff 3.99).mp h
  norm_num at h4

end NonVacuityExamples

end Green19

#print axioms Green19.weightedTriforce_ge_div_256
#print axioms Green19.weightedTriforce_ge_pow_four
#print axioms Green19.popular_corner_f2_pow_four
#print axioms Green19.validExponent_four
#print axioms Green19.validExponent_of_ge_four
#print axioms Green19.mandacheKernel_triforce
#print axioms Green19.behrend_ap3_free
#print axioms Green19.ruzsa_szemeredi_triforce_density
#print axioms Green19.mandache_random_corner_upper
#print axioms Green19.not_validExponent_of_lt_four
#print axioms Green19.validExponent_iff
#print axioms Green19.green_19
#print axioms Green19.green_19.lower
#print axioms Green19.green_19.upper
