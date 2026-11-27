import FormalConjectures.OptimizationConstants.«6a»
import Mathlib

/-!
# A lower bound for the abundance constant of union-closed families

Credit: Ronak Patel / Avon Labs (@ronak14p).
We use the independent and dependent union couplings of Sawin (arXiv:2211.11504),
as in Yu (arXiv:2212.00658) and Cambie (arXiv:2212.12500).
The numerical inequality below uses a cubic moment of the conditional absence
probabilities. A finite table of rational bounds certifies the resulting
one-variable inequalities by interpolation.
-/

/- Encode each set by the membership bits below a common finite cutoff. This encoding preserves unions and all coordinate frequencies. -/
section
namespace C6Intermediate
open Finset

def Cube : ℕ → Type
  | 0 => Unit
  | n+1 => Cube n × Bool

def encode (s : Finset ℕ) : (n : ℕ) → Cube n
  | 0 => ()
  | n+1 => (encode s n, decide (n ∈ s))

def join : (n : ℕ) → Cube n → Cube n → Cube n
  | 0, _, _ => ()
  | n+1, x, y => (join n x.1 y.1, x.2 || y.2)

inductive Coord : ℕ → Type
  | prev {n} : Coord n → Coord (n+1)
  | last {n} : Coord (n+1)

def index : {n : ℕ} → Coord n → ℕ
  | _, .prev i => index i
  | n+1, .last => n

def read : {n : ℕ} → Cube n → Coord n → Bool
  | _, x, .prev i => read x.1 i
  | _, x, .last => x.2

lemma read_encode {n : ℕ} (s : Finset ℕ) (i : Coord n) :
    read (encode s n) i = decide (index i ∈ s) := by
  induction i with
  | prev i ih => exact ih
  | last => rfl

lemma encode_union (s t : Finset ℕ) (n : ℕ) :
    encode (s ∪ t) n = join n (encode s n) (encode t n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [encode, join, ih] <;> rfl

lemma encode_agree (s t : Finset ℕ) (n : ℕ) (h : encode s n = encode t n) :
    ∀ i < n, i ∈ s ↔ i ∈ t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rcases Prod.mk.inj (show (encode s n, decide (n ∈ s)) =
        (encode t n, decide (n ∈ t)) from h) with ⟨h₁,h₂⟩
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact ih h₁ i hi
    · simpa using h₂

noncomputable instance cubeDecidableEq (n : ℕ) : DecidableEq (Cube n) := Classical.decEq _

/-- A finite Boolean-cube abundance bound implies the same lower bound for Tao's supremum. -/
theorem of_cube (c : ℝ) (hc : c ≤ 1)
    (cubeBound : ∀ n (S : Finset (Cube n)), 1 < S.card →
      (∀ x ∈ S, ∀ y ∈ S, join n x y ∈ S) →
      ∃ i : Coord n, c * S.card ≤ (S.filter fun x => read x i).card) :
    c ≤ Constant6a.C6a := by
  classical
  unfold Constant6a.C6a
  apply le_csSup
  · refine ⟨1, ?_⟩
    intro d hd
    let S : Finset (Finset ℕ) := {{0}}
    obtain ⟨i, hi⟩ := hd S (by decide) (by decide)
    simpa [S] using hi.trans (Nat.cast_le.mpr (card_filter_le ..))
  · intro A hne hclosed
    by_cases h0 : A.card = 0
    · exact ⟨0, by simp [card_eq_zero.mp h0]⟩
    by_cases h1 : A.card = 1
    · obtain ⟨s, rfl⟩ := card_eq_one.mp h1
      obtain ⟨i, hi⟩ := nonempty_iff_ne_empty.mpr (show s ≠ ∅ from fun h => hne (by rw [h]))
      exact ⟨i, by simpa [Finset.filter_singleton, hi] using hc⟩
    let n := A.sup (fun s => s.sup id) + 1
    let enc := fun s : Finset ℕ => encode s n
    let S := A.image enc
    have inside (s : Finset ℕ) (hs : s ∈ A) (i : ℕ) (hi : i ∈ s) : i < n :=
      Nat.lt_succ_of_le ((le_sup (f := id) hi).trans (le_sup (f := fun s : Finset ℕ => s.sup id) hs))
    have inj : Set.InjOn enc A := by
      intro s hs t ht heq
      ext i
      by_cases h : i < n
      · exact encode_agree s t n heq i h
      · exact ⟨fun hi => (h (inside _ hs _ hi)).elim, fun hi => (h (inside _ ht _ hi)).elim⟩
    have hcard : S.card = A.card := card_image_of_injOn inj
    have closed : ∀ x ∈ S, ∀ y ∈ S, join n x y ∈ S := by
      intro x hx y hy
      obtain ⟨s, hs, rfl⟩ := mem_image.mp hx
      obtain ⟨t, ht, rfl⟩ := mem_image.mp hy
      exact mem_image.mpr ⟨s ∪ t, hclosed _ hs _ ht, encode_union s t n⟩
    obtain ⟨i, hi⟩ := cubeBound n S (by omega) closed
    have hf : S.filter (fun x => read x i) = (A.filter fun s => index i ∈ s).image enc := by
      ext x
      constructor
      · intro hx
        obtain ⟨hs, hr⟩ := mem_filter.mp hx
        obtain ⟨s, ha, rfl⟩ := (mem_image.mp hs : ∃ s ∈ A, enc s = x)
        exact mem_image.mpr ⟨s, mem_filter.mpr ⟨ha, by simpa [enc, read_encode] using hr⟩, rfl⟩
      · intro hx
        obtain ⟨s, hs, rfl⟩ := mem_image.mp hx
        obtain ⟨hs, hi⟩ := mem_filter.mp hs
        exact mem_filter.mpr ⟨mem_image_of_mem _ hs, by simp [enc, read_encode, hi]⟩
    rw [hcard, hf, card_image_of_injOn (inj.mono (filter_subset _ _))] at hi
    exact ⟨index i, hi⟩

end C6Intermediate
end

/- Grow two set prefixes one bit at a time. The four entries of the Bernoulli coupling fix both marginals while prescribing the probability of their disjunction. -/
section
namespace C6Coupled
open Finset Real
noncomputable section

private lemma mixture {ι : Type*} (s : Finset ι) (w p : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hp : ∀ i ∈ s, p i ∈ Set.Icc 0 1) :
    ∑ i ∈ s, w i * binEntropy (p i) ≤
    (∑ i ∈ s, w i) * binEntropy ((∑ i ∈ s, w i * p i) / ∑ i ∈ s, w i) := by
  let W := ∑ i ∈ s, w i
  have hW : 0 ≤ W := sum_nonneg hw
  rcases hW.eq_or_lt with h|h
  · have hz := (sum_eq_zero_iff_of_nonneg hw).mp h.symm
    change 0 = ∑ i ∈ s, w i at h
    simp [sum_congr rfl (fun i hi => by rw [hz i hi, zero_mul] : ∀ i ∈ s, w i * binEntropy (p i) = 0), ← h]
  · have hh := strictConcave_binEntropy.concaveOn.le_map_sum
        (w := fun i => w i / W) (fun i hi => div_nonneg (hw i hi) h.le)
        (by rw [← sum_div]; exact div_self h.ne') hp
    simp only [smul_eq_mul] at hh
    simp_rw [div_mul_eq_mul_div, ← sum_div] at hh
    exact (div_le_iff₀ h).mp hh |>.trans_eq (mul_comm ..)

private lemma split_entropy {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    negMulLog x + negMulLog y =
      negMulLog (x+y) + (x+y)*binEntropy (x/(x+y)) := by
  by_cases h : x + y = 0
  · have : x = 0 := by linarith
    have : y = 0 := by linarith
    simp [*]
  have hx' : (x+y)*(x/(x+y)) = x := by field_simp
  have hy' : (x+y)*(1-x/(x+y)) = y := by field_simp; ring
  rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  have h1 := negMulLog_mul (x+y) (x/(x+y))
  have h2 := negMulLog_mul (x+y) (1-x/(x+y))
  rw [hx'] at h1
  rw [hy'] at h2
  linarith only [h1,h2]

variable {I : Type*} [Fintype I]

structure Coupling (w : I → ℝ) where
  mass : I × I → ℝ
  nonneg : ∀ a, 0 ≤ mass a
  row : ∀ x, ∑ y, mass (x,y) = w x
  symm : ∀ x y, mass (x,y) = mass (y,x)

def bern (p : ℝ) : Bool → ℝ
  | true => p
  | false => 1-p

def extendMass (w p : I → ℝ) (a : I × Bool) := w a.1 * bern (p a.1) a.2

def nextJoin (u : I × I → I) (a : (I × Bool) × (I × Bool)) : I × Bool :=
  (u (a.1.1,a.2.1), a.1.2 || a.2.2)

def unionMass (u : I × I → I) (c : I × I → ℝ) (z : I) : ℝ := by
  classical
  exact ∑ a ∈ univ.filter (fun a => u a = z), c a

def H (w : I → ℝ) : ℝ := ∑ a, negMulLog (w a)

def optimal (p q : ℝ) : ℝ := max (max p q) (min (1/2) (p+q))

def independent (p q : ℝ) : ℝ := p+q-p*q

/-- Feasible values of the union probability for two Bernoulli laws. -/
def Feasible (p q r : ℝ) : Prop := p ≤ r ∧ q ≤ r ∧ r ≤ 1 ∧ r ≤ p+q

theorem optimal_feasible {p q : ℝ} (hp : p ∈ Set.Icc 0 1) (hq : q ∈ Set.Icc 0 1) :
    Feasible p q (optimal p q) := by
  unfold optimal Feasible
  refine ⟨le_trans (le_max_left ..) (le_max_left ..), le_trans (le_max_right ..) (le_max_left ..), ?_, ?_⟩
  · exact max_le (max_le hp.2 hq.2) ((min_le_left ..).trans (by norm_num))
  · exact max_le (max_le (le_add_of_nonneg_right hq.1) (le_add_of_nonneg_left hp.1)) (min_le_right ..)

theorem independent_feasible {p q : ℝ} (hp : p ∈ Set.Icc 0 1) (hq : q ∈ Set.Icc 0 1) :
    Feasible p q (independent p q) := by
  unfold independent Feasible
  exact ⟨by nlinarith [mul_nonneg (sub_nonneg.mpr hp.2) hq.1],
    by nlinarith [mul_nonneg hp.1 (sub_nonneg.mpr hq.2)],
    by nlinarith [mul_nonneg (sub_nonneg.mpr hp.2) (sub_nonneg.mpr hq.2)],
    by nlinarith [mul_nonneg hp.1 hq.1]⟩

/-- Conditional two-bit law with marginals p,q and disjunction probability r. -/
def kernel (p q r : ℝ) : Bool → Bool → ℝ
  | false, false => 1-r
  | false, true => r-p
  | true, false => r-q
  | true, true => p+q-r

theorem kernel_nonneg {p q r : ℝ} (hr : Feasible p q r) (b d : Bool) :
    0 ≤ kernel p q r b d := by
  rcases hr with ⟨h₁,h₂,h₃,h₄⟩
  cases b <;> cases d <;> dsimp [kernel] <;> linarith

theorem kernel_row (p q r : ℝ) (b : Bool) : ∑ d, kernel p q r b d = bern p b := by
  cases b <;> simp [Fintype.sum_bool, kernel, bern]

theorem kernel_flip (p q r : ℝ) (b d : Bool) : kernel p q r b d = kernel q p r d b := by
  cases b <;> cases d <;> simp [kernel, add_comm]

def extend {w : I → ℝ} (c : Coupling w) (p : I → ℝ) (r : ℝ → ℝ → ℝ)
    (hf : ∀ x y, Feasible (p x) (p y) (r (p x) (p y)))
    (hs : ∀ x y, r x y = r y x) : Coupling (extendMass w p) where
  mass a := c.mass (a.1.1,a.2.1) *
    kernel (p a.1.1) (p a.2.1) (r (p a.1.1) (p a.2.1)) a.1.2 a.2.2
  nonneg a := mul_nonneg (c.nonneg _) (kernel_nonneg (hf ..) ..)
  symm := by
    rintro ⟨x,b⟩ ⟨y,d⟩
    dsimp only
    rw [c.symm x y, hs (p x) (p y), kernel_flip]
  row := by
    rintro ⟨x,b⟩
    simp only [Fintype.sum_prod_type, ← mul_sum, kernel_row, ← sum_mul, c.row, extendMass]

def product (w : I → ℝ) : I × I → ℝ := fun a => w a.1 * w a.2

def productCoupling (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) : Coupling w where
  mass := product w
  nonneg _ := mul_nonneg (hw _) (hw _)
  row _ := by simp [product, ← mul_sum, hs]
  symm _ _ := mul_comm ..

theorem kernel_independent (p q : ℝ) (b d : Bool) :
    kernel p q (independent p q) b d = bern p b * bern q d := by
  cases b <;> cases d <;> dsimp [kernel, bern, independent] <;> ring

theorem H_extendMass (w p : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hp : ∀ i, p i ∈ Set.Icc 0 1) :
    H (extendMass w p) = H w + ∑ i, w i * binEntropy (p i) := by
  simp only [H, extendMass, Fintype.sum_prod_type, Fintype.sum_bool, bern, ← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  have h := split_entropy (mul_nonneg (hw i) (hp i).1) (mul_nonneg (hw i) (sub_nonneg.mpr (hp i).2))
  rw [show w i * p i + w i * (1-p i) = w i by ring] at h
  by_cases h0 : w i = 0
  · simp [h0]
  · simpa [h0] using h

private theorem unionMass_extend {w : I → ℝ} (u : I × I → I) (c : Coupling w)
    (p : I → ℝ) (r : ℝ → ℝ → ℝ)
    (hf : ∀ x y, Feasible (p x) (p y) (r (p x) (p y))) (hs : ∀ x y, r x y = r y x)
    (z : I) (b : Bool) :
    unionMass (nextJoin u) (extend c p r hf hs).mass (z,b) =
      ∑ a ∈ (by classical exact univ.filter fun a => u a = z), c.mass a * bern (r (p a.1) (p a.2)) b := by
  classical
  rw [unionMass, Finset.sum_filter]
  simp only [Finset.sum_filter, Fintype.sum_prod_type, nextJoin, extend]
  apply sum_congr rfl
  intro x _
  rw [sum_comm]
  apply sum_congr rfl
  intro y _
  by_cases h : u (x,y) = z <;> cases b <;>
    simp [h, Prod.mk.injEq, Fintype.sum_bool, bern, kernel] <;> ring

private theorem growthStep {w : I → ℝ} (u : I × I → I) (c : Coupling w)
    (p : I → ℝ) (hp : ∀ x, p x ∈ Set.Icc 0 1) (r : ℝ → ℝ → ℝ)
    (hf : ∀ x y, Feasible (p x) (p y) (r (p x) (p y))) (hs : ∀ x y, r x y = r y x) :
    H (unionMass u c.mass) + ∑ a, c.mass a * binEntropy (r (p a.1) (p a.2)) ≤
      H (unionMass (nextJoin u) (extend c p r hf hs).mass) := by
  classical
  let W := c.mass
  let P (a : I × I) := r (p a.1) (p a.2)
  let t (z : I) := univ.filter (fun a => u a = z)
  have hp' (a) : P a ∈ Set.Icc 0 1 := ⟨(hp a.1).1.trans (hf a.1 a.2).1, (hf a.1 a.2).2.2.1⟩
  have hW (z) : unionMass u c.mass z = ∑ a ∈ t z, W a := rfl
  let v := unionMass (nextJoin u) (extend c p r hf hs).mass
  have hv (z b) : v (z,b) = ∑ a ∈ t z, W a * bern (P a) b := unionMass_extend u c p r hf hs z b
  have hv0 (z b) : 0 ≤ v (z,b) := by
    rw [hv]
    apply sum_nonneg
    intro a _
    exact mul_nonneg (c.nonneg a) (by cases b <;> dsimp [bern] <;> linarith [(hp' a).1, (hp' a).2])
  have hsum (z) : v (z,true) + v (z,false) = unionMass u c.mass z := by
    rw [hv, hv, hW, ← sum_add_distrib]
    apply sum_congr rfl
    intro a _
    dsimp [bern]; ring
  have he (z) := split_entropy (hv0 z true) (hv0 z false)
  have hj (z) := mixture (t z) W P (fun a _ => c.nonneg a) (fun a _ => hp' a)
  have hz (z) : negMulLog (unionMass u c.mass z) + ∑ a ∈ t z, W a * binEntropy (P a) ≤
      negMulLog (v (z,true)) + negMulLog (v (z,false)) := by
    rw [he, hsum]
    apply add_le_add_right
    simpa only [hv z true, bern, hW] using hj z
  have h := sum_le_sum (s := univ) (fun z _ => hz z)
  rw [sum_add_distrib, show (∑ z, ∑ a ∈ t z, W a * binEntropy (P a)) = ∑ a, W a * binEntropy (P a) from
    sum_fiberwise_of_maps_to (fun _ _ => mem_univ _) _] at h
  change _ ≤ H v
  simpa only [H, Fintype.sum_prod_type, Fintype.sum_bool] using h

theorem coupledStep {w : I → ℝ} (p : I → ℝ) (u : I × I → I) (c : Coupling w)
    (hp : ∀ i, p i ∈ Set.Icc 0 1) :
    ∃ c' : Coupling (extendMass w p), H (unionMass u c.mass) +
      ∑ a, c.mass a * binEntropy (optimal (p a.1) (p a.2)) ≤ H (unionMass (nextJoin u) c'.mass) := by
  have hf x y := optimal_feasible (hp x) (hp y)
  have hs (x y : ℝ) : optimal x y = optimal y x := by simp [optimal, max_comm x y, add_comm x y]
  exact ⟨extend c p optimal hf hs, growthStep u c p hp optimal hf hs⟩

theorem independentStep (w p : I → ℝ) (u : I × I → I)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (hp : ∀ i, p i ∈ Set.Icc 0 1) :
    H (unionMass u (product w)) +
      ∑ a, product w a * binEntropy (independent (p a.1) (p a.2)) ≤
      H (unionMass (nextJoin u) (product (extendMass w p))) := by
  let c := productCoupling w hw hsum
  have hf x y := independent_feasible (hp x) (hp y)
  have hs (x y : ℝ) : independent x y = independent y x := by dsimp [independent]; ring
  have he : (extend c p independent hf hs).mass = product (extendMass w p) := by
    funext a
    simp only [extend, c, productCoupling, product, extendMass, kernel_independent]
    ring
  have h := growthStep u c p hp independent hf hs
  rw [he] at h
  exact h

end
end C6Coupled
end

/- The entropy increments for the independent union and the coupled union can be combined with a fixed mixture weight at every coordinate. -/
section
namespace C6Intermediate
open C6Coupled Finset Real
noncomputable section

instance cubeFintype : (n : ℕ) → Fintype (Cube n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n+1 => by
    letI : Fintype (Cube n) := cubeFintype n
    exact inferInstanceAs (Fintype (Cube n × Bool))

def coordinateMean {n : ℕ} (w : Cube n → ℝ) (i : Coord n) : ℝ :=
  ∑ a, if read a i then w a else 0

def ScalarBound (t α k : ℝ) : Prop :=
  ∀ {I : Type} [Fintype I] (w p : I → ℝ) (c : Coupling w),
  (∀ a, 0 ≤ w a) → (∑ a, w a) = 1 → (∀ a, p a ∈ Set.Icc 0 1) →
  (∑ a, w a * p a) ≤ t →
  k * (∑ a, w a * binEntropy (p a)) ≤
    (1-α) * (∑ a, product w a * binEntropy (independent (p a.1) (p a.2))) +
    α * (∑ a, c.mass a * binEntropy (optimal (p a.1) (p a.2)))

private lemma sum_unit (v : Unit → ℝ) : ∑ a, v a = v () := by simp

private lemma sum_last {I : Type} [Fintype I] (v : I × Bool → ℝ) :
    ∑ a, v a = ∑ x, (v (x,true) + v (x,false)) := by simp only [Fintype.sum_prod_type, Fintype.sum_bool]

theorem cubeGrowth {t α k : ℝ} (scalar : ScalarBound t α k) (hα : α ∈ Set.Icc 0 1)
    (n : ℕ) (w : Cube n → ℝ) (hw : ∀ a, 0 ≤ w a) (hs : ∑ a, w a = 1)
    (hm : ∀ i, coordinateMean w i ≤ t) :
    ∃ c : Coupling w, k * H w ≤
      (1-α) * H (unionMass (fun a => join n a.1 a.2) (product w)) +
      α * H (unionMass (fun a => join n a.1 a.2) c.mass) := by
  classical
  induction n with
  | zero =>
    refine ⟨productCoupling w hw hs, ?_⟩
    change (∑ a : Unit, w a) = 1 at hs
    have h : w () = 1 := (sum_unit w).symm.trans hs
    have hw1 : w = fun _ => 1 := by funext x; cases x; exact h
    subst w
    change k * (∑ _ : Unit, negMulLog 1) ≤
      (1-α) * (∑ z : Unit, negMulLog (unionMass (fun _ : Unit × Unit => ()) (product (fun _ => 1)) z)) +
      α * (∑ z : Unit, negMulLog (unionMass (fun _ : Unit × Unit => ()) (product (fun _ => 1)) z))
    simp [unionMass, product]
  | succ n ih =>
    let w₀ := fun a : Cube n => w (a,true) + w (a,false)
    let p := fun a : Cube n => w (a,true) / w₀ a
    have hw₀ a : 0 ≤ w₀ a := add_nonneg (hw _) (hw _)
    have hp a : p a ∈ Set.Icc 0 1 :=
      ⟨div_nonneg (hw _) (hw₀ _), div_le_one_of_le₀ (le_add_of_nonneg_right (hw _)) (hw₀ _)⟩
    have hwp a : w₀ a * p a = w (a,true) := by
      by_cases hz : w₀ a = 0
      · have ha : w (a,true) = 0 := by have := hw (a,false); have := hw (a,true); dsimp [w₀] at hz; linarith
        simp [hz, ha]
      · exact mul_div_cancel₀ _ hz
    have split : w = extendMass w₀ p := by
      funext x
      rcases x with ⟨a,b⟩
      cases b
      · change _ = w₀ a * (1 - p a)
        rw [mul_sub, mul_one, hwp]
        dsimp [w₀]; ring
      · exact (hwp a).symm
    have hs₀ : ∑ a, w₀ a = 1 := by
      change (∑ a : Cube n × Bool, w a) = 1 at hs
      exact (sum_last w).symm.trans hs
    have hm₀ (i : Coord n) : coordinateMean w₀ i ≤ t := by
      have hh := hm (.prev i)
      change (∑ a : Cube n × Bool, if read a.1 i then w a else 0) ≤ t at hh
      simpa only [coordinateMean, w₀, Fintype.sum_prod_type, Fintype.sum_bool, ite_add_zero] using hh
    have hmean : (∑ a, w₀ a * p a) ≤ t := by
      have hh := hm .last
      change (∑ a : Cube n × Bool, if a.2 then w a else 0) ≤ t at hh
      simpa [Fintype.sum_prod_type, Fintype.sum_bool, hwp] using hh
    obtain ⟨c, hprev⟩ := ih w₀ hw₀ hs₀ hm₀
    let u := fun a : Cube n × Cube n => join n a.1 a.2
    obtain ⟨c', hdep⟩ := coupledStep p u c hp
    have hind := independentStep w₀ p u hw₀ hs₀ hp
    have hl := scalar w₀ p c hw₀ hs₀ hp hmean
    rw [split]
    refine ⟨c', ?_⟩
    change k * H (extendMass w₀ p) ≤
      (1-α) * H (unionMass (nextJoin u) (product (extendMass w₀ p))) +
      α * H (unionMass (nextJoin u) c'.mass)
    rw [H_extendMass w₀ p hw₀ hp, mul_add]
    change k * H w₀ ≤ (1-α) * H (unionMass u (product w₀)) + α * H (unionMass u c.mass) at hprev
    linarith only [hprev, hl, mul_le_mul_of_nonneg_left hind (sub_nonneg.mpr hα.2),
      mul_le_mul_of_nonneg_left hdep hα.1]

end
end C6Intermediate
end

section
namespace C6Coupled
open Finset Real
noncomputable section
variable {I : Type*} [Fintype I]

private lemma sum_negMulLog_le_log_card {β : Type*} [Fintype β] [Nonempty β] (p : β → ℝ) (h0 : ∀ b, 0 ≤ p b)
    (h1 : ∑ b, p b = 1) : ∑ b, negMulLog (p b) ≤ log (Fintype.card β) := by
  let m : ℝ := Fintype.card β
  have hm : m ≠ 0 := by dsimp [m]; exact_mod_cast Fintype.card_ne_zero
  have hJ := Real.concaveOn_negMulLog.le_map_sum (t := (univ : Finset β))
    (w := fun _ => m⁻¹) (p := p) (by intro; intros; positivity)
    (by simp [nsmul_eq_mul, ← show (Fintype.card β : ℝ) = m from rfl, m, Fintype.card_ne_zero])
    (fun b _ => h0 b)
  simp only [smul_eq_mul, ← mul_sum, h1, mul_one, Real.negMulLog, Real.log_inv] at hJ
  have hpos : 0 < m := by dsimp [m]; exact_mod_cast Fintype.card_pos
  change ∑ b, -(p b) * log (p b) ≤ log m
  apply (mul_le_mul_iff_right₀ (inv_pos.mpr hpos)).mp
  simpa using hJ

/-- The law of a uniformly sampled member of the finite set S. -/
def uniform (S : Finset I) (a : I) : ℝ := by
  classical
  exact if a ∈ S then (S.card : ℝ)⁻¹ else 0

theorem uniform_nonneg (S : Finset I) (a : I) : 0 ≤ uniform S a := by
  classical
  unfold uniform
  split <;> positivity

theorem uniform_sum (S : Finset I) (hS : S.Nonempty) : ∑ a, uniform S a = 1 := by
  classical
  have hs : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
  simp [uniform, sum_ite_mem, nsmul_eq_mul, hs]

theorem H_uniform (S : Finset I) (hS : S.Nonempty) :
    H (uniform S) = log S.card := by
  classical
  have hs : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
  have he (i : I) : negMulLog (uniform S i) =
      if i ∈ S then negMulLog (S.card : ℝ)⁻¹ else 0 := by by_cases hi : i ∈ S <;> simp [uniform, hi]
  unfold H
  simp_rw [he]
  simp [sum_ite_mem, nsmul_eq_mul, negMulLog, ← mul_assoc, hs]

theorem mass_total {w : I → ℝ} (c : Coupling w) (hs : ∑ a, w a = 1) :
    ∑ a, c.mass a = 1 := by
  rw [Fintype.sum_prod_type]
  simpa only [c.row] using hs

theorem unionMass_sum {w : I → ℝ} (u : I × I → I) (c : Coupling w) (hs : ∑ a, w a = 1) :
    ∑ z, unionMass u c.mass z = 1 := by
  classical
  exact (sum_fiberwise_of_maps_to (s := (univ : Finset (I × I))) (t := (univ : Finset I)) (g := u) (fun _ _ => mem_univ _) c.mass).trans (mass_total c hs)

theorem unionMass_nonneg {w : I → ℝ} (u : I × I → I) (c : Coupling w) (z : I) :
    0 ≤ unionMass u c.mass z :=
  sum_nonneg (fun a _ => c.nonneg a)

theorem unionMass_support (S : Finset I) (u : I × I → I)
    (hu : ∀ x ∈ S, ∀ y ∈ S, u (x,y) ∈ S) (c : Coupling (uniform S)) (z : I) (hz : z ∉ S) :
    unionMass u c.mass z = 0 := by
  classical
  have hzero (x : I) (hx : x ∉ S) (y : I) : c.mass (x,y) = 0 := by
    have hsum := c.row x
    simp [uniform, hx] at hsum
    exact (sum_eq_zero_iff_of_nonneg (fun a _ => c.nonneg (x,a))).mp hsum y (mem_univ _)
  apply sum_eq_zero
  rintro ⟨x,y⟩ ha
  have he : u (x,y) = z := (mem_filter.mp ha).2
  by_cases hx : x ∈ S
  · by_cases hy : y ∈ S
    · exact (hz (he ▸ hu _ hx _ hy)).elim
    · exact (c.symm x y).trans (hzero y hy x)
  · exact hzero x hx y

theorem entropy_cap (S : Finset I) (hS : S.Nonempty) (u : I × I → I)
    (hu : ∀ x ∈ S, ∀ y ∈ S, u (x,y) ∈ S) (c : Coupling (uniform S)) :
    H (unionMass u c.mass) ≤ log S.card := by
  classical
  let v := unionMass u c.mass
  have hv (i : I) (hi : i ∉ S) : v i = 0 := unionMass_support S u hu c i hi
  have hsum (f : ℝ → ℝ) (hf : f 0 = 0) : (∑ i, f (v i)) = ∑ i : S, f (v i) := by
    rw [sum_coe_sort S (fun i => f (v i))]
    exact (sum_subset (subset_univ _) (fun i _ hi => by rw [hv i hi,hf])).symm
  let : Nonempty S := hS.to_subtype
  have h1 := unionMass_sum u c (uniform_sum S hS)
  change ∑ i, v i = 1 at h1
  have h1' : ∑ i : S, v i = 1 := (hsum id rfl).symm.trans h1
  have h := sum_negMulLog_le_log_card (fun i : S => v i) (fun i => unionMass_nonneg u c i) h1'
  change ∑ i, negMulLog (v i) ≤ log _
  rw [hsum negMulLog (by simp)]
  simpa only [Fintype.card_coe] using h

end
end C6Coupled
end

section
namespace C6Intermediate
open C6Coupled Finset Real

theorem uniform_mean {n : ℕ} (S : Finset (Cube n)) (i : Coord n) :
    coordinateMean (uniform S) i = ((S.filter fun x => read x i).card : ℝ) / S.card := by
  classical
  unfold coordinateMean
  have e (a : Cube n) : (if read a i then uniform S a else 0) =
      if a ∈ S.filter (fun x => read x i) then (S.card : ℝ)⁻¹ else 0 := by
    by_cases h : read a i <;> by_cases h' : a ∈ S <;> simp [uniform, h, h']
  simp only [e, sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul, div_eq_mul_inv]

theorem lowerBound_of_scalar {t α k : ℝ} (ht : t ≤ 1) (hα : α ∈ Set.Icc 0 1)
    (hk : 1 < k) (scalar : ScalarBound t α k) : t ≤ Constant6a.C6a := by
  apply of_cube t ht
  intro n S hsize closed
  classical
  have hS : S.Nonempty := card_pos.mp (by omega)
  have hcard : 0 < (S.card : ℝ) := by exact_mod_cast hS.card_pos
  by_contra! h
  have hm (i : Coord n) : coordinateMean (uniform S) i ≤ t := by
    rw [uniform_mean]
    exact (div_le_iff₀ hcard).mpr (h i).le
  obtain ⟨c, hbound⟩ := cubeGrowth scalar hα n _ (uniform_nonneg S) (uniform_sum S hS) hm
  let u := fun a : Cube n × Cube n => join n a.1 a.2
  have hdep := entropy_cap S hS u closed c
  have hind := entropy_cap S hS u closed (productCoupling _ (uniform_nonneg S) (uniform_sum S hS))
  change H (unionMass u (product (uniform S))) ≤ log S.card at hind
  rw [H_uniform S hS] at hbound
  change k * log S.card ≤ (1-α) * H (unionMass u (product (uniform S))) +
    α * H (unionMass u c.mass) at hbound
  have hlog := log_pos (show 1 < (S.card : ℝ) by exact_mod_cast hsize)
  linarith only [hbound, mul_le_mul_of_nonneg_left hind (sub_nonneg.mpr hα.2),
    mul_le_mul_of_nonneg_left hdep hα.1, mul_pos (sub_pos.mpr hk) hlog]
end C6Intermediate
end

/- Padding with an all-present atom raises the mean to the target. Independent union entropy scales quadratically in the retained mass, while both the coupled term and the original entropy scale linearly. -/
section
namespace C6Intermediate
open C6Coupled Finset Real

/-- The entropy inequality restricted to laws having exactly mean t. -/
def ExactScalarBound (t α k : ℝ) : Prop :=
  ∀ {I : Type} [Fintype I] (w p : I → ℝ) (c : Coupling w),
  (∀ a, 0 ≤ w a) → (∑ a, w a) = 1 → (∀ a, p a ∈ Set.Icc 0 1) →
  (∑ a, w a * p a) = t →
  k * (∑ a, w a * binEntropy (p a)) ≤
    (1-α) * (∑ a, product w a * binEntropy (independent (p a.1) (p a.2))) +
    α * (∑ a, c.mass a * binEntropy (optimal (p a.1) (p a.2)))

private def addAtom {I : Type*} (r : ℝ) (w : I → ℝ) : Option I → ℝ
  | none => 1-r
  | some i => r*w i

private def atomProbability {I : Type*} (p : I → ℝ) : Option I → ℝ
  | none => 1
  | some i => p i

private def atomCoupling {I : Type*} [Fintype I] {w : I → ℝ} (c : Coupling w)
    (r : ℝ) (hr : r ∈ Set.Icc 0 1) : Coupling (addAtom r w) where
  mass := fun (i,j) => match i,j with
    | none, none => 1-r
    | some x, some y => r * c.mass (x,y)
    | _, _ => 0
  nonneg := by
    rintro ⟨i,j⟩
    cases i <;> cases j <;> dsimp <;>
      first | exact sub_nonneg.mpr hr.2 | exact le_rfl | exact mul_nonneg hr.1 (c.nonneg _)
  row := by
    intro i
    cases i <;> simp [Fintype.sum_option, addAtom, ← mul_sum, c.row]
  symm := by
    intro i j
    cases i <;> cases j <;> dsimp <;> first | rfl | rw [c.symm]

/-- Raise the mean by adjoining a deterministic coordinate value 1.
All entropy terms vanish on the added atom. -/
theorem scalarBound_of_exact {t α k : ℝ} (ht : t < 1) (hα : α ≤ 1)
    (h : ExactScalarBound t α k) : ScalarBound t α k := by
  intro I _ w p c hw hsum hp hmean
  classical
  let s := ∑ i, w i * p i
  let r := (1 - t) / (1 - s)
  have hs : s < 1 := hmean.trans_lt ht
  have hr : 0 < r := div_pos (sub_pos.mpr ht) (sub_pos.mpr hs)
  have hr1 : r ≤ 1 := (div_le_one (sub_pos.mpr hs)).mpr (sub_le_sub_left hmean _)
  have he : 1 - r + r*s = t := by
    have hv : r*(1-s) = 1-t := div_mul_cancel₀ _ (sub_pos.mpr hs).ne'
    linarith
  have hpad := h (addAtom r w) (atomProbability p) (atomCoupling c r ⟨hr.le,hr1⟩)
    (by rintro (_|i); exact sub_nonneg.mpr hr1; exact mul_nonneg hr.le (hw i))
    (by simp [Fintype.sum_option, addAtom, ← mul_sum, hsum])
    (by rintro (_|i); exact ⟨zero_le_one, le_rfl⟩; exact hp i)
    (by simpa [Fintype.sum_option, addAtom, atomProbability, mul_assoc, ← mul_sum, s] using he)
  let X := ∑ i, w i * binEntropy (p i)
  let Y := ∑ a, product w a * binEntropy (independent (p a.1) (p a.2))
  let Z := ∑ a, c.mass a * binEntropy (optimal (p a.1) (p a.2))
  have hX : (∑ i, addAtom r w i * binEntropy (atomProbability p i)) = r * X := by
    simp [X, Fintype.sum_option, addAtom, atomProbability, mul_assoc, mul_sum]
  have e₁ (z : ℝ) : independent 1 z = 1 := by unfold independent; ring
  have e₂ (z : ℝ) : independent z 1 = 1 := by unfold independent; ring
  have e₃ : optimal 1 1 = 1 := by norm_num [optimal]
  have hY : (∑ a, product (addAtom r w) a *
      binEntropy (independent (atomProbability p a.1) (atomProbability p a.2))) =
      r^2 * Y := by
    simp only [Y, product, Fintype.sum_prod_type, Fintype.sum_option, addAtom, atomProbability,
      e₁, e₂, binEntropy_one, mul_zero, sum_const_zero, add_zero, zero_add, mul_sum]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    ring
  have hZ : (∑ a, (atomCoupling c r ⟨hr.le,hr1⟩).mass a *
      binEntropy (optimal (atomProbability p a.1) (atomProbability p a.2))) = r * Z := by
    simp [Z, Fintype.sum_prod_type, Fintype.sum_option, atomProbability, atomCoupling,
      e₃, mul_assoc, mul_sum]
  rw [hX,hY,hZ] at hpad
  change k*X ≤ (1-α)*Y + α*Z
  have hy : 0 ≤ Y := by
    apply sum_nonneg
    intro a _
    have hf := independent_feasible (hp a.1) (hp a.2)
    exact mul_nonneg (mul_nonneg (hw _) (hw _)) (binEntropy_nonneg ((hp _).1.trans hf.1) hf.2.2.1)
  have hle : r^2 * Y ≤ r * Y :=
    mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg hr.le (sub_nonneg.mpr hr1)] : r^2 ≤ r) hy
  apply (mul_le_mul_iff_right₀ hr).mp
  linarith only [hpad, mul_le_mul_of_nonneg_left hle (sub_nonneg.mpr hα)]
end C6Intermediate
end

/- For two absence probabilities above one half, concavity bounds the coupled entropy by the average of two clamped diagonal entropies. Below one half the smaller absence probability gives the coupled entropy directly. -/
section
namespace C6Intermediate
open C6Coupled Finset Real Set
noncomputable section

def capUpper (x : ℝ) := max (1/2) (2*x-1)

private theorem transfer_cost {F : ℝ → ℝ} {α L : ℝ} (ha : 0 ≤ α)
    (hbase : ∀ x ∈ Set.Icc (0:ℝ) 1, L ≤ F x)
    (hlow : ∀ x ∈ Set.Icc (0:ℝ) (1/2), -L ≤ F x + 2*α*binEntropy x)
    (hhigh : ∀ x ∈ Set.Icc (1/2:ℝ) 1, 0 ≤ F x + α*binEntropy (capUpper x))
    {x y : ℝ} (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1) :
    0 ≤ F x + F y + 2*α*binEntropy (optimal (1-x) (1-y)) := by
  wlog hxy : x ≤ y generalizing x y
  · have h := this hy hx (le_of_not_ge hxy)
    have he : optimal (1-x) (1-y) = optimal (1-y) (1-x) := by
      simp only [optimal, max_comm (1-x) (1-y), add_comm (1-x) (1-y)]
    rw [he]
    linarith only [h]
  by_cases h : x ≤ 1/2
  · have he : optimal (1-x) (1-y) = 1-x := by
      unfold optimal
      rw [max_eq_left (show 1-y ≤ 1-x by linarith), max_eq_left ((min_le_left ..).trans (by linarith))]
    rw [he, binEntropy_one_sub]
    linarith only [hlow x ⟨hx.1,h⟩, hbase y hy]
  have hx' : 1/2 ≤ x := le_of_not_ge h
  have hy' := hx'.trans hxy
  let u := capUpper x
  let v := capUpper y
  have hu : u ∈ Set.Icc (1/2:ℝ) 1 := ⟨le_max_left .., max_le (by norm_num) (by linarith [hx.2])⟩
  have hv : v ∈ Set.Icc (1/2:ℝ) 1 := ⟨le_max_left .., max_le (by norm_num) (by linarith [hy.2])⟩
  let z := max (1/2:ℝ) (x+y-1)
  have hsmall : z ≤ (u+v)/2 := by
    have e₁ : 2*x-1 ≤ u := le_max_right .. 
    have e₂ : 2*y-1 ≤ v := le_max_right ..
    exact max_le (by linarith [hu.1,hv.1]) (by linarith)
  have hz : z ∈ Set.Icc (2:ℝ)⁻¹ 1 := ⟨by simpa only [z,one_div] using (le_max_left (1/2:ℝ) (x+y-1)),
    hsmall.trans (by linarith [hu.2,hv.2])⟩
  have hmid : (u+v)/2 ∈ Set.Icc (2:ℝ)⁻¹ 1 := ⟨hz.1.trans hsmall,by linarith [hu.2,hv.2]⟩
  have hanti := binEntropy_strictAntiOn.antitoneOn hz hmid hsmall
  have hc := strictConcave_binEntropy.concaveOn.2 (show u ∈ Set.Icc (0:ℝ) 1 from ⟨by linarith [hu.1],hu.2⟩)
    (show v ∈ Set.Icc (0:ℝ) 1 from ⟨by linarith [hv.1],hv.2⟩)
    (show (0:ℝ) ≤ 1/2 by norm_num) (show (0:ℝ) ≤ 1/2 by norm_num) (by norm_num)
  simp only [smul_eq_mul] at hc
  rw [show (1/2:ℝ)*u+1/2*v = (u+v)/2 by ring] at hc
  have he : optimal (1-x) (1-y) = 1-z := by
    unfold optimal z
    rcases le_total (1/2:ℝ) (x+y-1) with h | h
    · rw [max_eq_right h, min_eq_right (by linarith), max_eq_right] <;> try linarith
      exact max_le (by linarith [hy.2]) (by linarith [hx.2])
    · rw [max_eq_left h, min_eq_left (by linarith), max_eq_right (max_le (by linarith) (by linarith))]
      ring
  rw [he, binEntropy_one_sub]
  have hcomb : (binEntropy u + binEntropy v) / 2 ≤ binEntropy z := by linarith only [hc,hanti]
  linarith only [mul_le_mul_of_nonneg_left hcomb ha, hhigh x ⟨hx',hx.2⟩, hhigh y ⟨hy',hy.2⟩]

private theorem expect_left {I : Type} [Fintype I] {w : I → ℝ}
    (c : Coupling w) (g : I → ℝ) : (∑ a, c.mass a * g a.1) = ∑ i, w i * g i := by
  simp only [Fintype.sum_prod_type, ← sum_mul, c.row]

private theorem expect_right {I : Type} [Fintype I] {w : I → ℝ}
    (c : Coupling w) (g : I → ℝ) : (∑ a, c.mass a * g a.2) = ∑ i, w i * g i := by
  rw [Fintype.sum_prod_type, sum_comm]
  apply sum_congr rfl
  intro y _
  simp only [← sum_mul, c.symm _ y, c.row]

def residual (f : ℝ → ℝ) (m α k C l u A B D x : ℝ) :=
  (1-α)*m*(binEntropy (x^2)/x + C*x*(f x-l)*(f x-u)) - k*binEntropy x -
    A*(x-m) - B*x*(f x-l) - D*x*(u-f x)

def DualCells (f : ℝ → ℝ) (m α k C : ℝ) : Prop :=
  ∀ t ∈ Set.Icc (0:ℝ) 1, ∃ l u A B D L : ℝ, l ≤ t ∧ t ≤ u ∧ 0 ≤ B ∧ 0 ≤ D ∧
    (∀ x ∈ Set.Icc (0:ℝ) 1, L ≤ residual f m α k C l u A B D x) ∧
    (∀ x ∈ Set.Icc (0:ℝ) (1/2), -L ≤ residual f m α k C l u A B D x + 2*α*binEntropy x) ∧
    (∀ x ∈ Set.Icc (1/2:ℝ) 1, 0 ≤ residual f m α k C l u A B D x + α*binEntropy (capUpper x))

end
end C6Intermediate
end

/- For an absence probability x with mean m, set t = E[x f(x)] / m. On a slice l ≤ t ≤ u, the inequality (t-l)(u-t) ≥ 0 gives the chord bound on the variance of f. The terms with coefficients A, B and D account for the mean and the two slice endpoints. -/
section
namespace C6Intermediate
open C6Coupled Finset Real
noncomputable section
variable {I : Type} [Fintype I]

private def E (w g : I → ℝ) := ∑ i, w i * g i

private theorem E_add (w g h : I → ℝ) : E w (fun i => g i + h i) = E w g + E w h := by
  simp [E,mul_add,sum_add_distrib]
private theorem E_sub (w g h : I → ℝ) : E w (fun i => g i - h i) = E w g - E w h := by
  simp [E,mul_sub,sum_sub_distrib]
private theorem E_scale (w g : I → ℝ) (k : ℝ) : E w (fun i => k*g i) = k * E w g := by
  simp [E, mul_left_comm _ k _, mul_sum]
private theorem E_const {w : I → ℝ} (hw : ∑ i, w i = 1) (k : ℝ) : E w (fun _ => k) = k := by
  simp [E, ← sum_mul, hw]
private theorem E_prod (w g h : I → ℝ) :
    E (product w) (fun a => g a.1 * h a.2) = E w g * E w h := by
  simp only [E, product, Fintype.sum_prod_type, mul_mul_mul_comm (w _) (w _), ← mul_sum, ← sum_mul]

theorem exact_of_dual {f : ℝ → ℝ} {m α k C : ℝ}
    (hm : 0 < m) (ha : α ∈ Set.Icc 0 1) (hC : 0 ≤ C)
    (hf : ∀ z ∈ Set.Icc (0:ℝ) 1, f z ∈ Set.Icc (0:ℝ) 1)
    (cells : DualCells f m α k C)
    (kernel : ∀ x y : ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 →
      y*(binEntropy (x^2)/x)+x*(binEntropy (y^2)/y)+
        x*y*C*(f x-f y)^2 ≤ 2*binEntropy (x*y)) :
    ExactScalarBound (1-m) α k := by
  intro I inst w p c hw hs hp hmean
  let x := fun i => 1-p i
  let q := fun i => f (x i)
  let b := fun i => binEntropy ((x i)^2) / x i
  let h := fun i => binEntropy (x i)
  let T := fun i => x i * q i
  let V := fun i => x i * (q i)^2
  have hx i : x i ∈ Set.Icc 0 1 := ⟨sub_nonneg.mpr (hp i).2, sub_le_self _ (hp i).1⟩
  have hq i := hf (x i) (hx i)
  have hxm : E w x = m := by
    change E w (fun i => 1-p i) = _
    rw [E_sub, E_const hs]
    change _ - (∑ i, w i * p i) = _
    rw [hmean]; ring
  let t := E w T / m
  have ht : m*t = E w T := mul_div_cancel₀ _ hm.ne'
  have ht0 : 0 ≤ E w T := sum_nonneg (fun i _ => mul_nonneg (hw i) (mul_nonneg (hx i).1 (hq i).1))
  have ht1 : E w T ≤ E w x := sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (hx i).1 (hq i).2) (hw i)
  obtain ⟨l,u,A,B,D,L,hlt,htu,hB,hD,hbase,hlow,hhigh⟩ := cells t
    ⟨div_nonneg ht0 hm.le, (div_le_one hm).mpr (ht1.trans_eq hxm)⟩
  let F := residual f m α k C l u A B D
  have pair (a : I × I) := transfer_cost ha.1 hbase hlow hhigh (hx a.1) (hx a.2)
  let opt := fun a : I × I => binEntropy (optimal (p a.1) (p a.2))
  let ind := fun a : I × I => binEntropy (independent (p a.1) (p a.2))
  have hopt (a : I × I) : binEntropy (optimal (1-x a.1) (1-x a.2)) = opt a := by simp [x,opt]
  have hind (a : I × I) : binEntropy (x a.1*x a.2) = ind a := by
    rw [← binEntropy_one_sub (x a.1*x a.2)]; congr 1; dsimp [x,ind,independent]; ring
  have hpair : 0 ≤ E c.mass (fun a : I × I => F (x a.1) + F (x a.2) + (2*α)*opt a) := by
    apply sum_nonneg
    intro a _
    exact mul_nonneg (c.nonneg a) (by simpa only [hopt] using pair a)
  simp only [E_add, E_scale] at hpair
  rw [show E c.mass (fun a => F (x a.1)) = E w (fun i => F (x i)) from expect_left c (fun i => F (x i)),
      show E c.mass (fun a => F (x a.2)) = E w (fun i => F (x i)) from expect_right c (fun i => F (x i))] at hpair
  have ker (a : I × I) := kernel _ _ (hx a.1).1 (hx a.1).2 (hx a.2).1 (hx a.2).2
  have ik : E (product w) (fun a : I × I => b a.1*x a.2 + x a.1*b a.2 +
      C*(V a.1*x a.2 + x a.1*V a.2 - 2*(T a.1*T a.2))) ≤
        E (product w) (fun a => 2*ind a) := by
    apply sum_le_sum
    intro a _
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hw a.1) (hw a.2))
    simp only []; rw [← hind a]; convert! ker a using 1 <;> dsimp [V,T,q,b] <;> ring
  simp only [E_scale, E_add, E_sub, E_prod, hxm] at ik
  have heq : (fun i => F (x i)) = (fun i =>
      ((1-α)*m)*(b i + C*(V i - (l+u)*T i + (l*u)*x i)) - k*h i -
        A*(x i-m) - B*(T i-l*x i) - D*(u*x i-T i)) := by
    funext i; dsimp [F,residual,b,q,V,T,h]; ring
  rw [heq] at hpair
  simp only [E_sub, E_add, E_scale, E_const hs, hxm, sub_self, mul_zero, sub_zero] at hpair
  have hl : 0 ≤ B * (E w T - l*m) := mul_nonneg hB (by linarith only [ht,mul_le_mul_of_nonneg_left hlt hm.le])
  have hu : 0 ≤ D * (u*m - E w T) := mul_nonneg hD (by linarith only [ht,mul_le_mul_of_nonneg_left htu hm.le])
  have hd : 0 ≤ (1-α)*C*((E w T - l*m)*(u*m-E w T)) :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr ha.2) hC)
      (mul_nonneg (by linarith only [ht,mul_le_mul_of_nonneg_left hlt hm.le])
        (by linarith only [ht,mul_le_mul_of_nonneg_left htu hm.le]))
  have hstrict : k * E w h ≤ (1-α)*E (product w) ind + α*E c.mass opt := by
    nlinarith only [hpair,hl,hu, mul_le_mul_of_nonneg_left ik (sub_nonneg.mpr ha.2),hd]
  simpa only [E,h,x,binEntropy_one_sub] using hstrict

end
end C6Intermediate
end

/- A cubic correction to the concavity inequality for scaled binary entropy yields a positive multiple of the squared difference of the two cubic moments. -/
section
open Real Set
namespace C6Projected
noncomputable section
def moment (x : ℝ) := (6*x + 3*x^2 + 2*x^3)/11
def corr (x : ℝ) := x/2+x^2/6+x^3/12

private lemma tail (u : ℝ) (hu : 0 ≤ u) (hu1 : u < 1) :
    0 ≤ u/(1-u)+log (1-u)-u^2/2-2*u^3/3-3*u^4/4 := by
  let g (v : ℝ) := v/(1-v)+log (1-v)-v^2/2-2*v^3/3-3*v^4/4
  have hd (v : ℝ) (hv : v < 1) : HasDerivAt g
      (v^4*(4-3*v)/(1-v)^2) v := by
    dsimp [g]
    have hn : 1-v ≠ 0 := by linarith
    have h := (hasDerivAt_const v (1:ℝ)).sub (hasDerivAt_id v)
    convert! (((((hasDerivAt_id v).div h hn).add (h.log hn)).sub
      (((hasDerivAt_id v).pow 2).div_const 2)).sub
      ((((hasDerivAt_id v).pow 3).const_mul 2).div_const 3)).sub
      ((((hasDerivAt_id v).pow 4).const_mul 3).div_const 4) using 1 <;>
      simp only [Pi.sub_apply, id_eq, Pi.div_apply, Pi.add_apply, Function.comp_apply, Pi.pow_apply] <;>
      first | rfl | (field_simp [hn]; ring)
  have mono : MonotoneOn g (Icc 0 u) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 u)
    · exact fun v hv => (hd v (lt_of_le_of_lt hv.2 hu1)).continuousAt.continuousWithinAt
    · intro v hv
      rw [interior_Icc] at hv
      exact (hd v (hv.2.trans hu1)).differentiableAt.differentiableWithinAt
    · intro v hv
      rw [interior_Icc] at hv
      rw [(hd v (hv.2.trans hu1)).deriv]
      exact div_nonneg (mul_nonneg (by positivity) (by linarith [hv.2.trans hu1])) (sq_nonneg _)
  have h := mono (show 0 ∈ Icc (0:ℝ) u from ⟨le_rfl,hu⟩) (show u ∈ Icc (0:ℝ) u from ⟨hu,le_rfl⟩) hu
  simpa [g] using h

private lemma concave_aux :
    ConcaveOn ℝ (Iic 0) (fun t : ℝ => binEntropy (exp t) / exp t + corr (exp t)) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Iic 0)
    (f' := fun t => log (1 - exp t) / exp t + (exp t/2 + (exp t)^2/3 + (exp t)^3/4))
    (f'' := fun t => -1 / (1 - exp t) - log (1 - exp t) / exp t +
      (exp t/2 + 2*(exp t)^2/3 + 3*(exp t)^3/4))
  · apply Continuous.continuousOn
    apply Continuous.add
    · exact (binEntropy_continuous.comp continuous_exp).div continuous_exp (fun t => (exp_pos t).ne')
    · unfold corr
      fun_prop
  · intro t ht
    rw [interior_Iic] at ht
    have hp : exp t < 1 := Real.exp_lt_one_iff.mpr ht
    have e := hasDerivAt_exp t
    have h := ((hasDerivAt_binEntropy (exp_pos t).ne' hp.ne).comp t e).div e (exp_pos t).ne'
    have q := ((e.div_const 2).add ((e.pow 2).div_const 6)).add ((e.pow 3).div_const 12)
    apply ((h.add q).congr_deriv ?_).hasDerivWithinAt
    simp only [binEntropy, log_inv, Function.comp_apply]
    field_simp [ne_of_gt (exp_pos t)]
    ring
  · intro t ht
    rw [interior_Iic] at ht
    have hp : 0 < 1 - exp t := sub_pos.mpr (Real.exp_lt_one_iff.mpr ht)
    have e := hasDerivAt_exp t
    have h := ((((hasDerivAt_const t (1 : ℝ)).sub e).log hp.ne').div e (exp_pos t).ne')
    have q := ((e.div_const 2).add ((e.pow 2).div_const 3)).add ((e.pow 3).div_const 4)
    apply ((h.add q).congr_deriv ?_).hasDerivWithinAt
    simp only [Pi.sub_apply, zero_sub]
    field_simp [hp.ne', (exp_pos t).ne']
    <;> ring
  · intro t ht
    rw [interior_Iic] at ht
    have e := exp_pos t
    have h1 : exp t < 1 := Real.exp_lt_one_iff.mpr ht
    have hp : 0 < 1-exp t := by linarith
    have h := tail (exp t) e.le h1
    field_simp [hp] at h
    field_simp [hp, e]
    linarith

theorem kernel (x y : ℝ) (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) (hy₀ : 0 ≤ y) (hy₁ : y ≤ 1) :
    y * (binEntropy (x^2)/x) + x * (binEntropy (y^2)/y) +
      x*y*(121/174)*(moment x - moment y)^2 ≤ 2 * binEntropy (x*y) := by
  rcases hx₀.eq_or_lt with h | hx
  · simp [← h]
  rcases hy₀.eq_or_lt with h | hy
  · simp [← h]
  have hmx : 2 * log x ∈ Iic (0 : ℝ) := mul_nonpos_of_nonneg_of_nonpos (by norm_num) (log_nonpos hx.le hx₁)
  have hmy : 2 * log y ∈ Iic (0 : ℝ) := mul_nonpos_of_nonneg_of_nonpos (by norm_num) (log_nonpos hy.le hy₁)
  have h := concave_aux.2 hmx hmy
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
  dsimp only [smul_eq_mul] at h
  rw [show 1 / 2 * (2 * log x) + 1 / 2 * (2 * log y) = log x + log y by ring,
    exp_add, exp_log hx, exp_log hy,
    show exp (2 * log x) = x ^ 2 by rw [two_mul, exp_add, exp_log hx, sq],
    show exp (2 * log y) = y ^ 2 by rw [two_mul, exp_add, exp_log hy, sq]] at h
  have var (a b c : ℝ) : (121/174 : ℝ)*((6*a+3*b+2*c)/11)^2 ≤ a^2/2+b^2/6+c^2/12 := by
    nlinarith [sq_nonneg (3*a-2*b), sq_nonneg (2*a-c), sq_nonneg (4*b-3*c)]
  have hvar := var (x-y) (x^2-y^2) (x^3-y^3)
  unfold corr at h
  unfold moment
  have h' := mul_le_mul_of_nonneg_left h (show 0 ≤ 2*x*y by positivity)
  field_simp [hx.ne',hy.ne'] at h' ⊢
  -- Clear the residual comparison by separating the two inequalities.
  nlinarith only [h', mul_nonneg (show 0 ≤ x^2*y^2 by positivity) (sub_nonneg.mpr hvar)]

end
end C6Projected
end

section
namespace C6Intermediate
theorem bound_of_cells (cert : DualCells C6Projected.moment 0.61766 0.0356 1.000000001 (121/174)) :
    0.38234 ≤ Constant6a.C6a := by
  apply lowerBound_of_scalar (α := 0.0356) (k := 1.000000001) (by norm_num)
    (by constructor <;> norm_num) (by norm_num)
  apply scalarBound_of_exact (by norm_num) (by norm_num)
  rw [show (0.38234:ℝ) = 1-0.61766 by norm_num]
  refine exact_of_dual (by norm_num : (0:ℝ) < 0.61766)
    (by constructor <;> norm_num : (0.0356:ℝ) ∈ Set.Icc 0 1)
    (by norm_num : (0:ℝ) ≤ 121/174) ?_ cert C6Projected.kernel
  · intro z hz
    obtain ⟨hz0,hz1⟩ := hz
    constructor
    · unfold C6Projected.moment
      positivity
    · have h₂ := pow_le_one₀ hz0 hz1 (n := 2)
      have h₃ := pow_le_one₀ hz0 hz1 (n := 3)
      unfold C6Projected.moment
      linarith
end C6Intermediate
end

/- Bounds on the first two derivatives control the polynomial residual at the endpoints and between adjacent rational grid points. -/
section
namespace C6Poly
open C6Projected
noncomputable section
def Params (l u A B D : ℝ) := l ∈ Set.Icc (0:ℝ) 1 ∧ u ∈ Set.Icc (0:ℝ) 1 ∧
  |A| ≤ 0.14 ∧ |B| ≤ 0.003 ∧ |D| ≤ 0.003
private def K : ℝ := ((1-0.0356)*0.61766)*(121/174)
def P (l u A B D x : ℝ) :=
  ((1-0.0356)*0.61766)*(121/174)*x*(moment x-l)*(moment x-u) - A*(x-0.61766) -
    B*x*(moment x-l) - D*x*(u-moment x)
private def f₁ (x : ℝ) := (6+6*x+6*x^2)/11
private def f₂ (x : ℝ) := (6+12*x)/11
private def J (l u B D x : ℝ) := K*(moment x-l)*(moment x-u)-B*(moment x-l)+D*(moment x-u)
private def M (l u B D x : ℝ) := K*((moment x-l)+(moment x-u))-B+D
private def p₁ (l u A B D x : ℝ) := J l u B D x + x*(M l u B D x*f₁ x)-A
private def p₂ (l u B D x : ℝ) := 2*(M l u B D x*f₁ x)+x*(2*K*f₁ x^2+M l u B D x*f₂ x)

private theorem diff₀ (x : ℝ) : HasDerivAt moment (f₁ x) x := by
  convert! (((((hasDerivAt_id x).const_mul 6).add (((hasDerivAt_id x).pow 2).const_mul 3)).add
    (((hasDerivAt_id x).pow 3).const_mul 2)).div_const 11) using 1 <;> simp [moment,f₁] <;> ring

private theorem diff₁ (x : ℝ) : HasDerivAt f₁ (f₂ x) x := by
  convert! (((((hasDerivAt_id x).const_mul 6).const_add 6).add
    (((hasDerivAt_id x).pow 2).const_mul 6)).div_const 11) using 1 <;> simp [f₁,f₂] <;> ring

private theorem diffJ (l u B D x : ℝ) :
    HasDerivAt (J l u B D) (M l u B D x*f₁ x) x := by
  have g := (diff₀ x).sub_const l
  have h := (diff₀ x).sub_const u
  convert! ((((g.const_mul K).mul h).sub (g.const_mul B)).add (h.const_mul D)) using 1 <;>
    simp [J,M] <;> ring

private theorem diffM (l u B D x : ℝ) :
    HasDerivAt (M l u B D) (2*K*f₁ x) x := by
  convert! ((((((diff₀ x).sub_const l).add ((diff₀ x).sub_const u)).const_mul K).sub_const B).add_const D) using 1 <;>
    ring

private theorem diffP (l u A B D x : ℝ) : HasDerivAt (P l u A B D) (p₁ l u A B D x) x := by
  have h := (((hasDerivAt_id x).mul (diffJ l u B D x)).sub (((hasDerivAt_id x).sub_const 0.61766).const_mul A))
  convert! h using 1
  · funext z; dsimp [P,J,K]; ring
  · dsimp [p₁]; ring

private theorem diffP₁ (l u A B D x : ℝ) : HasDerivAt (p₁ l u A B D) (p₂ l u B D x) x := by
  convert! (((diffJ l u B D x).add ((hasDerivAt_id x).mul ((diffM l u B D x).mul (diff₁ x)))).sub_const A) using 1
  · dsimp [p₂]; ring

private theorem bounds {l u A B D x : ℝ} (hP : Params l u A B D) (hx : x ∈ Set.Icc (0:ℝ) 1) :
    |p₁ l u A B D x| ≤ 3 ∧ |p₂ l u B D x| ≤ 10 := by
  obtain ⟨hl,hu,hA,hB,hD⟩ := hP
  have hk : |K| ≤ 0.42 := by norm_num [K]
  have hx₂ := pow_le_one₀ hx.1 hx.2 (n := 2)
  have hx₃ := pow_le_one₀ hx.1 hx.2 (n := 3)
  have hf : moment x ∈ Set.Icc (0:ℝ) 1 := by
    dsimp [moment]
    exact ⟨by positivity [hx.1], by linarith [hx.2]⟩
  have ha : |moment x-l| ≤ 1 := abs_le.mpr ⟨by linarith [hf.1,hl.2], by linarith [hf.2,hl.1]⟩
  have hb : |moment x-u| ≤ 1 := abs_le.mpr ⟨by linarith [hf.1,hu.2], by linarith [hf.2,hu.1]⟩
  have hsum := (abs_add_le (moment x-l) (moment x-u)).trans (add_le_add ha hb)
  have hm : |M l u B D x| ≤ 0.85 := by
    unfold M
    calc
      _ ≤ (|K| * |(moment x-l)+(moment x-u)| + |B|) + |D| := by
        grw [abs_add_le, abs_sub, abs_mul]
      _ ≤ _ := by linarith [mul_le_mul hk hsum (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 0.42)]
  have hj : |J l u B D x| ≤ 0.43 := by
    unfold J
    calc
      _ ≤ |K| * |moment x-l| * |moment x-u| + |B| * |moment x-l| + |D| * |moment x-u| := by
        grw [abs_add_le, abs_sub, abs_mul, abs_mul, abs_mul, abs_mul]
      _ ≤ _ := by
        have e₁ := mul_le_mul hk ha (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 0.42)
        linarith [mul_le_mul e₁ hb (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 0.42*1),
          mul_le_mul hB ha (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 0.003),
          mul_le_mul hD hb (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 0.003)]
  have h₁ : |f₁ x| ≤ 2 := by rw [abs_le]; dsimp [f₁]; constructor <;> linarith [sq_nonneg x,hx.1,hx.2]
  have h₂ : |f₂ x| ≤ 2 := by rw [abs_le]; dsimp [f₂]; constructor <;> linarith [hx.1,hx.2]
  have hm₁ : |M l u B D x * f₁ x| ≤ 1.7 := by
    rw [abs_mul]; linarith [mul_le_mul hm h₁ (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 0.85)]
  have hxx : |x| ≤ 1 := (abs_of_nonneg hx.1).trans_le hx.2
  constructor
  · unfold p₁
    calc
      _ ≤ (|J l u B D x| + |x| * |M l u B D x*f₁ x|) + |A| := by
        grw [abs_sub, abs_add_le, abs_mul x]
      _ ≤ _ := by linarith [mul_le_mul hxx hm₁ (abs_nonneg _) zero_le_one]
  · unfold p₂
    have hinner : |2*K*f₁ x^2+M l u B D x*f₂ x| ≤ 5.1 := by
      calc
        _ ≤ 2 * |K| * |f₁ x| ^ 2+|M l u B D x| * |f₂ x| := by
          grw [abs_add_le]; simp [abs_mul,abs_pow]
        _ ≤ _ := by
          have hsq := pow_le_pow_left₀ (abs_nonneg _) h₁ 2
          have hk' : 2 * |K| ≤ 2*0.42 := by linarith
          linarith [mul_le_mul hk' hsq (sq_nonneg _) (by norm_num),
            mul_le_mul hm h₂ (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 0.85)]
    calc
      _ ≤ 2 * |M l u B D x*f₁ x| + |x| * |2*K*f₁ x^2+M l u B D x*f₂ x| := by
        grw [abs_add_le]; simp [abs_mul]
      _ ≤ _ := by linarith [mul_le_mul hxx hinner (abs_nonneg _) zero_le_one]

theorem lipschitz {l u A B D x y : ℝ} (hP : Params l u A B D)
    (hx : x ∈ Set.Icc (0:ℝ) 1) (hy : y ∈ Set.Icc (0:ℝ) 1) :
    |P l u A B D x - P l u A B D y| ≤ 3 * |x-y| := by
  have h := (convex_Icc (0:ℝ) 1).lipschitzOnWith_of_nnnorm_hasDerivWithin_le (C := 3)
    (fun z _ => (diffP l u A B D z).hasDerivWithinAt)
    (fun z hz => by exact_mod_cast (show ‖p₁ l u A B D z‖ ≤ (3:ℝ) from (bounds hP hz).1))
  simpa [Real.dist_eq] using h.dist_le_mul x hx y hy

theorem chord {l u A B D x y s : ℝ} (hP : Params l u A B D)
    (hx : x ∈ Set.Icc (0:ℝ) 1) (hy : y ∈ Set.Icc (0:ℝ) 1) (hs : s ∈ Set.Icc (0:ℝ) 1) :
    (1-s)*P l u A B D x + s*P l u A B D y - 10*(y-x)^2 ≤ P l u A B D ((1-s)*x+s*y) := by
  let g := fun z => P l u A B D z - 5*z^2
  have dg z : HasDerivAt g (p₁ l u A B D z - 10*z) z := by
    convert! (diffP l u A B D z).sub (((hasDerivAt_id z).pow 2).const_mul 5) using 1 <;> simp <;> ring
  have dg' z : HasDerivAt (fun z => p₁ l u A B D z - 10*z) (p₂ l u B D z - 10) z := by
    convert! (diffP₁ l u A B D z).sub ((hasDerivAt_id z).const_mul 10) using 1 <;> simp
  have conc : ConcaveOn ℝ (Set.Icc (0:ℝ) 1) g := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc ..) (f' := fun z => p₁ l u A B D z - 10*z)
      (f'' := fun z => p₂ l u B D z - 10)
    · exact fun z _ => (dg z).continuousAt.continuousWithinAt
    · exact fun z _ => (dg z).hasDerivWithinAt
    · exact fun z _ => (dg' z).hasDerivWithinAt
    · intro z hz
      linarith only [(le_abs_self (p₂ l u B D z)).trans (bounds hP (interior_subset hz)).2]
  have hh := conc.2 hx hy (sub_nonneg.mpr hs.2) hs.1 (show 1-s+s=1 by ring)
  simp only [smul_eq_mul,g] at hh
  have hcoef : 0 ≤ 10-5*s*(1-s) := by nlinarith [sq_nonneg s,hs.2]
  nlinarith only [hh,mul_nonneg hcoef (sq_nonneg (y-x))]
end
end C6Poly
end

section
open Finset BigOperators Filter Topology Real

namespace C6Reduction

theorem entropy_series {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    HasSum (fun n : ℕ => x ^ (n + 2) / (((n : ℝ) + 1) * (n + 2)))
      (x - negMulLog (1 - x)) := by
  rcases h1.eq_or_lt with rfl | hlt
  · simp only [one_pow, sub_self, negMulLog_zero, sub_zero]
    rw [hasSum_iff_tendsto_nat_of_nonneg (fun _ => by positivity)]
    let f (n : ℕ) := 1 / ((n : ℝ) + 1)
    have ht (n : ℕ) : 1 / (((n : ℝ) + 1) * (n + 2)) = f n - f (n + 1) := by
      dsimp [f]
      push_cast
      field_simp
      ring
    simp_rw [ht, sum_range_sub' f]
    simpa [f] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  · have h := hasSum_pow_div_log_of_abs_lt_one (by rwa [abs_of_nonneg h0])
    have htail := (hasSum_nat_add_iff' 1).mpr h
    have hdiff := (h.mul_left x).sub htail
    convert! hdiff using 1
    · funext n
      simp only [Nat.cast_add, Nat.cast_one]
      rw [show n + 2 = (n + 1) + 1 from rfl, pow_succ]
      field_simp
      ring
    · simp [negMulLog]
      ring


end C6Reduction
end

section
namespace C6Interval
open Real Set Filter Topology

private lemma squareDiv_series {x : ℝ} (hx : x ∈ Set.Icc 0 1) :
    HasSum (fun n : ℕ => x ^ (2*n+3) / (((n:ℝ)+1)*(n+2)))
      (x + 2*negMulLog x - binEntropy (x^2)/x) := by
  by_cases h0 : x = 0
  · subst x
    simpa using (hasSum_zero (α := ℝ) (β := ℕ))
  have h := (C6Reduction.entropy_series (sq_nonneg x) (pow_le_one₀ hx.1 hx.2)).mul_left x⁻¹
  convert! h using 1
  · funext n
    rw [← pow_mul, show 2*(n+2) = (2*n+3)+1 by omega, pow_succ]
    field_simp
    rw [← pow_add]
  · rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub, sq, negMulLog_mul]
    field_simp [h0]
    ring

theorem squareDiv_concave : ConcaveOn ℝ (Set.Icc 0 1) (fun x : ℝ => binEntropy (x^2)/x) := by
  refine ⟨convex_Icc .., ?_⟩
  intro l hl u hu r s hr hs hrs
  let x := r*l+s*u
  have hx : x ∈ Set.Icc 0 1 := (convex_Icc (0:ℝ) 1) hl hu hr hs hrs
  have h := (squareDiv_series hl).mul_left r |>.add ((squareDiv_series hu).mul_left s)
  have he := hasSum_le (f := fun n : ℕ => x^(2*n+3)/(((n:ℝ)+1)*(n+2))) (g := _)
    (fun n => by
      have hp := (convexOn_pow (𝕜 := ℝ) (2*n+3)).2 hl.1 hu.1 hr hs hrs
      dsimp only [smul_eq_mul] at hp
      change x^(2*n+3)/_ ≤ r*(l^(2*n+3)/_)+s*(u^(2*n+3)/_)
      rw [mul_div_assoc', mul_div_assoc', ← add_div]
      exact div_le_div_of_nonneg_right hp (by positivity)) (squareDiv_series hx) h
  have hn := concaveOn_negMulLog.2 hl.1 hu.1 hr hs hrs
  change r*negMulLog l + s*negMulLog u ≤ negMulLog x at hn
  change r*(binEntropy (l^2)/l)+s*(binEntropy (u^2)/u) ≤ binEntropy (x^2)/x
  nlinarith only [he, hn, show x = r*l+s*u from rfl]

private lemma entropy_semiconvex {l u : ℝ} (hl : 0 < l) (hu : u < 1) :
    ConvexOn ℝ (Set.Icc l u) (fun x : ℝ => binEntropy x + (1/(2*l*(1-u)))*x^2) := by
  let A := 1/(2*l*(1-u))
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc l u)
    (f' := fun x => log (1-x) - log x + A*(2*x))
    (f'' := fun x => -(1-x)⁻¹ - x⁻¹ + A*2)
  · exact binEntropy_continuous.continuousOn.add (by fun_prop)
  · intro x hx
    rw [interior_Icc] at hx
    have hp := hl.trans hx.1
    have hq := hx.2.trans hu
    have h := (hasDerivAt_binEntropy hp.ne' hq.ne).add (((hasDerivAt_id x).pow 2).const_mul A)
    refine (h.congr_deriv ?_).hasDerivWithinAt
    simp
  · intro x hx
    rw [interior_Icc] at hx
    have hp := hl.trans hx.1
    have hq := sub_pos.mpr (hx.2.trans hu)
    have h := (((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)).log hq.ne').sub (hasDerivAt_log hp.ne')
    have d := h.add (((hasDerivAt_id x).const_mul 2).const_mul A)
    refine (d.congr_deriv ?_).hasDerivWithinAt
    simp [div_eq_mul_inv]
  · intro x hx
    rw [interior_Icc] at hx
    have hp := hl.trans hx.1
    have hq := sub_pos.mpr (hx.2.trans hu)
    have hc := sub_pos.mpr hu
    have hm : l*(1-u) ≤ x*(1-x) := mul_le_mul hx.1.le (by linarith [hx.2] : 1-u ≤ 1-x) hc.le hp.le
    have h := one_div_le_one_div_of_le (mul_pos hl hc) hm
    unfold A
    field_simp [hp.ne', hq.ne', hc.ne', hl.ne'] at h ⊢
    nlinarith

theorem entropy_chord_upper {l u r s : ℝ} (hl : 0 < l) (hu : u < 1) (hlu : l ≤ u)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hrs : r+s=1) :
    binEntropy (r*l+s*u) ≤ r*binEntropy l+s*binEntropy u + (u-l)^2/(8*l*(1-u)) := by
  let A := 1/(2*l*(1-u))
  have h := (entropy_semiconvex hl hu).2 (show l ∈ Set.Icc l u from ⟨le_rfl,hlu⟩)
    (show u ∈ Set.Icc l u from ⟨hlu,le_rfl⟩) hr hs hrs
  simp only [smul_eq_mul] at h
  have hA : 0 ≤ A := by dsimp [A]; positivity [sub_pos.mpr hu]
  have hid : r*l^2 + s*u^2 - (r*l+s*u)^2 = r*s*(u-l)^2 := by
    rw [show r = 1-s by linarith]
    ring
  have he : A*(r*s*(u-l)^2) ≤ A*((1/4)*(u-l)^2) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (r-s),sq_sub_sq r s] : r*s ≤ 1/4)
      (sq_nonneg _)) hA
  have hd : (u-l)^2/(8*l*(1-u)) = A*((1/4)*(u-l)^2) := by dsimp [A]; field_simp; ring
  rw [hd]
  change binEntropy (r*l+s*u) + A*(r*l+s*u)^2 ≤ r*(binEntropy l + A*l^2)+s*(binEntropy u+A*u^2) at h
  linarith only [h, he, congrArg (A*·) hid]

theorem clampedEntropy_concave :
    ConcaveOn ℝ (Set.Icc 0 1) (fun x : ℝ => binEntropy (max (1/2) (2*x-1))) := by
  refine ⟨convex_Icc .., ?_⟩
  intro l hl u hu r s hr hs hrs
  let v (x : ℝ) := max (1/2) (2*x-1)
  have hvl (x : ℝ) : 2⁻¹ ≤ v x := by simpa only [v,one_div] using (le_max_left (1/2 : ℝ) (2*x-1))
  have hvu (x : ℝ) (hx : x ≤ 1) : v x ≤ 1 := max_le (by norm_num) (by linarith)
  have hj := Real.strictConcave_binEntropy.concaveOn.2
    (show v l ∈ Set.Icc 0 1 from ⟨(by norm_num : (0:ℝ) ≤ 2⁻¹).trans (hvl l), hvu l hl.2⟩)
    (show v u ∈ Set.Icc 0 1 from ⟨(by norm_num : (0:ℝ) ≤ 2⁻¹).trans (hvl u), hvu u hu.2⟩) hr hs hrs
  change r*binEntropy (v l) + s*binEntropy (v u) ≤ binEntropy (r*v l + s*v u) at hj
  have hsmall : v (r*l+s*u) ≤ r*v l+s*v u := by
    apply max_le
    · have h₁ := mul_le_mul_of_nonneg_left (le_max_left (1/2:ℝ) (2*l-1)) hr
      have h₂ := mul_le_mul_of_nonneg_left (le_max_left (1/2:ℝ) (2*u-1)) hs
      dsimp [v]; linarith
    · have h₁ := mul_le_mul_of_nonneg_left (le_max_right (1/2:ℝ) (2*l-1)) hr
      have h₂ := mul_le_mul_of_nonneg_left (le_max_right (1/2:ℝ) (2*u-1)) hs
      dsimp [v]; linarith
  have hlarge : r*v l+s*v u ≤ 1 := by
    linarith [mul_le_mul_of_nonneg_left (hvu l hl.2) hr, mul_le_mul_of_nonneg_left (hvu u hu.2) hs]
  exact hj.trans (binEntropy_strictAntiOn.antitoneOn ⟨hvl _,hsmall.trans hlarge⟩
    ⟨(hvl _).trans hsmall,hlarge⟩ hsmall)

end C6Interval
end

section
namespace C6Endpoint
open Real

private lemma h_lower {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    u * (-log u) ≤ binEntropy u := by
  rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  have h := negMulLog_nonneg (sub_nonneg.mpr h1) (sub_le_self _ h0)
  simp only [negMulLog] at *
  linarith

private lemma h_upper {u : ℝ} (h1 : u ≤ 1) :
    binEntropy u ≤ u * (-log u) + u := by
  rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  have h := negMulLog_le_one_sub_self (sub_nonneg.mpr h1)
  simp only [negMulLog] at *
  linarith

private lemma log_cut {u : ℝ} (h0 : 0 < u) (h : u ≤ 1 / 2^40) :
    27 ≤ -log u := by
  have hl := log_le_log h0 h
  rw [one_div, log_inv, log_pow] at hl
  norm_num1 at hl
  linarith [log_two_gt_d9]

/-- Endpoint growth estimate for the projected scalar entropy. -/
theorem base (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1)
    (h : min x (1-x) ≤ 1/2^40) :
    2 * min x (1-x) ≤ ((1-0.0356)*0.61766)*(binEntropy (x^2)/x) -
      (1+1/10^9)*binEntropy x := by
  rcases h0.eq_or_lt with rfl | hx
  · norm_num
  rcases h1.eq_or_lt with rfl | hx1
  · norm_num
  have hs0 : 0 ≤ x^2 := sq_nonneg _
  have hs1 : x^2 ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_left h1 h0]
  by_cases hm : x ≤ 1-x
  · rw [min_eq_left hm] at h ⊢
    have hl := log_cut hx h
    have hu := h_upper h1
    have hsq := h_lower hs0 hs1
    rw [log_pow] at hsq
    norm_num1 at hsq
    have hg : 2*x*(-log x) ≤ binEntropy (x^2)/x := by
      apply (le_div_iff₀ hx).mpr
      linarith only [hsq]
    have hpos := mul_le_mul_of_nonneg_left hl hx.le
    linarith only [hg, hu, hpos, hx]
  · rw [min_eq_right (le_of_not_ge hm)] at h ⊢
    let y := 1-x
    have hy : 0 < y := sub_pos.mpr hx1
    have hy1 : y ≤ 1 := sub_le_self _ h0
    have hl := log_cut hy h
    have hu := h_upper hy1
    rw [show binEntropy y = binEntropy x from binEntropy_one_sub x] at hu
    have hs := h_lower (sub_nonneg.mpr hs1) (sub_le_self _ hs0)
    rw [binEntropy_one_sub] at hs
    have hid : 1-x^2 = y*(1+x) := by dsimp [y]; ring
    rw [hid, log_mul hy.ne' (by positivity : (1+x : ℝ) ≠ 0)] at hs
    have hlog : log (1+x) ≤ 1 :=
      (log_le_log (by positivity) (by linarith : 1+x ≤ 2)).trans (by linarith [log_two_lt_d9])
    have hb : 2*y*(-log y - 1) ≤ binEntropy (x^2)/x := by
      apply (le_div_iff₀ hx).mpr
      calc
        _ ≤ y*(1+x)*(-log y - 1) := by
          have h' := mul_nonneg (mul_nonneg hy.le (sub_nonneg.mpr h1))
            (show 0 ≤ -log y - 1 by linarith)
          linarith only [h']
        _ ≤ y*(1+x)*(-(log y + log (1+x))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
        _ ≤ _ := hs
    have hl' := mul_le_mul_of_nonneg_left hl hy.le
    change 2*y ≤ _
    linarith only [hb, hu, hl', hy]

/-- The polynomial correction on the final interval of moment values is
absorbed by the endpoint entropy growth. -/
theorem last_slice (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) (h : min x (1-x) ≤ 1/2^40) :
    0 ≤ ((1-0.0356)*0.61766)*(binEntropy (x^2)/x) - (1+1/10^9)*binEntropy x +
      ((1-0.0356)*0.61766)*(121/174)*x*
        (((6*x+3*x^2+2*x^3)/11)-0.935)*(((6*x+3*x^2+2*x^3)/11)-1) := by
  let f := (6*x+3*x^2+2*x^3)/11
  have hf0 : 0 ≤ f := by dsimp [f]; positivity
  have hx2 : x^2 ≤ 1 := by nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]
  have hx3 : x^3 ≤ 1 := by nlinarith [mul_nonneg h0 (sub_nonneg.mpr hx2)]
  have hf1 : f ≤ 1 := by dsimp [f]; linarith
  have hfm : 1-f ≤ 2*(1-x) := by
    have hfact : 1-f = (1-x)*(11+5*x+2*x^2)/11 := by dsimp [f]; ring
    rw [hfact]
    nlinarith only [mul_nonneg (sub_nonneg.mpr h1)
      (show 0 ≤ 22-(11+5*x+2*x^2) by linarith)]
  have he := base x h0 h1 h
  change 0 ≤ _ + ((1-0.0356)*0.61766)*(121/174)*x*(f-0.935)*(f-1)
  by_cases hm : x ≤ 1-x
  · rw [min_eq_left hm] at he
    have hf : 0 ≤ 0.935 - f := by
      dsimp [f]
      have hx2' : x^2 ≤ x := by nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]
      have hx3' : x^3 ≤ x := by nlinarith [mul_nonneg h0 (sub_nonneg.mpr hx2)]
      linarith
    nlinarith only [he, h0, mul_nonneg h0
      (mul_nonneg hf (sub_nonneg.mpr hf1))]
  · rw [min_eq_right (le_of_not_ge hm)] at he
    have h' : 0 ≤ (1-f) * (1 - x*(f-0.935)) := by
      apply mul_nonneg (sub_nonneg.mpr hf1)
      nlinarith [mul_nonneg h0 (sub_nonneg.mpr hf1)]
    nlinarith only [h', hfm, he, sub_nonneg.mpr hf1, sub_nonneg.mpr h1]
end C6Endpoint
end

section
namespace C6Interval
open Finset Real

/-- The odd Taylor polynomial for twice the inverse hyperbolic tangent. -/
def oddSum (z : ℚ) : ℕ → ℚ
  | 0 => 0
  | n+1 => oddSum z n + z ^ (2*n+1) / (2*n+1 : ℚ)

def logPoly (z : ℚ) (n : ℕ) : ℚ := 2 * oddSum z n

private lemma oddSum_eq (z : ℚ) (n : ℕ) :
    oddSum z n = ∑ i ∈ range n, z ^ (2*i+1) / (2*i+1 : ℚ) := by
  induction n with
  | zero => simp [oddSum]
  | succ n ih => rw [oddSum, sum_range_succ, ih]

def logErr (z : ℚ) (n : ℕ) : ℚ := 2 * (z^(2*n+1)/(1-z^2))

/-- For q in (0,1], this argument z satisfies (1+z)/(1-z) = 1/q. -/
def arg (q : ℚ) := (1-q)/(1+q)

/-- The two rational bounds are for minus log(q). Dyadic rescaling makes the
Taylor argument at most one third whenever q ≥ 2^(-fuel-1). -/
def negLogBounds (n : ℕ) : ℕ → ℚ → ℚ × ℚ
  | 0, q => (logPoly (arg q) n, logPoly (arg q) n + logErr (arg q) n)
  | k+1, q =>
    if q < 1/2 then
      let b := negLogBounds n k (2*q)
      (b.1 + 0.6931471803, b.2 + 0.6931471808)
    else (logPoly (arg q) n, logPoly (arg q) n + logErr (arg q) n)

private theorem approx_at (q : ℚ) (n : ℕ) (hq : 0 < q) (h1 : q ≤ 1) :
    (logPoly (arg q) n : ℝ) ≤ -log q ∧
      -log q ≤ ((logPoly (arg q) n + logErr (arg q) n : ℚ) : ℝ) := by
  let z : ℝ := arg q
  have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
  have h1' : (q : ℝ) ≤ 1 := by exact_mod_cast h1
  have hz : z = (1-(q : ℝ))/(1+q) := by simp [z, arg]
  have hz0 : 0 ≤ z := hz ▸ div_nonneg (sub_nonneg.mpr h1') (by linarith)
  have hz1 : z < 1 := by rw [hz]; apply (div_lt_iff₀ (by linarith)).mpr; linarith
  have he : (1+z)/(1-z) = (q : ℝ)⁻¹ := by
    rw [hz]
    field_simp [show (1:ℝ)+q ≠ 0 by linarith, hq'.ne']
    all_goals ring
  have hl := sum_range_le_log_div hz0 hz1 n
  have hu := log_div_le_sum_range_add hz0 hz1 n
  rw [he, log_inv] at hl hu
  simp only [logPoly, oddSum_eq, logErr]
  push_cast
  change 2 * (∑ i ∈ range n, z^(2*i+1) / (2*(i:ℝ)+1)) ≤ -log q ∧
    -log q ≤ 2 * (∑ i ∈ range n, z^(2*i+1)/(2*(i:ℝ)+1)) + 2*(z^(2*n+1)/(1-z^2))
  constructor <;> linarith

theorem negLogBounds_spec (q : ℚ) (n fuel : ℕ) (hq : 0 < q) (h1 : q ≤ 1) :
    ((negLogBounds n fuel q).1 : ℝ) ≤ -log q ∧ -log q ≤ ((negLogBounds n fuel q).2 : ℝ) := by
  induction fuel generalizing q with
  | zero => exact approx_at q n hq h1
  | succ k ih =>
    rw [negLogBounds]
    split_ifs with ht
    · have hi := ih (2*q) (by linarith) (by linarith)
      have hn : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
      push_cast at *
      rw [log_mul (by norm_num) hn] at hi
      constructor <;> linarith [log_two_gt_d9, log_two_lt_d9]
    · exact approx_at q n hq h1

def negMulLogBounds (n fuel : ℕ) (q : ℚ) : ℚ × ℚ :=
  if q = 0 then (0,0) else
  let b := negLogBounds n fuel q
  (q*b.1, q*b.2)

theorem negMulLogBounds_spec {q : ℚ} (n fuel : ℕ) (hq : 0 ≤ q) (h1 : q ≤ 1) :
    ((negMulLogBounds n fuel q).1 : ℝ) ≤ negMulLog q ∧
      negMulLog q ≤ ((negMulLogBounds n fuel q).2 : ℝ) := by
  rcases hq.eq_or_lt with he|hp
  · subst q; simp [negMulLogBounds]
  have ht := negLogBounds_spec q n fuel hp h1
  have hq' : 0 ≤ (q : ℝ) := by exact_mod_cast hq
  simpa [negMulLogBounds, hp.ne', negMulLog] using
    And.intro (mul_le_mul_of_nonneg_left ht.1 hq') (mul_le_mul_of_nonneg_left ht.2 hq')

def entropyBounds (n fuel : ℕ) (q : ℚ) : ℚ × ℚ :=
  let a := negMulLogBounds n fuel q
  let b := negMulLogBounds n fuel (1-q)
  (a.1+b.1, a.2+b.2)

theorem entropyBounds_spec {q : ℚ} (n fuel : ℕ) (hq : 0 ≤ q) (h1 : q ≤ 1) :
    ((entropyBounds n fuel q).1 : ℝ) ≤ binEntropy q ∧
      binEntropy q ≤ ((entropyBounds n fuel q).2 : ℝ) := by
  have ha := negMulLogBounds_spec n fuel hq h1
  have hb := negMulLogBounds_spec n fuel (q := 1-q) (by linarith) (by linarith)
  rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simpa [entropyBounds] using And.intro (add_le_add ha.1 hb.1) (add_le_add ha.2 hb.2)


end C6Interval
end

section
namespace C6Fast

/-- Integer endpoints enclose entropy in units of min(q,1-q) times 10^-14. -/
inductive Table where
  | leaf
  | node (q : ℚ) (lower upper : ℕ) (l r : Table)

private def units (q : ℚ) (n : ℕ) := n * min q (1-q) / 10^14

private def checkPoint (q : ℚ) (lo hi : ℕ) :=
  let b := C6Interval.entropyBounds 7 96 q
  decide (units q lo ≤ b.1 ∧ b.2 ≤ units q hi)

private def verified : Table → Bool
  | .leaf => true
  | .node q lo hi l r => checkPoint q lo hi && verified l && verified r

private def get : Table → ℚ → ℚ × ℚ
  | .leaf, x => C6Interval.entropyBounds 7 96 x
  | .node q lo hi l r, x => if x < q then get l x else if q < x then get r x else (units x lo,units x hi)

private theorem get_spec {t : Table} (ht : verified t = true) {x : ℚ}
    (hx : 0 ≤ x) (h1 : x ≤ 1) :
    ((get t x).1 : ℝ) ≤ Real.binEntropy x ∧ Real.binEntropy x ≤ ((get t x).2 : ℝ) := by
  induction t with
  | leaf => exact C6Interval.entropyBounds_spec 7 96 hx h1
  | node q lo hi l r ihl ihr =>
    simp only [verified, Bool.and_eq_true] at ht
    rw [get]
    split_ifs with h h'
    · exact ihl ht.1.2
    · exact ihr ht.2
    · have eq : x = q := le_antisymm (le_of_not_gt h') (le_of_not_gt h)
      subst q
      have hbound := ht.1.1
      simp only [checkPoint, decide_eq_true_eq] at hbound
      have he := C6Interval.entropyBounds_spec 7 96 hx h1
      exact ⟨(Rat.cast_le.mpr hbound.1).trans he.1, he.2.trans (Rat.cast_le.mpr hbound.2)⟩
private def tab0 : Table := (.node (1/4503599627370496) 3704365336555601 3704365354786239 (.node (1/73786976294838206464) 4674771388975601 4674771407906239 (.node (1/18889465931478580854784) 5229289133215601 5229289152546239 (.node (1/302231454903657293676544) 5506548005335601 5506548024866239 (.node (1/1208925819614629174706176) 5645177441395601 5645177461026239 .leaf .leaf) (.node (1/75557863725914323419136) 5367918569275601 5367918588706239 .leaf .leaf)) (.node (1/1180591620717411303424) 4952030261095601 4952030280226239 (.node (1/4722366482869645213696) 5090659697155601 5090659716386239 .leaf .leaf) (.node (1/295147905179352825856) 4813400825035601 4813400844066239 .leaf .leaf))) (.node (1/288230376151711744) 4120253644735601 4120253663266239 (.node (1/4611686018427387904) 4397512516855601 4397512535586239 (.node (1/18446744073709551616) 4536141952915601 4536141971746239 .leaf .leaf) (.node (1/1152921504606846976) 4258883080795601 4258883099426239 .leaf .leaf)) (.node (1/18014398509481984) 3842994772615601 3842994790946239 (.node (1/72057594037927936) 3981624208675601 3981624227106239 .leaf .leaf) .leaf))) (.node (1/274877906944) 2733959284135419 2733959301666057 (.node (1/17592186044416) 3149847592315598 3149847610146236 (.node (1/281474976710656) 3427106464435601 3427106482466238 (.node (1/1125899906842624) 3565735900495601 3565735918626239 .leaf .leaf) (.node (1/70368744177664) 3288477028375600 3288477046306238 .leaf .leaf)) (.node (1/1099511627776) 2872588720195555 2872588737826193 (.node (1/4398046511104) 3011218156255589 3011218173986227 .leaf .leaf) (.node (1/549755813888) 2803274002165510 2803274019746148 .leaf .leaf))) (.node (1/17179869184) 2456700412012690 2456700429343328 (.node (1/68719476736) 2595329848074873 2595329865505511 (.node (1/137438953472) 2664644566105237 2664644583585875 .leaf .leaf) (.node (1/34359738368) 2526015130044146 2526015147424783 .leaf .leaf)) (.node (1/4294967296) 2318070975943959 2318070993174597 (.node (1/8589934592) 2387385693979780 2387385711260418 .leaf .leaf) .leaf))))

private def tab1 : Table := (.node (1/65536) 1209034724532267 1209034740962905 (.node (1/8388608) 1694238507725136 1694238524505774 (.node (1/134217728) 1971497385433072 1971497402413710 (.node (1/536870912) 2110126821772468 2110126838853106 (.node (1/1073741824) 2179441539849035 2179441556979672 .leaf .leaf) (.node (1/268435456) 2040812103649336 2040812120679974 .leaf .leaf)) (.node (1/33554432) 1832867948255485 1832867965136122 (.node (1/67108864) 1902182667030543 1902182683961181 .leaf .leaf) (.node (1/16777216) 1763553228735368 1763553245566006 .leaf .leaf))) (.node (1/524288) 1416979546198108 1416979562778746 (.node (1/2097152) 1555609053783739 1555609070464377 (.node (1/4194304) 1624923783734671 1624923800465309 .leaf .leaf) (.node (1/1048576) 1486294311911870 1486294328542508 .leaf .leaf)) (.node (1/131072) 1278349824034904 1278349840515542 (.node (1/262144) 1347664732800495 1347664749331133 .leaf .leaf) .leaf))) (.node (1/256) 654322175924577 654322191955215 (.node (1/4096) 931764407330819 931764423561457 (.node (1/16384) 1070402999595698 1070403015926336 (.node (1/32768) 1139719243551172 1139719259931810 .leaf .leaf) (.node (1/8192) 1001085229621608 1001085245902246 .leaf .leaf)) (.node (1/1024) 793098335268263 793098351398901 (.node (1/2048) 862437479288487 862437495469125 .leaf .leaf) (.node (1/512) 723734741375152 723734757455790 .leaf .leaf))) (.node (25/1024) 470028837638946 470028837888952 (.node (9/1024) 572983976324206 572983977730469 (.node (1/128) 584811378960630 584811394941267 .leaf .leaf) (.node (1/64) 515102956074877 515102972005515 .leaf .leaf)) (.node (9/256) 433016504752236 433016506058499 (.node (1/32) 444994553920800 444994569801437 .leaf .leaf) .leaf))))

private def tab2 : Table := (.node (1/2147483648) 2248756257902318 2248756275082956 tab0 tab1)

private def tab3 : Table := (.node (1/4) 224934056791126 224934072521893 (.node (5/32) 277375278850166 277375279009386 (.node (25/256) 327580156060130 327580156210136 (.node (81/1024) 349638571378647 349638571568720 (.node (1/16) 374066652821957 374066668652595 .leaf .leaf) (.node (3/32) 331871098387986 331871098538030 .leaf .leaf)) (.node (1/8) 301416127922767 301416143703404 (.node (121/1024) 307412402551021 307412402701022 .leaf .leaf) (.node (9/64) 288779677110620 288779678316883 .leaf .leaf))) (.node (7/32) 240146888869424 240146888969441 (.node (3/16) 257374701375747 257374701475793 (.node (169/1024) 271409757444948 271409757554644 .leaf .leaf) (.node (49/256) 255088654995797 255088655095814 .leaf .leaf)) (.node (961/4096) 232205156191178 232205156291226 (.node (225/1024) 239644063401606 239644063501624 .leaf .leaf) .leaf))) (.node (5329/16384) 193929571055469 193929571130713 (.node (1225/4096) 203989555111001 203989555380170 (.node (9/32) 211246230203088 211246231360199 (.node (1089/4096) 217816465607523 217816469857415 .leaf .leaf) (.node (289/1024) 210839099958165 210839101023330 .leaf .leaf)) (.node (5/16) 198747639827449 198747639941376 (.node (5041/16384) 200609045987904 200609046136664 .leaf .leaf) (.node (81/256) 197256171355764 197256171451609 .leaf .leaf))) (.node (361/1024) 184094284592824 184094284678366 (.node (5625/16384) 187349912584227 187349912658795 (.node (1369/4096) 190627917506805 190627917577274 .leaf .leaf) (.node (11/32) 187197542668872 187197542743802 .leaf .leaf)) (.node (1521/4096) 177645187189315 177645187322935 (.node (5929/16384) 180859785326325 180859785430560 .leaf .leaf) .leaf))))

private def tab4 : Table := (.node (110889/262144) 161047636961270 161047637798437 (.node (13/32) 166268204859233 166268205298830 (.node (25/64) 171270870017920 171270870266108 (.node (6241/16384) 174449280366014 174449280544907 (.node (24649/65536) 176044972359166 176044972513009 .leaf .leaf) (.node (25281/65536) 172857962301246 172857962511129 .leaf .leaf)) (.node (6561/16384) 168108773492358 168108773846243 (.node (25921/65536) 169687856043506 169687856339002 .leaf .leaf) (.node (26569/65536) 166533475977776 166533476403674 .leaf .leaf))) (.node (27225/65536) 163393652474415 163393653098426 (.node (1681/4096) 164961817523488 164961818038152 (.node (106929/262144) 165747200978014 165747201445980 .leaf .leaf) (.node (108241/262144) 164177307416654 164177307983147 .leaf .leaf)) (.node (6889/16384) 161828835406525 161828836165155 (.node (109561/262144) 162610834525285 162610835213114 .leaf .leaf) .leaf))) (.node (455625/1048576) 157541665507567 157541666818382 (.node (441/1024) 158708664124914 158708665252878 (.node (112225/262144) 159487569475753 159487570496616 (.node (27889/65536) 160267221035626 160267221959897 .leaf .leaf) (.node (450241/1048576) 159098024659194 159098025732227 .leaf .leaf)) (.node (113569/262144) 157930486820509 157930488067209 (.node (452929/1048576) 158319485602381 158319486788183 .leaf .leaf) .leaf)) (.node (114921/262144) 156376243653267 156376245177462 (.node (458329/1048576) 156764546197726 156764547647109 (.node (28561/65536) 157153019391077 157153020769395 .leaf .leaf) (.node (7/16) 156643247257591 156643248729929 .leaf .leaf)) (.node (7225/16384) 155600141408784 155600143094642 (.node (461041/1048576) 155988109482421 155988111085373 .leaf .leaf) .leaf))))

private def tab5 : Table := (.node (3/8) 176416863476260 176416863625004 tab3 tab4)

private def tab6 : Table := (.node (49/1024) 401533469495037 401533469695053 tab2 tab5)

private def tab7 : Table := (.node (7535025/16777216) 153178962066541 153178964378944 (.node (1874161/4194304) 153856279429291 153856281545616 (.node (466489/1048576) 154437210988132 154437212949812 (.node (116281/262144) 154824694441300 154824696306289 (.node (1857769/4194304) 155018495747924 155018497566393 .leaf .leaf) (.node (1863225/4194304) 154630932949765 154630934862481 .leaf .leaf)) (.node (29241/65536) 154049884513333 154049886576785 (.node (1868689/4194304) 154243528271116 154243530283031 .leaf .leaf) (.node (7491169/16777216) 153953077154941 153953079244661 .leaf .leaf))) (.node (1879641/4194304) 153469184139932 153469186366148 (.node (469225/1048576) 153662712733393 153662714903961 (.node (7502121/16777216) 153759491300678 153759493443951 .leaf .leaf) (.node (7513081/16777216) 153565943691719 153565945889933 .leaf .leaf)) (.node (117649/262144) 153275693363085 153275695646391 (.node (7524049/16777216) 153372434042300 153372436296879 .leaf .leaf) .leaf))) (.node (1901641/4194304) 151922292755998 151922295482501 (.node (1890625/4194304) 152695445072244 152695447535839 (.node (7546009/16777216) 152985527478444 152985529850168 (.node (1885129/4194304) 153082240116914 153082242458788 .leaf .leaf) (.node (471969/1048576) 152888824115361 152888826517318 .leaf .leaf)) (.node (1896129/4194304) 152308796715952 152308799307647 (.node (1849/4096) 152502102701253 152502105228081 .leaf .leaf) (.node (474721/1048576) 152115526829770 152115529488009 .leaf .leaf))) (.node (1912689/4194304) 151149708845946 151149711863598 (.node (1907161/4194304) 151535930898163 151535933766530 (.node (119025/262144) 151729094207792 151729097004323 .leaf .leaf) (.node (477481/1048576) 151342802539976 151342805482034 .leaf .leaf)) (.node (1918225/4194304) 150763624300463 150763627475204 (.node (29929/65536) 150956649528639 150956652623836 .leaf .leaf) .leaf))))

private def tab8 : Table := (.node (126025/262144) 144026969449061 144026977165868 (.node (30625/65536) 147872140496135 147872145142081 (.node (7569/16384) 149413378006964 149413381798986 (.node (120409/262144) 150184750272396 150184753698291 (.node (1923769/4194304) 150377674960337 150377678300374 .leaf .leaf) (.node (483025/1048576) 149798999419517 149799003023822 .leaf .leaf)) (.node (121801/262144) 148642514256137 148642518453461 (.node (485809/1048576) 149027883723805 149027887713332 .leaf .leaf) (.node (488601/1048576) 148257267286973 148257271702918 .leaf .leaf))) (.node (121/256) 146332788594507 146332794286433 (.node (15/32) 147454459814610 147454464723631 (.node (491401/1048576) 147487131560141 147487136448054 .leaf .leaf) (.node (123201/262144) 147102238152096 147102243294558 .leaf .leaf)) (.node (31329/65536) 144795173025581 144795179998194 (.node (124609/262144) 145563773135582 145563779435504 .leaf .leaf) .leaf))) (.node (1/2) 138629434051202 138629465412477 (.node (32041/65536) 141724548700030 141724559157612 (.node (31/64) 143000529936487 143000538773095 (.node (7921/16384) 143259143521073 143259152061095 .leaf .leaf) (.node (127449/262144) 142491676283284 142491685733843 .leaf .leaf)) (.node (2025/4096) 140191235943640 140191248746252 (.node (128881/262144) 140957741654300 140957753225510 .leaf .leaf) (.node (32761/65536) 138659051265372 138659066934713 .leaf .leaf))) (.node (33/64) 143000529936487 143000538773095 (.node (65/128) 140805099956242 140805111762869 (.node (8281/16384) 140140150534690 140140163423870 .leaf .leaf) (.node (33489/65536) 141698841788820 141698852281942 .leaf .leaf)) (.node (34225/65536) 144873328548135 144873335449182 (.node (529/1024) 143276394570032 143276403090627 .leaf .leaf) .leaf))))

private def tab9 : Table := (.node (480249/1048576) 150570632873666 150570636130004 tab7 tab8)

private def tab10 : Table := (.node (37/64) 161396145054250 161396145855364 (.node (9025/16384) 153168549678096 153168551993653 (.node (69/128) 149714941727036 149714945371444 (.node (17/32) 147454459814610 147454464723631 (.node (8649/16384) 146490185824664 146490191399596 .leaf .leaf) (.node (34969/65536) 148127532217262 148127536709379 .leaf .leaf)) (.node (35721/65536) 151466082573637 151466085468438 (.node (2209/4096) 149785958637950 149785962248446 .leaf .leaf) (.node (35/64) 151999158810625 151999161509763 .leaf .leaf))) (.node (37249/65536) 158416925974806 158416927145844 (.node (36481/65536) 154894035485607 154894037333813 (.node (71/128) 154308210802183 154308212797177 .leaf .leaf) (.node (9/16) 156643247257591 156643248729929 .leaf .leaf)) (.node (9409/16384) 160215848489066 160215849419395 (.node (73/128) 159005471523946 159005472609778 .leaf .leaf) .leaf))) (.node (39/64) 171270870017920 171270870266108 (.node (38809/65536) 165772435627933 165772436094479 (.node (75/128) 163816592104626 163816592696845 (.node (38025/65536) 162040829850062 162040830588760 .leaf .leaf) (.node (2401/4096) 163892725824637 163892726411322 .leaf .leaf)) (.node (9801/16384) 167680904888130 167680905260090 (.node (19/32) 166268204859233 166268205298830 .leaf .leaf) (.node (77/128) 168752449034079 168752449362656 .leaf .leaf))) (.node (159/256) 175116178026952 175116178194714 (.node (157/256) 172543403178880 172543403395718 (.node (625/1024) 171588155978866 171588156218727 .leaf .leaf) (.node (79/128) 173825099616547 173825099806808 .leaf .leaf)) (.node (5/8) 176416863476260 176416863625004 (.node (10201/16384) 175623102231676 175623102391625 .leaf .leaf) .leaf))))

private def tab11 : Table := (.node (21/32) 187197542668872 187197542743802 (.node (331/512) 183753073513703 183753073600813 (.node (327/512) 181048326725817 181048326828704 (.node (2601/4096) 179795348206812 179795348319370 (.node (81/128) 179047989273402 179047989392585 .leaf .leaf) (.node (163/256) 180378914155132 180378914262974 .leaf .leaf)) (.node (329/512) 182395214205193 182395214299436 (.node (41/64) 181720415769808 181720415868172 .leaf .leaf) (.node (165/256) 183072755465978 183072755556478 .leaf .leaf))) (.node (167/256) 185811036159740 185811036238631 (.node (83/128) 184436202849367 184436202933422 (.node (10609/16384) 184115633720302 184115633805749 .leaf .leaf) (.node (333/512) 185122178525697 185122178607016 .leaf .leaf)) (.node (671/1024) 186849805617729 186849805693538 (.node (335/512) 186502811945825 186502812022587 .leaf .leaf) .leaf))) (.node (679/1024) 189652915753970 189652915824889 (.node (169/256) 188596019101063 188596019173227 (.node (337/512) 187895265718092 187895265791486 (.node (673/1024) 187546027791898 187546027866022 .leaf .leaf) (.node (675/1024) 188245261217836 188245261290577 .leaf .leaf)) (.node (339/512) 189299841458225 189299841529476 (.node (677/1024) 188947544217718 188947544289384 .leaf .leaf) .leaf)) (.node (341/512) 190716850911006 190716850981470 (.node (681/1024) 190361415444394 190361415514916 (.node (85/128) 190006772077775 190006772148450 .leaf .leaf) (.node (1363/2048) 190539033847456 190539033917937 .leaf .leaf)) (.node (683/1024) 191073083577721 191073083648228 (.node (1365/2048) 190894867273903 190894867344376 .leaf .leaf) .leaf))))

private def tab12 : Table := (.node (161/256) 177727387676125 177727387808820 tab10 tab11)

private def tab13 : Table := (.node (67/128) 145216659490548 145216666085822 tab9 tab12)

private def tab14 : Table := (.node (463761/1048576) 155212337154727 155212338927855 tab6 tab13)

private def tab15 : Table := (.node (43/64) 192866386486820 192866386559275 (.node (2743/4096) 192056876123782 192056876194975 (.node (2739/4096) 191698424502832 191698424573673 (.node (2737/4096) 191519503313815 191519503384526 (.node (171/256) 191430118588089 191430118658745 .leaf .leaf) (.node (1369/2048) 191608938591509 191608938662281 .leaf .leaf)) (.node (2741/4096) 191877548553888 191877548624890 (.node (685/1024) 191787961129621 191787961200539 .leaf .leaf) (.node (1371/2048) 191967186857821 191967186928914 .leaf .leaf))) (.node (2747/4096) 192416144461408 192416144533076 (.node (2745/4096) 192236407872136 192236407943550 (.node (343/512) 192146616434315 192146616505614 .leaf .leaf) (.node (1373/2048) 192326250520142 192326250591679 .leaf .leaf)) (.node (1375/2048) 192686134878203 192686134950317 (.node (687/1024) 192506089779187 192506089850996 .leaf .leaf) .leaf))) (.node (1383/2048) 194133986878441 194133986954390 (.node (1379/2048) 193408387110206 193408387183908 (.node (689/1024) 193227511925905 193227511999153 (.node (1377/2048) 193046845277571 193046845350403 .leaf .leaf) (.node (11025/16384) 193250109905688 193250109978990 .leaf .leaf)) (.node (1381/2048) 193770765815017 193770765889755 (.node (345/512) 193589471511808 193589471586006 .leaf .leaf) (.node (691/1024) 193952270707128 193952270782448 .leaf .leaf))) (.node (1387/2048) 194862978267971 194862978346932 (.node (1385/2048) 194498055835016 194498055912367 (.node (173/256) 194315915022281 194315915098906 .leaf .leaf) (.node (693/1024) 194680410016076 194680410094205 .leaf .leaf)) (.node (695/1024) 195411974520377 195411974602179 (.node (347/512) 195045761296312 195045761376161 .leaf .leaf) .leaf))))

private def tab16 : Table := (.node (179/256) 203312141596098 203312141833128 (.node (11/16) 198747639827449 198747639941376 (.node (175/256) 197256171355764 197256171451609 (.node (349/512) 196515843186174 196515843275447 (.node (697/1024) 196147009681174 196147009767665 .leaf .leaf) (.node (699/1024) 196885561772809 196885561865191 .leaf .leaf)) (.node (351/512) 198000087437020 198000087540986 (.node (701/1024) 197627677903119 197627678002814 .leaf .leaf) (.node (2809/4096) 198093331623066 198093331728170 .leaf .leaf))) (.node (89/128) 201775211956402 201775212136553 (.node (177/256) 200253851583568 200253851724387 (.node (353/512) 199498877811581 199498877937655 .leaf .leaf) (.node (355/512) 201012612270488 201012612429139 .leaf .leaf)) (.node (11449/16384) 203143268333799 203143268563556 (.node (357/512) 202541703707174 202541703913181 .leaf .leaf) .leaf))) (.node (47089/65536) 211150705835211 211150706970076 (.node (181/256) 206434472765142 206434473199952 (.node (45/64) 204865077278306 204865077596909 (.node (359/512) 204086580730348 204086581004533 .leaf .leaf) (.node (46225/65536) 205751941688776 205751942068165 .leaf .leaf)) (.node (729/1024) 208420084062920 208420084713159 (.node (91/128) 208020799723760 208020800323191 .leaf .leaf) (.node (183/256) 209624548707264 209624549538746 .leaf .leaf))) (.node (11881/16384) 213947052296866 213947054290497 (.node (185/256) 212886375754520 212886377366671 (.node (23/32) 211246230203088 211246231360199 .leaf .leaf) (.node (371/512) 213713544709622 213713546612487 .leaf .leaf)) (.node (190969/262144) 215370956771485 215370959414603 (.node (93/128) 214545539161588 214545541407128 .leaf .leaf) .leaf))))

private def tab17 : Table := (.node (87/128) 195779055395862 195779055479870 tab15 tab16)

private def tab18 : Table := (.node (191/256) 223147735358035 223147746803085 (.node (3025/4096) 219751228777724 219751234910307 (.node (47/64) 217923253842682 217923258180392 (.node (47961/65536) 216812628706593 216812632208979 (.node (187/256) 216224297768144 216224300892051 .leaf .leaf) (.node (375/512) 217071212466704 217071216148793 .leaf .leaf)) (.node (377/512) 218780501317372 218780506424511 (.node (192721/262144) 218272551551314 218272556188346 .leaf .leaf) (.node (189/256) 219643036061223 219643042070621 .leaf .leaf))) (.node (779689/1048576) 222005562752385 222005572057484 (.node (194481/262144) 221249185000599 221249193100996 (.node (379/512) 220510941046415 220510948112987 .leaf .leaf) (.node (95/128) 221384301101414 221384309405711 .leaf .leaf)) (.node (48841/65536) 222766967176492 222766977861776 (.node (381/512) 222263202967597 222263212719899 .leaf .leaf) .leaf))) (.node (790321/1048576) 226651968880232 226651968980335 (.node (3/4) 224934056791126 224934072521893 (.node (383/512) 224037989018549 224038002441013 (.node (783225/1048576) 223533470344232 223533482610118 .leaf .leaf) (.node (196249/262144) 224305145888994 224305159964301 .leaf .leaf)) (.node (385/512) 225836034860751 225836034960866 (.node (786769/1048576) 225082070083276 225082070183403 .leaf .leaf) (.node (12321/16384) 225864317914563 225864318014678 .leaf .leaf))) (.node (97/128) 228578404876532 228578404976611 (.node (198025/262144) 227445103336193 227445103436285 (.node (193/256) 226744018305874 226744018405976 .leaf .leaf) (.node (793881/1048576) 228243803445282 228243803545365 .leaf .leaf)) (.node (797449/1048576) 229858238638142 229858238738209 (.node (49729/65536) 229048153231802 229048153331876 .leaf .leaf) .leaf))))

private def tab19 : Table := (.node (3249/4096) 246470199726432 246470199826440 (.node (99/128) 236177343219660 236177343319688 (.node (804609/1048576) 233157725798952 233157725898994 (.node (801025/1048576) 231495970025257 231495970125310 (.node (199809/262144) 230674147583564 230674147683623 .leaf .leaf) (.node (49/64) 232323798021775 232323798121823 .leaf .leaf)) (.node (197/256) 234236579668257 234236579768294 (.node (201601/262144) 233997849818431 233997849918469 .leaf .leaf) (.node (50625/65536) 235697084040307 235697084140337 .leaf .leaf))) (.node (205209/262144) 240954279104434 240954279204449 (.node (12769/16384) 239174417162091 239174417262110 (.node (203401/262144) 237422319877115 237422319977139 .leaf .leaf) (.node (25/32) 240146888869424 240146888969441 .leaf .leaf)) (.node (101/128) 244241134016998 244241134117008 (.node (51529/65536) 242762855255318 242762855355330 .leaf .leaf) .leaf))) (.node (105/128) 262076826247121 262076826347455 (.node (13225/16384) 254277200744979 254277200844992 (.node (52441/65536) 250305103719651 250305103819657 (.node (51/64) 248469757017844 248469757117850 .leaf .leaf) (.node (103/128) 252843569437424 252843569537432 .leaf .leaf)) (.node (53361/65536) 258397258545275 258397258645346 (.node (13/16) 257374701375747 257374701475793 .leaf .leaf) .leaf)) (.node (107/128) 272058177576243 272058177688182 (.node (53/64) 266965435547636 266965435649777 (.node (841/1024) 262677364388753 262677364489178 .leaf .leaf) (.node (13689/16384) 271774065387562 271774065498465 .leaf .leaf)) (.node (27/32) 277375278850166 277375279009386 (.node (215/256) 274687304835112 274687304962057 .leaf .leaf) .leaf))))

private def tab20 : Table := (.node (195/256) 230438042820573 230438042920634 tab18 tab19)

private def tab21 : Table := (.node (373/512) 215382432024178 215382434673268 tab17 tab20)

private def tab22 : Table := (.node (889/1024) 295717474780028 295717479936866 (.node (883/1024) 291046689369961 291046691322222 (.node (219/256) 285823659882385 285823660530495 (.node (109/128) 282940073691288 282940074057854 (.node (3481/4096) 281700299075032 281700299368282 .leaf .leaf) (.node (437/512) 284373057586992 284373058070160 .leaf .leaf)) (.node (55/64) 288779677110620 288779678316883 (.node (439/512) 287292364932627 287292365813049 .leaf .leaf) (.node (441/512) 290286121927009 290286123588483 .leaf .leaf))) (.node (443/512) 293358624488949 293358627662429 (.node (885/1024) 292582867687955 292582870386565 (.node (221/256) 291812247229591 291812249524591 .leaf .leaf) (.node (14161/16384) 292631201235561 292631203961646 .leaf .leaf)) (.node (111/128) 294925850177861 294925854565232 (.node (887/1024) 294139592983742 294139596715449 .leaf .leaf) .leaf))) (.node (897/1024) 302253748494346 302253748644347 (.node (893/1024) 298939283944799 298939293746914 (.node (891/1024) 297317149865068 297317156981403 (.node (445/512) 296514547252792 296514553311922 .leaf .leaf) (.node (223/256) 298125366746652 298125375100738 .leaf .leaf)) (.node (895/1024) 300584573421870 300584586894188 (.node (447/512) 299758989482976 299759000977861 .leaf .leaf) (.node (7/8) 301416127922767 301416143703404 .leaf .leaf))) (.node (113/128) 308295314926572 308295315076573 (.node (225/256) 304803973959867 304803974109868 (.node (449/512) 303097529543110 303097529693111 .leaf .leaf) (.node (451/512) 306536282200619 306536282350620 .leaf .leaf)) (.node (227/256) 311897216297471 311897216447472 (.node (453/512) 310081976169433 310081976319434 .leaf .leaf) .leaf))))

private def tab23 : Table := (.node (15625/16384) 404852970696783 404852970896862 (.node (59/64) 350932371566315 350932371775535 (.node (231/256) 327580156060130 327580156210136 (.node (229/256) 319464783591387 319464783741388 (.node (14641/16384) 318551184294526 318551184444527 .leaf .leaf) (.node (115/128) 323448748944610 323448749094612 .leaf .leaf)) (.node (3721/4096) 334359909779539 334359909929679 (.node (29/32) 331871098387986 331871098538030 .leaf .leaf) (.node (117/128) 340987958190887 340987958343027 .leaf .leaf))) (.node (961/1024) 375692435055898 375692435255899 (.node (119/128) 361879521020246 361879522276509 (.node (15129/16384) 352985294300880 352985294558597 .leaf .leaf) (.node (15/16) 374066652821957 374066668652595 .leaf .leaf)) (.node (61/64) 403645825044108 403645825244152 (.node (121/128) 387826381626280 387826381826281 .leaf .leaf) .leaf))) (.node (65025/65536) 585007650381208 585007650731209 (.node (125/128) 474160658300658 474160658550702 (.node (31/32) 444994553920800 444994569801437 (.node (123/128) 422280170066762 422280170325983 .leaf .leaf) (.node (3969/4096) 445791339087511 445791339337512 .leaf .leaf)) (.node (16129/16384) 515497430872024 515497431172025 (.node (63/64) 515102956074877 515102972005515 .leaf .leaf) (.node (127/128) 584811378960630 584811394941267 .leaf .leaf))) (.node (1046529/1048576) 723783630175241 723783630625242 (.node (261121/262144) 654420072126543 654420072526544 (.node (255/256) 654322175924577 654322191955215 .leaf .leaf) (.node (511/512) 723734741375152 723734757455790 .leaf .leaf)) (.node (4190209/4194304) 793122765244574 793122765744575 (.node (1023/1024) 793098335268263 793098351398901 .leaf .leaf) .leaf))))

private def tab24 : Table := (.node (57/64) 315617485994337 315617486144338 tab22 tab23)

private def tab25 : Table := (.node (274876858369/274877906944) 1347664829172553 1347664830072554 (.node (32767/32768) 1139719243551172 1139719259931810 (.node (8191/8192) 1001085229621608 1001085245902246 (.node (4095/4096) 931764407330819 931764423561457 (.node (16769025/16777216) 862449691050457 862449691600458 .leaf .leaf) (.node (67092481/67108864) 931770512782294 931770513382295 .leaf .leaf)) (.node (16383/16384) 1070402999595698 1070403015926336 (.node (268402689/268435456) 1001088282616666 1001088283266667 .leaf .leaf) (.node (1073676289/1073741824) 1070404526537213 1070404527237214 .leaf .leaf))) (.node (131071/131072) 1278349824034904 1278349840515542 (.node (65535/65536) 1209034724532267 1209034740962905 (.node (4294836225/4294967296) 1139720007509576 1139720008259577 .leaf .leaf) (.node (17179607041/17179869184) 1209035107010030 1209035107810031 .leaf .leaf)) (.node (262143/262144) 1347664732800495 1347664749331133 (.node (68718952449/68719476736) 1278350015775076 1278350016625077 .leaf .leaf) .leaf))) (.node (70368727400449/70368744177664) 1624923790699535 1624923791799536 (.node (4398042316801/4398046511104) 1486294336758141 1486294337758142 (.node (1099509530625/1099511627776) 1416979594886280 1416979595836281 (.node (524287/524288) 1416979546198108 1416979562778746 .leaf .leaf) (.node (1048575/1048576) 1486294311911870 1486294328542508 .leaf .leaf)) (.node (17592177655809/17592186044416) 1555609066709070 1555609067759071 (.node (2097151/2097152) 1555609053783739 1555609070464377 .leaf .leaf) (.node (4194303/4194304) 1624923783734671 1624923800465309 .leaf .leaf))) (.node (1125899839733761/1125899906842624) 1763553231229883 1763553232429884 (.node (281474943156225/281474976710656) 1694238511709767 1694238512859768 (.node (8388607/8388608) 1694238507725136 1694238524505774 .leaf .leaf) (.node (16777215/16777216) 1763553228735368 1763553245566006 .leaf .leaf)) (.node (4503599493152769/4503599627370496) 1832867950004941 1832867951254942 (.node (33554431/33554432) 1832867948255485 1832867965136122 .leaf .leaf) .leaf))))

private def tab26 : Table := (.node (295147905144993087489/295147905179352825856) 2387385694987089 2387385696637090 (.node (1073741823/1073741824) 2179441539849035 2179441556979672 (.node (268435455/268435456) 2040812103649336 2040812120679974 (.node (134217727/134217728) 1971497385433072 1971497402413710 (.node (18014398241046529/18014398509481984) 1902182668407470 1902182669707471 .leaf .leaf) (.node (72057593501057025/72057594037927936) 1971497386623735 1971497387973736 .leaf .leaf)) (.node (536870911/536870912) 2110126821772468 2110126838853106 (.node (288230375077969921/288230376151711744) 2040812104746867 2040812106146868 .leaf .leaf) (.node (1152921502459363329/1152921504606846976) 2110126822823433 2110126824273434 .leaf .leaf))) (.node (4294967295/4294967296) 2318070975943959 2318070993174597 (.node (2147483647/2147483648) 2248756257902318 2248756275082956 (.node (4611686014132420609/4611686018427387904) 2179441540876716 2179441542376717 .leaf .leaf) (.node (18446744065119617025/18446744073709551616) 2248756258918358 2248756260468359 .leaf .leaf)) (.node (8589934591/8589934592) 2387385693979780 2387385711260418 (.node (73786976277658337281/73786976294838206464) 2318070976954179 2318070978554180 .leaf .leaf) .leaf))) (.node (137438953471/137438953472) 2664644566105237 2664644583585875 (.node (4722366482732206260225/4722366482869645213696) 2526015131049272 2526015132799273 (.node (1180591620648691826689/1180591620717411303424) 2456700413018544 2456700414718545 (.node (17179869183/17179869184) 2456700412012690 2456700429343328 .leaf .leaf) (.node (34359738367/34359738368) 2526015130044146 2526015147424783 .leaf .leaf)) (.node (18889465931203702947841/18889465931478580854784) 2595329849079636 2595329850879637 (.node (68719476735/68719476736) 2595329848074873 2595329865505511 .leaf .leaf) .leaf)) (.node (549755813887/549755813888) 2803274002165510 2803274019746148 (.node (274877906943/274877906944) 2733959284135419 2733959301666057 (.node (75557863725364567605249/75557863725914323419136) 2664644567109818 2664644568959819 .leaf .leaf) (.node (302231454902557782048769/302231454903657293676544) 2733959285139909 2733959287039910 .leaf .leaf)) (.node (1099511627775/1099511627776) 2872588720195555 2872588737826193 (.node (1208925819612430151450625/1208925819614629174706176) 2803274003169954 2803274005119955 .leaf .leaf) .leaf))))

private def tab27 : Table := (.node (67108863/67108864) 1902182667030543 1902182683961181 tab25 tab26)

private def tab28 : Table := (.node (2047/2048) 862437479288487 862437495469125 tab24 tab27)

private def tab29 : Table := (.node (217/256) 280125117553531 280125117780572 tab21 tab28)

private def tab30 : Table := (.node (1367/2048) 191251500466765 191251500537333 tab14 tab29)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem table_checked : verified tab30 = true := by decide +kernel

def entropyBounds (q : ℚ) := get tab30 q

theorem entropyBounds_spec {q : ℚ} (hq : 0 ≤ q) (h1 : q ≤ 1) :
    ((entropyBounds q).1 : ℝ) ≤ Real.binEntropy q ∧ Real.binEntropy q ≤ ((entropyBounds q).2 : ℝ) :=
  get_spec table_checked hq h1

end C6Fast
end

section
namespace C6Cell
open Real Set C6Interval

structure Row where
  l : ℚ
  u : ℚ
  A : ℚ
  B : ℚ
  D : ℚ
  L : ℚ
  deriving DecidableEq, Repr

def pval (d : Row) (q : ℚ) : ℚ :=
  let f := (6*q+3*q^2+2*q^3)/11
  (1-0.0356)*0.61766*(121/174)*q*(f-d.l)*(f-d.u) -
    d.A*(q-0.61766) - d.B*q*(f-d.l) - d.D*q*(d.u-f)

noncomputable def curve (d : Row) (mode : ℕ) (x : ℝ) : ℝ :=
  (1-0.0356)*0.61766*(binEntropy (x^2)/x) - 1.000000001*binEntropy x +
  C6Poly.P d.l d.u d.A d.B d.D x +
    (if mode = 0 then 0 else if mode = 1 then 2*0.0356*binEntropy x
     else 0.0356*binEntropy (max (1/2) (2*x-1))) -
    (if mode = 0 then (d.L : ℝ) else if mode = 1 then -d.L else 0)

def point (d : Row) (mode : ℕ) (q : ℚ) : ℚ :=
  let s := C6Fast.entropyBounds (q^2)
  let h := C6Fast.entropyBounds q
  (1-0.0356)*0.61766*(s.1/q) - 1.000000001*h.2 + pval d q +
  (if mode = 0 then 0 else if mode = 1 then 2*0.0356*h.1
   else 0.0356*(C6Fast.entropyBounds (max (1/2) (2*q-1))).1) -
  (if mode = 0 then d.L else if mode = 1 then -d.L else 0)

theorem pval_spec (d : Row) (q : ℚ) :
    (pval d q : ℝ) = C6Poly.P d.l d.u d.A d.B d.D q := by
  simp [pval, C6Poly.P, C6Projected.moment]
  <;> ring

theorem point_spec (d : Row) (mode : ℕ) (q : ℚ) (hq : 0 ≤ q) (h1 : q ≤ 1) :
    (point d mode q : ℝ) ≤ curve d mode q := by
  have hs := (C6Fast.entropyBounds_spec (q := q^2) (sq_nonneg _) (pow_le_one₀ hq h1)).1
  have hx := C6Fast.entropyBounds_spec hq h1
  have hc := (C6Fast.entropyBounds_spec (q := max (1/2) (2*q-1))
     (le_max_of_le_left (by norm_num)) (max_le (by norm_num) (by linarith))).1
  push_cast at hs hc
  have hrs := div_le_div_of_nonneg_right hs (show (0:ℝ) ≤ q by exact_mod_cast hq)
  unfold point curve
  split_ifs <;> push_cast <;> rw [pval_spec] <;> linarith only [hx.1,hx.2,hc,hrs]

end C6Cell
end

section
namespace C6Cell

open Real Set C6Interval

def threshold (d : Row) (mode : ℕ) : ℚ :=
  if mode=0 then d.L else if mode=1 then -d.L else 0

private noncomputable def bonus (mode : ℕ) (x : ℝ) :=
  if mode = 0 then 0 else if mode = 1 then 2*0.0356*binEntropy x
  else 0.0356*binEntropy (max (1/2) (2*x-1))

private lemma curve_form (d : Row) (mode : ℕ) (x : ℝ) :
    curve d mode x =
    (1-0.0356)*0.61766*(binEntropy (x^2)/x) - 1.000000001*binEntropy x +
      C6Poly.P d.l d.u d.A d.B d.D x + bonus mode x - (threshold d mode : ℝ) := by
  simp only [curve, threshold, bonus]
  split_ifs <;> push_cast <;> rfl

private lemma bonus_nonnegative (mode : ℕ) (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
    0 ≤ bonus mode x := by
  unfold bonus
  have hh := binEntropy_nonneg hx.1 hx.2
  have hc := binEntropy_nonneg (le_max_of_le_left (by norm_num) : 0 ≤ max (1/2 : ℝ) (2*x-1))
    (max_le (by norm_num) (by linarith [hx.2]) : max (1/2 : ℝ) (2*x-1) ≤ 1)
  split_ifs <;> positivity

private lemma bonus_chord (mode : ℕ) {a b r s : ℝ} (ha : a ∈ Set.Icc 0 1)
    (hb : b ∈ Set.Icc 0 1) (hr : 0 ≤ r) (hs : 0 ≤ s) (hrs : r+s=1) :
    r*bonus mode a + s*bonus mode b ≤ bonus mode (r*a+s*b) := by
  have h₁ := strictConcave_binEntropy.concaveOn.2 ha hb hr hs hrs
  have h₂ := clampedEntropy_concave.2 ha hb hr hs hrs
  simp only [smul_eq_mul] at h₁ h₂
  unfold bonus
  split_ifs <;> linarith only [h₁,h₂]

/-- Extend rational point checks to their entire interval using chord bounds. -/
theorem box (d : Row) (mode : ℕ) (a b : ℚ) (hP : C6Poly.Params d.l d.u d.A d.B d.D)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1)
    (hcheck : (10 + 1.000000001/(8*a*(1-b)))*(b-a)^2 ≤ min (point d mode a) (point d mode b))
    {x : ℝ} (hx : x ∈ Set.Icc (a:ℝ) b) : 0 ≤ curve d mode x := by
  have ha' : (0:ℝ) < a := by exact_mod_cast ha
  have hb' : (b:ℝ) < 1 := by exact_mod_cast hb
  have hab' : (a:ℝ) ≤ b := by exact_mod_cast hab
  have hA : (a:ℝ) ∈ Set.Icc 0 1 := ⟨ha'.le, hab'.trans hb'.le⟩
  have hB : (b:ℝ) ∈ Set.Icc 0 1 := ⟨ha'.le.trans hab', hb'.le⟩
  obtain ⟨r,s,hr,hs,hrs,hx'⟩ := (Convex.mem_Icc hab').mp hx
  let E := (10 + 1.000000001/(8*(a:ℝ)*(1-b)))*((b:ℝ)-a)^2
  have ec (q : ℚ) (h : min (point d mode a) (point d mode b) ≤ point d mode q) : E ≤ (point d mode q : ℝ) := by
    dsimp [E]; simpa using (Rat.cast_le (K := ℝ)).mpr (hcheck.trans h)
  have hpa := (ec a (min_le_left ..)).trans (point_spec d mode a ha.le (hab.trans hb.le))
  have hpb := (ec b (min_le_right ..)).trans (point_spec d mode b (ha.le.trans hab) hb.le)
  have hlow : E ≤ r*(curve d mode a) + s*(curve d mode b) := by
    linarith only [mul_le_mul_of_nonneg_left hpa hr, mul_le_mul_of_nonneg_left hpb hs,
      congrArg (E * ·) hrs]
  have hBns := bonus_chord mode hA hB hr hs hrs
  have hS := squareDiv_concave.2 hA hB hr hs hrs
  simp only [smul_eq_mul] at hS
  have hE := entropy_chord_upper ha' hb' hab' hr hs hrs
  have hPol := C6Poly.chord hP hA hB (show s ∈ Set.Icc 0 1 from ⟨hs,by linarith⟩)
  rw [show 1-s=r by linarith] at hPol
  rw [← hx']
  simp only [curve_form] at hlow ⊢
  dsimp [E] at hlow
  have heq : 1.000000001 / (8*(a:ℝ)*(1-b)) * ((b:ℝ)-a)^2 =
      1.000000001 * (((b:ℝ)-a)^2 / (8*(a:ℝ)*(1-b))) := by ring
  rw [add_mul, heq] at hlow
  linarith only [hlow, hBns, hS, hE, hPol, congrArg ((threshold d mode : ℝ) * ·) hrs]

theorem edge (d : Row) (mode : ℕ) (q : ℚ) (hP : C6Poly.Params d.l d.u d.A d.B d.D)
    (hq : q=0 ∨ q=1) (hcheck : 3*(1/2^40) ≤ pval d q - threshold d mode)
    {x : ℝ} (hx : x ∈ Set.Icc 0 1) (hclose : |x-(q:ℝ)| ≤ 1/2^40) : 0 ≤ curve d mode x := by
  have hq' : (q:ℝ) ∈ Set.Icc 0 1 := by rcases hq with rfl|rfl <;> norm_num
  have hmin : min x (1-x) ≤ 1/2^40 := by
    rcases hq with rfl|rfl
    · simpa [abs_of_nonneg hx.1] using (min_le_left x (1-x)).trans (by simpa [abs_of_nonneg hx.1] using hclose)
    · apply (min_le_right x (1-x)).trans
      simpa [abs_of_nonpos (sub_nonpos.mpr hx.2)] using hclose
  have hbase := C6Endpoint.base x hx.1 hx.2 hmin
  have hlip := (abs_le.mp (C6Poly.lipschitz hP hx hq')).1
  have hchk : (3:ℝ)*(1/2^40) ≤ C6Poly.P d.l d.u d.A d.B d.D q - (threshold d mode : ℝ) := by
    rw [← pval_spec]; simpa using (Rat.cast_le (K := ℝ)).mpr hcheck
  rw [curve_form]
  have hm := le_min hx.1 (sub_nonneg.mpr hx.2)
  linarith only [hclose, hbase, hlip, hchk, hm, bonus_nonnegative mode x hx]

theorem finalEdge (mode : ℕ) {x : ℝ} (hx : x ∈ Set.Icc 0 1) (h : min x (1-x) ≤ 1/2^40) :
    0 ≤ curve ⟨0.935,1,0,0,0,0⟩ mode x := by
  have hb := C6Endpoint.last_slice x hx.1 hx.2 h
  rw [curve_form]
  norm_num [C6Poly.P, C6Projected.moment, threshold] <;>
    linarith only [hb, bonus_nonnegative mode x hx]

end C6Cell
end

section
namespace C6Cell
open Set Real

def gridCheck (d : Row) (mode : ℕ) (last : ℚ) (lo : ℚ) : List ℚ → Bool
  | [] => decide (lo = last)
  | mid :: xs =>
    decide (0 < lo ∧ lo ≤ mid ∧ mid < 1 ∧
      (10 + 1.000000001/(8*lo*(1-mid))) * (mid-lo)^2 ≤
        min (point d mode lo) (point d mode mid)) &&
    gridCheck d mode last mid xs

theorem grid_spec (d : Row) (mode : ℕ) (a b : ℚ) (xs : List ℚ)
    (hP : C6Poly.Params d.l d.u d.A d.B d.D)
    (h : gridCheck d mode b a xs = true)
    (hpt : 0 ≤ curve d mode a) {x : ℝ} (hx : x ∈ Icc (a:ℝ) b) : 0 ≤ curve d mode x := by
  induction xs generalizing a with
  | nil =>
    have hab : a = b := by simpa [gridCheck] using h
    subst b
    rw [le_antisymm hx.2 hx.1]
    exact hpt
  | cons mid xs ih =>
    simp only [gridCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    have hb (z : ℝ) := box d mode a mid hP h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2 (x := z)
    by_cases e : x ≤ mid
    · exact hb _ ⟨hx.1,e⟩
    · exact ih mid h.2 (hb _ ⟨by exact_mod_cast h.1.2.1, le_rfl⟩) ⟨(le_of_not_ge e), hx.2⟩

theorem grid_cover (d : Row) (mode : ℕ) (a b start stop : ℚ) (xs : List ℚ)
    (hP : C6Poly.Params d.l d.u d.A d.B d.D)
    (hgrid : gridCheck d mode stop start xs = true)
    (ha : a ≤ start) (hb : stop ≤ b)
    (hL : ∀ x ∈ Icc (a:ℝ) start, 0 ≤ curve d mode x)
    (hR : ∀ x ∈ Icc (stop:ℝ) b, 0 ≤ curve d mode x) :
    ∀ x ∈ Icc (a:ℝ) b, 0 ≤ curve d mode x := by
  intro x hx
  by_cases hl : x ≤ start
  · exact hL _ ⟨hx.1,hl⟩
  by_cases hr : stop ≤ x
  · exact hR _ ⟨hr,hx.2⟩
  have hpt := hL start ⟨by exact_mod_cast ha,le_rfl⟩
  exact grid_spec d mode start stop xs hP hgrid hpt ⟨le_of_not_ge hl,le_of_not_ge hr⟩

theorem edgeL (d : Row) (mode : ℕ) (hP : C6Poly.Params d.l d.u d.A d.B d.D)
    (h : 3*(1/2^40) ≤ pval d 0 - threshold d mode) :
    ∀ x ∈ Icc (0:ℝ) (1/2^40), 0 ≤ curve d mode x := by
  intro x hx
  exact edge d mode 0 hP (Or.inl rfl) h ⟨hx.1,by norm_num at hx ⊢; linarith [hx.2]⟩
    (by simpa [abs_of_nonneg hx.1] using hx.2)

theorem edgeR (d : Row) (mode : ℕ) (hP : C6Poly.Params d.l d.u d.A d.B d.D)
    (h : 3*(1/2^40) ≤ pval d 1 - threshold d mode) :
    ∀ x ∈ Icc (1-1/2^40:ℝ) 1, 0 ≤ curve d mode x := by
  intro x hx
  exact edge d mode 1 hP (Or.inr rfl) h ⟨by norm_num at hx ⊢; linarith [hx.1], hx.2⟩
    (by norm_cast; rw [abs_of_nonpos (by linarith [hx.2])]; linarith [hx.1])

theorem edgeMid (d : Row) (mode : ℕ)
    (h : 0 ≤ point d mode (1/2)) :
    ∀ x ∈ Icc (1/2:ℝ) (1/2), 0 ≤ curve d mode x := by
  intro x hx
  rw [le_antisymm hx.2 hx.1]
  have h' := point_spec d mode (1/2) (by norm_num) (by norm_num)
  push_cast at h'
  exact (show (0:ℝ) ≤ ((point d mode (1/2):ℚ):ℝ) by exact_mod_cast h).trans h'

end C6Cell
end

section
namespace C6Cell
open Real Set

set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private def row0 : Row := ⟨0,(12/25),(138349133/1000000000),0,0,(-616901/25000000)⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem params0 : C6Poly.Params row0.l row0.u row0.A row0.B row0.D := by norm_num [C6Poly.Params,row0]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private def row1 : Row := ⟨(12/25),(41/80),(40202393/1000000000),0,(2693861/1000000000),(-616901/25000000)⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem params1 : C6Poly.Params row1.l row1.u row1.A row1.B row1.D := by norm_num [C6Poly.Params,row1]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private def row2 : Row := ⟨(41/80),(423/800),(40011313/1000000000),0,(22453/25000000),(-616901/25000000)⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem params2 : C6Poly.Params row2.l row2.u row2.A row2.B row2.D := by norm_num [C6Poly.Params,row2]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private def row3 : Row := ⟨(423/800),(859/1600),(19984583/500000000),0,0,(-616901/25000000)⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem params3 : C6Poly.Params row3.l row3.u row3.A row3.B row3.D := by norm_num [C6Poly.Params,row3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private def row4 : Row := ⟨(859/1600),(109/200),(39953359/1000000000),0,0,(-616901/25000000)⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem params4 : C6Poly.Params row4.l row4.u row4.A row4.B row4.D := by norm_num [C6Poly.Params,row4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private def row5 : Row := ⟨(109/200),(177/320),(998943/25000000),0,0,(-616901/25000000)⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem params5 : C6Poly.Params row5.l row5.u row5.A row5.B row5.D := by norm_num [C6Poly.Params,row5]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private def row6 : Row := ⟨(177/320),(449/800),(1249449/31250000),(1461301/1000000000),0,(-616901/25000000)⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem params6 : C6Poly.Params row6.l row6.u row6.A row6.B row6.D := by norm_num [C6Poly.Params,row6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private def row7 : Row := ⟨(449/800),(231/400),(800683/20000000),(54143/31250000),0,(-616901/25000000)⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem params7 : C6Poly.Params row7.l row7.u row7.A row7.B row7.D := by norm_num [C6Poly.Params,row7]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private def row8 : Row := ⟨(231/400),(61/100),(10055061/250000000),(48307/40000000),0,(-616901/25000000)⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem params8 : C6Poly.Params row8.l row8.u row8.A row8.B row8.D := by norm_num [C6Poly.Params,row8]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private def row9 : Row := ⟨(61/100),(37/50),(40524187/1000000000),0,0,(-616901/25000000)⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem params9 : C6Poly.Params row9.l row9.u row9.A row9.B row9.D := by norm_num [C6Poly.Params,row9]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private def row10 : Row := ⟨(37/50),(87/100),(4070009/125000000),0,0,(-9555527/500000000)⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem params10 : C6Poly.Params row10.l row10.u row10.A row10.B row10.D := by norm_num [C6Poly.Params,row10]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private def row11 : Row := ⟨(87/100),(187/200),(4553879/500000000),0,0,(-350469/62500000)⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem params11 : C6Poly.Params row11.l row11.u row11.A row11.B row11.D := by norm_num [C6Poly.Params,row11]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private def row12 : Row := ⟨0.935,1,0,0,0,0⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem params12 : C6Poly.Params row12.l row12.u row12.A row12.B row12.D := by norm_num [C6Poly.Params,row12]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private def grid0_0 : List ℚ := [(1/549755813888),(1/274877906944),(1/137438953472),(1/68719476736),(1/34359738368),(1/17179869184),(1/8589934592),(1/4294967296),(1/2147483648),(1/1073741824),(1/536870912),(1/268435456),(1/134217728),(1/67108864),(1/33554432),(1/16777216),(1/8388608),(1/4194304),(1/2097152),(1/1048576),(1/524288),(1/262144),(1/131072),(1/65536),(1/32768),(1/16384),(1/8192),(1/4096),(1/2048),(1/1024),(1/512),(1/256),(1/128),(1/64),(1/32),(1/16),(1/8),(3/16),(1/4),(5/16),(11/32),(3/8),(13/32),(7/16),(15/32),(31/64),(1/2),(33/64),(17/32),(35/64),(71/128),(9/16),(73/128),(37/64),(75/128),(19/32),(77/128),(39/64),(79/128),(5/8),(81/128),(41/64),(83/128),(21/32),(43/64),(11/16),(45/64),(23/32),(3/4),(25/32),(13/16),(27/32),(7/8),(15/16),(31/32),(63/64),(127/128),(255/256),(511/512),(1023/1024),(2047/2048),(4095/4096),(8191/8192),(16383/16384),(32767/32768),(65535/65536),(131071/131072),(262143/262144),(524287/524288),(1048575/1048576),(2097151/2097152),(4194303/4194304),(8388607/8388608),(16777215/16777216),(33554431/33554432),(67108863/67108864),(134217727/134217728),(268435455/268435456),(536870911/536870912),(1073741823/1073741824),(2147483647/2147483648),(4294967295/4294967296),(8589934591/8589934592),(17179869183/17179869184),(34359738367/34359738368),(68719476735/68719476736),(137438953471/137438953472),(274877906943/274877906944),(549755813887/549755813888),(1099511627775/1099511627776)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem check0_0 : gridCheck row0 0 (1099511627775/1099511627776) (1/1099511627776) grid0_0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem good0_0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ curve row0 0 x := by
  have cc := grid_cover row0 0 0 1 (1/1099511627776) (1099511627775/1099511627776) grid0_0 params0 check0_0 (by norm_num) (by norm_num)
  norm_num at cc ⊢
  apply cc
  · have ee := edgeL row0 0 params0 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
  · have ee := edgeR row0 0 params0 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private def grid0_1 : List ℚ := [(1/549755813888),(1/274877906944),(1/137438953472),(1/68719476736),(1/34359738368),(1/17179869184),(1/8589934592),(1/4294967296),(1/2147483648),(1/1073741824),(1/536870912),(1/268435456),(1/134217728),(1/67108864),(1/33554432),(1/16777216),(1/8388608),(1/4194304),(1/2097152),(1/1048576),(1/524288),(1/262144),(1/131072),(1/65536),(1/32768),(1/16384),(1/8192),(1/4096),(1/2048),(1/1024),(1/512),(1/256),(1/128),(1/64),(1/32),(1/16),(1/8),(3/16),(1/4),(5/16),(11/32),(3/8),(13/32),(7/16),(15/32),(31/64),(1/2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem check0_1 : gridCheck row0 1 (1/2) (1/1099511627776) grid0_1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem good0_1 : ∀ x ∈ Icc (0:ℝ) (1/2), 0 ≤ curve row0 1 x := by
  have cc := grid_cover row0 1 0 (1/2) (1/1099511627776) (1/2) grid0_1 params0 check0_1 (by norm_num) (by norm_num)
  norm_num at cc ⊢
  apply cc
  · have ee := edgeL row0 1 params0 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
  · have ee := edgeMid row0 1 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private def grid0_2 : List ℚ := [(33/64),(17/32),(35/64),(71/128),(9/16),(73/128),(37/64),(75/128),(19/32),(77/128),(39/64),(79/128),(5/8),(81/128),(41/64),(83/128),(21/32),(43/64),(11/16),(45/64),(23/32),(3/4),(25/32),(13/16),(27/32),(7/8),(15/16),(31/32),(63/64),(127/128),(255/256),(511/512),(1023/1024),(2047/2048),(4095/4096),(8191/8192),(16383/16384),(32767/32768),(65535/65536),(131071/131072),(262143/262144),(524287/524288),(1048575/1048576),(2097151/2097152),(4194303/4194304),(8388607/8388608),(16777215/16777216),(33554431/33554432),(67108863/67108864),(134217727/134217728),(268435455/268435456),(536870911/536870912),(1073741823/1073741824),(2147483647/2147483648),(4294967295/4294967296),(8589934591/8589934592),(17179869183/17179869184),(34359738367/34359738368),(68719476735/68719476736),(137438953471/137438953472),(274877906943/274877906944),(549755813887/549755813888),(1099511627775/1099511627776)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem check0_2 : gridCheck row0 2 (1099511627775/1099511627776) (1/2) grid0_2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem good0_2 : ∀ x ∈ Icc ((1/2):ℝ) 1, 0 ≤ curve row0 2 x := by
  have cc := grid_cover row0 2 (1/2) 1 (1/2) (1099511627775/1099511627776) grid0_2 params0 check0_2 (by norm_num) (by norm_num)
  norm_num at cc ⊢
  apply cc
  · have ee := edgeMid row0 2 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
  · have ee := edgeR row0 2 params0 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private def grid1_0 : List ℚ := [(1/549755813888),(1/274877906944),(1/137438953472),(1/68719476736),(1/34359738368),(1/17179869184),(1/8589934592),(1/4294967296),(1/2147483648),(1/1073741824),(1/536870912),(1/268435456),(1/134217728),(1/67108864),(1/33554432),(1/16777216),(1/8388608),(1/4194304),(1/2097152),(1/1048576),(1/524288),(1/262144),(1/131072),(1/65536),(1/32768),(1/16384),(1/8192),(1/4096),(1/2048),(1/1024),(1/512),(1/256),(1/128),(1/64),(1/32),(1/16),(1/8),(3/16),(1/4),(9/32),(5/16),(11/32),(3/8),(13/32),(7/16),(15/32),(31/64),(1/2),(33/64),(17/32),(35/64),(9/16),(73/128),(37/64),(75/128),(19/32),(77/128),(39/64),(157/256),(79/128),(159/256),(5/8),(161/256),(81/128),(163/256),(327/512),(41/64),(329/512),(165/256),(331/512),(83/128),(167/256),(21/32),(169/256),(85/128),(171/256),(43/64),(173/256),(87/128),(11/16),(89/128),(45/64),(91/128),(23/32),(47/64),(3/4),(49/64),(25/32),(13/16),(27/32),(7/8),(29/32),(15/16),(31/32),(63/64),(127/128),(255/256),(511/512),(1023/1024),(2047/2048),(4095/4096),(8191/8192),(16383/16384),(32767/32768),(65535/65536),(131071/131072),(262143/262144),(524287/524288),(1048575/1048576),(2097151/2097152),(4194303/4194304),(8388607/8388608),(16777215/16777216),(33554431/33554432),(67108863/67108864),(134217727/134217728),(268435455/268435456),(536870911/536870912),(1073741823/1073741824),(2147483647/2147483648),(4294967295/4294967296),(8589934591/8589934592),(17179869183/17179869184),(34359738367/34359738368),(68719476735/68719476736),(137438953471/137438953472),(274877906943/274877906944),(549755813887/549755813888),(1099511627775/1099511627776)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem check1_0 : gridCheck row1 0 (1099511627775/1099511627776) (1/1099511627776) grid1_0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem good1_0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ curve row1 0 x := by
  have cc := grid_cover row1 0 0 1 (1/1099511627776) (1099511627775/1099511627776) grid1_0 params1 check1_0 (by norm_num) (by norm_num)
  norm_num at cc ⊢
  apply cc
  · have ee := edgeL row1 0 params1 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
  · have ee := edgeR row1 0 params1 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private def grid1_1 : List ℚ := [(1/549755813888),(1/274877906944),(1/137438953472),(1/68719476736),(1/34359738368),(1/17179869184),(1/8589934592),(1/4294967296),(1/2147483648),(1/1073741824),(1/536870912),(1/268435456),(1/134217728),(1/67108864),(1/33554432),(1/16777216),(1/8388608),(1/4194304),(1/2097152),(1/1048576),(1/524288),(1/262144),(1/131072),(1/65536),(1/32768),(1/16384),(1/8192),(1/4096),(1/2048),(1/1024),(1/512),(1/256),(1/128),(1/64),(1/32),(1/16),(3/32),(1/8),(5/32),(3/16),(7/32),(1/4),(9/32),(5/16),(11/32),(3/8),(13/32),(7/16),(15/32),(31/64),(1/2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem check1_1 : gridCheck row1 1 (1/2) (1/1099511627776) grid1_1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem good1_1 : ∀ x ∈ Icc (0:ℝ) (1/2), 0 ≤ curve row1 1 x := by
  have cc := grid_cover row1 1 0 (1/2) (1/1099511627776) (1/2) grid1_1 params1 check1_1 (by norm_num) (by norm_num)
  norm_num at cc ⊢
  apply cc
  · have ee := edgeL row1 1 params1 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
  · have ee := edgeMid row1 1 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private def grid1_2 : List ℚ := [(33/64),(17/32),(35/64),(9/16),(73/128),(37/64),(75/128),(19/32),(77/128),(39/64),(157/256),(79/128),(159/256),(5/8),(161/256),(81/128),(163/256),(327/512),(41/64),(329/512),(165/256),(331/512),(83/128),(167/256),(21/32),(169/256),(85/128),(171/256),(43/64),(173/256),(87/128),(11/16),(89/128),(45/64),(91/128),(23/32),(47/64),(3/4),(49/64),(25/32),(13/16),(27/32),(7/8),(29/32),(15/16),(31/32),(63/64),(127/128),(255/256),(511/512),(1023/1024),(2047/2048),(4095/4096),(8191/8192),(16383/16384),(32767/32768),(65535/65536),(131071/131072),(262143/262144),(524287/524288),(1048575/1048576),(2097151/2097152),(4194303/4194304),(8388607/8388608),(16777215/16777216),(33554431/33554432),(67108863/67108864),(134217727/134217728),(268435455/268435456),(536870911/536870912),(1073741823/1073741824),(2147483647/2147483648),(4294967295/4294967296),(8589934591/8589934592),(17179869183/17179869184),(34359738367/34359738368),(68719476735/68719476736),(137438953471/137438953472),(274877906943/274877906944),(549755813887/549755813888),(1099511627775/1099511627776)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem check1_2 : gridCheck row1 2 (1099511627775/1099511627776) (1/2) grid1_2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem good1_2 : ∀ x ∈ Icc ((1/2):ℝ) 1, 0 ≤ curve row1 2 x := by
  have cc := grid_cover row1 2 (1/2) 1 (1/2) (1099511627775/1099511627776) grid1_2 params1 check1_2 (by norm_num) (by norm_num)
  norm_num at cc ⊢
  apply cc
  · have ee := edgeMid row1 2 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
  · have ee := edgeR row1 2 params1 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private def grid2_0 : List ℚ := [(1/549755813888),(1/274877906944),(1/137438953472),(1/68719476736),(1/34359738368),(1/17179869184),(1/8589934592),(1/4294967296),(1/2147483648),(1/1073741824),(1/536870912),(1/268435456),(1/134217728),(1/67108864),(1/33554432),(1/16777216),(1/8388608),(1/4194304),(1/2097152),(1/1048576),(1/524288),(1/262144),(1/131072),(1/65536),(1/32768),(1/16384),(1/8192),(1/4096),(1/2048),(1/1024),(1/512),(1/256),(1/128),(1/64),(1/32),(1/16),(1/8),(3/16),(1/4),(9/32),(5/16),(11/32),(3/8),(13/32),(7/16),(15/32),(1/2),(33/64),(17/32),(35/64),(9/16),(37/64),(75/128),(19/32),(77/128),(39/64),(79/128),(159/256),(5/8),(161/256),(81/128),(163/256),(41/64),(329/512),(165/256),(331/512),(83/128),(333/512),(167/256),(335/512),(671/1024),(21/32),(673/1024),(337/512),(675/1024),(169/256),(339/512),(85/128),(341/512),(171/256),(343/512),(43/64),(345/512),(173/256),(87/128),(175/256),(11/16),(177/256),(89/128),(45/64),(91/128),(23/32),(93/128),(47/64),(3/4),(49/64),(25/32),(13/16),(27/32),(7/8),(29/32),(15/16),(31/32),(63/64),(127/128),(255/256),(511/512),(1023/1024),(2047/2048),(4095/4096),(8191/8192),(16383/16384),(32767/32768),(65535/65536),(131071/131072),(262143/262144),(524287/524288),(1048575/1048576),(2097151/2097152),(4194303/4194304),(8388607/8388608),(16777215/16777216),(33554431/33554432),(67108863/67108864),(134217727/134217728),(268435455/268435456),(536870911/536870912),(1073741823/1073741824),(2147483647/2147483648),(4294967295/4294967296),(8589934591/8589934592),(17179869183/17179869184),(34359738367/34359738368),(68719476735/68719476736),(137438953471/137438953472),(274877906943/274877906944),(549755813887/549755813888),(1099511627775/1099511627776)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem check2_0 : gridCheck row2 0 (1099511627775/1099511627776) (1/1099511627776) grid2_0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem good2_0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ curve row2 0 x := by
  have cc := grid_cover row2 0 0 1 (1/1099511627776) (1099511627775/1099511627776) grid2_0 params2 check2_0 (by norm_num) (by norm_num)
  norm_num at cc ⊢
  apply cc
  · have ee := edgeL row2 0 params2 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
  · have ee := edgeR row2 0 params2 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private def grid2_1 : List ℚ := [(1/549755813888),(1/274877906944),(1/137438953472),(1/68719476736),(1/34359738368),(1/17179869184),(1/8589934592),(1/4294967296),(1/2147483648),(1/1073741824),(1/536870912),(1/268435456),(1/134217728),(1/67108864),(1/33554432),(1/16777216),(1/8388608),(1/4194304),(1/2097152),(1/1048576),(1/524288),(1/262144),(1/131072),(1/65536),(1/32768),(1/16384),(1/8192),(1/4096),(1/2048),(1/1024),(1/512),(1/256),(1/128),(1/64),(1/32),(1/16),(3/32),(1/8),(5/32),(3/16),(7/32),(1/4),(9/32),(5/16),(11/32),(3/8),(13/32),(7/16),(15/32),(1/2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem check2_1 : gridCheck row2 1 (1/2) (1/1099511627776) grid2_1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem good2_1 : ∀ x ∈ Icc (0:ℝ) (1/2), 0 ≤ curve row2 1 x := by
  have cc := grid_cover row2 1 0 (1/2) (1/1099511627776) (1/2) grid2_1 params2 check2_1 (by norm_num) (by norm_num)
  norm_num at cc ⊢
  apply cc
  · have ee := edgeL row2 1 params2 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
  · have ee := edgeMid row2 1 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private def grid2_2 : List ℚ := [(33/64),(17/32),(35/64),(9/16),(37/64),(75/128),(19/32),(77/128),(39/64),(79/128),(159/256),(5/8),(161/256),(81/128),(163/256),(41/64),(329/512),(165/256),(331/512),(83/128),(333/512),(167/256),(335/512),(671/1024),(21/32),(673/1024),(337/512),(675/1024),(169/256),(339/512),(85/128),(341/512),(171/256),(343/512),(43/64),(345/512),(173/256),(87/128),(175/256),(11/16),(177/256),(89/128),(45/64),(91/128),(23/32),(93/128),(47/64),(3/4),(49/64),(25/32),(51/64),(13/16),(27/32),(7/8),(29/32),(15/16),(31/32),(63/64),(127/128),(255/256),(511/512),(1023/1024),(2047/2048),(4095/4096),(8191/8192),(16383/16384),(32767/32768),(65535/65536),(131071/131072),(262143/262144),(524287/524288),(1048575/1048576),(2097151/2097152),(4194303/4194304),(8388607/8388608),(16777215/16777216),(33554431/33554432),(67108863/67108864),(134217727/134217728),(268435455/268435456),(536870911/536870912),(1073741823/1073741824),(2147483647/2147483648),(4294967295/4294967296),(8589934591/8589934592),(17179869183/17179869184),(34359738367/34359738368),(68719476735/68719476736),(137438953471/137438953472),(274877906943/274877906944),(549755813887/549755813888),(1099511627775/1099511627776)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem check2_2 : gridCheck row2 2 (1099511627775/1099511627776) (1/2) grid2_2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem good2_2 : ∀ x ∈ Icc ((1/2):ℝ) 1, 0 ≤ curve row2 2 x := by
  have cc := grid_cover row2 2 (1/2) 1 (1/2) (1099511627775/1099511627776) grid2_2 params2 check2_2 (by norm_num) (by norm_num)
  norm_num at cc ⊢
  apply cc
  · have ee := edgeMid row2 2 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
  · have ee := edgeR row2 2 params2 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private def grid3_0 : List ℚ := [(1/549755813888),(1/274877906944),(1/137438953472),(1/68719476736),(1/34359738368),(1/17179869184),(1/8589934592),(1/4294967296),(1/2147483648),(1/1073741824),(1/536870912),(1/268435456),(1/134217728),(1/67108864),(1/33554432),(1/16777216),(1/8388608),(1/4194304),(1/2097152),(1/1048576),(1/524288),(1/262144),(1/131072),(1/65536),(1/32768),(1/16384),(1/8192),(1/4096),(1/2048),(1/1024),(1/512),(1/256),(1/128),(1/64),(1/32),(1/16),(1/8),(3/16),(1/4),(9/32),(5/16),(11/32),(3/8),(13/32),(7/16),(15/32),(1/2),(33/64),(17/32),(35/64),(9/16),(37/64),(19/32),(77/128),(39/64),(79/128),(5/8),(161/256),(81/128),(163/256),(41/64),(165/256),(83/128),(333/512),(167/256),(335/512),(21/32),(673/1024),(337/512),(675/1024),(169/256),(677/1024),(339/512),(679/1024),(85/128),(681/1024),(341/512),(683/1024),(171/256),(685/1024),(343/512),(687/1024),(43/64),(689/1024),(345/512),(173/256),(347/512),(87/128),(349/512),(175/256),(11/16),(177/256),(89/128),(179/256),(45/64),(91/128),(23/32),(93/128),(47/64),(3/4),(49/64),(25/32),(51/64),(13/16),(27/32),(7/8),(29/32),(15/16),(31/32),(63/64),(127/128),(255/256),(511/512),(1023/1024),(2047/2048),(4095/4096),(8191/8192),(16383/16384),(32767/32768),(65535/65536),(131071/131072),(262143/262144),(524287/524288),(1048575/1048576),(2097151/2097152),(4194303/4194304),(8388607/8388608),(16777215/16777216),(33554431/33554432),(67108863/67108864),(134217727/134217728),(268435455/268435456),(536870911/536870912),(1073741823/1073741824),(2147483647/2147483648),(4294967295/4294967296),(8589934591/8589934592),(17179869183/17179869184),(34359738367/34359738368),(68719476735/68719476736),(137438953471/137438953472),(274877906943/274877906944),(549755813887/549755813888),(1099511627775/1099511627776)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem check3_0 : gridCheck row3 0 (1099511627775/1099511627776) (1/1099511627776) grid3_0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem good3_0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ curve row3 0 x := by
  have cc := grid_cover row3 0 0 1 (1/1099511627776) (1099511627775/1099511627776) grid3_0 params3 check3_0 (by norm_num) (by norm_num)
  norm_num at cc ⊢
  apply cc
  · have ee := edgeL row3 0 params3 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
  · have ee := edgeR row3 0 params3 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private def grid3_1 : List ℚ := [(1/549755813888),(1/274877906944),(1/137438953472),(1/68719476736),(1/34359738368),(1/17179869184),(1/8589934592),(1/4294967296),(1/2147483648),(1/1073741824),(1/536870912),(1/268435456),(1/134217728),(1/67108864),(1/33554432),(1/16777216),(1/8388608),(1/4194304),(1/2097152),(1/1048576),(1/524288),(1/262144),(1/131072),(1/65536),(1/32768),(1/16384),(1/8192),(1/4096),(1/2048),(1/1024),(1/512),(1/256),(1/128),(1/64),(1/32),(1/16),(3/32),(1/8),(5/32),(3/16),(7/32),(1/4),(9/32),(5/16),(11/32),(3/8),(13/32),(7/16),(15/32),(1/2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem check3_1 : gridCheck row3 1 (1/2) (1/1099511627776) grid3_1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem good3_1 : ∀ x ∈ Icc (0:ℝ) (1/2), 0 ≤ curve row3 1 x := by
  have cc := grid_cover row3 1 0 (1/2) (1/1099511627776) (1/2) grid3_1 params3 check3_1 (by norm_num) (by norm_num)
  norm_num at cc ⊢
  apply cc
  · have ee := edgeL row3 1 params3 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
  · have ee := edgeMid row3 1 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private def grid3_2 : List ℚ := [(33/64),(17/32),(35/64),(9/16),(37/64),(19/32),(77/128),(39/64),(79/128),(5/8),(161/256),(81/128),(163/256),(41/64),(165/256),(83/128),(333/512),(167/256),(335/512),(21/32),(673/1024),(337/512),(675/1024),(169/256),(677/1024),(339/512),(679/1024),(85/128),(681/1024),(341/512),(683/1024),(171/256),(685/1024),(343/512),(687/1024),(43/64),(689/1024),(345/512),(173/256),(347/512),(87/128),(349/512),(175/256),(11/16),(177/256),(89/128),(179/256),(45/64),(91/128),(23/32),(93/128),(47/64),(3/4),(49/64),(25/32),(51/64),(13/16),(27/32),(7/8),(29/32),(15/16),(31/32),(63/64),(127/128),(255/256),(511/512),(1023/1024),(2047/2048),(4095/4096),(8191/8192),(16383/16384),(32767/32768),(65535/65536),(131071/131072),(262143/262144),(524287/524288),(1048575/1048576),(2097151/2097152),(4194303/4194304),(8388607/8388608),(16777215/16777216),(33554431/33554432),(67108863/67108864),(134217727/134217728),(268435455/268435456),(536870911/536870912),(1073741823/1073741824),(2147483647/2147483648),(4294967295/4294967296),(8589934591/8589934592),(17179869183/17179869184),(34359738367/34359738368),(68719476735/68719476736),(137438953471/137438953472),(274877906943/274877906944),(549755813887/549755813888),(1099511627775/1099511627776)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem check3_2 : gridCheck row3 2 (1099511627775/1099511627776) (1/2) grid3_2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem good3_2 : ∀ x ∈ Icc ((1/2):ℝ) 1, 0 ≤ curve row3 2 x := by
  have cc := grid_cover row3 2 (1/2) 1 (1/2) (1099511627775/1099511627776) grid3_2 params3 check3_2 (by norm_num) (by norm_num)
  norm_num at cc ⊢
  apply cc
  · have ee := edgeMid row3 2 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
  · have ee := edgeR row3 2 params3 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private def grid4_0 : List ℚ := [(1/549755813888),(1/274877906944),(1/137438953472),(1/68719476736),(1/34359738368),(1/17179869184),(1/8589934592),(1/4294967296),(1/2147483648),(1/1073741824),(1/536870912),(1/268435456),(1/134217728),(1/67108864),(1/33554432),(1/16777216),(1/8388608),(1/4194304),(1/2097152),(1/1048576),(1/524288),(1/262144),(1/131072),(1/65536),(1/32768),(1/16384),(1/8192),(1/4096),(1/2048),(1/1024),(1/512),(1/256),(1/128),(1/64),(1/32),(1/16),(1/8),(3/16),(1/4),(9/32),(5/16),(11/32),(3/8),(13/32),(7/16),(15/32),(1/2),(33/64),(17/32),(35/64),(9/16),(37/64),(19/32),(77/128),(39/64),(79/128),(5/8),(81/128),(163/256),(41/64),(165/256),(83/128),(167/256),(335/512),(21/32),(337/512),(169/256),(677/1024),(339/512),(679/1024),(85/128),(681/1024),(1363/2048),(341/512),(1365/2048),(683/1024),(1367/2048),(171/256),(2737/4096),(1369/2048),(2739/4096),(685/1024),(2741/4096),(1371/2048),(2743/4096),(343/512),(2745/4096),(1373/2048),(2747/4096),(687/1024),(1375/2048),(43/64),(1377/2048),(689/1024),(1379/2048),(345/512),(691/1024),(173/256),(693/1024),(347/512),(87/128),(349/512),(175/256),(351/512),(11/16),(177/256),(89/128),(179/256),(45/64),(91/128),(23/32),(93/128),(47/64),(3/4),(49/64),(25/32),(51/64),(13/16),(27/32),(7/8),(29/32),(15/16),(31/32),(63/64),(127/128),(255/256),(511/512),(1023/1024),(2047/2048),(4095/4096),(8191/8192),(16383/16384),(32767/32768),(65535/65536),(131071/131072),(262143/262144),(524287/524288),(1048575/1048576),(2097151/2097152),(4194303/4194304),(8388607/8388608),(16777215/16777216),(33554431/33554432),(67108863/67108864),(134217727/134217728),(268435455/268435456),(536870911/536870912),(1073741823/1073741824),(2147483647/2147483648),(4294967295/4294967296),(8589934591/8589934592),(17179869183/17179869184),(34359738367/34359738368),(68719476735/68719476736),(137438953471/137438953472),(274877906943/274877906944),(549755813887/549755813888),(1099511627775/1099511627776)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem check4_0 : gridCheck row4 0 (1099511627775/1099511627776) (1/1099511627776) grid4_0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem good4_0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ curve row4 0 x := by
  have cc := grid_cover row4 0 0 1 (1/1099511627776) (1099511627775/1099511627776) grid4_0 params4 check4_0 (by norm_num) (by norm_num)
  norm_num at cc ⊢
  apply cc
  · have ee := edgeL row4 0 params4 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
  · have ee := edgeR row4 0 params4 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private def grid4_1 : List ℚ := [(1/549755813888),(1/274877906944),(1/137438953472),(1/68719476736),(1/34359738368),(1/17179869184),(1/8589934592),(1/4294967296),(1/2147483648),(1/1073741824),(1/536870912),(1/268435456),(1/134217728),(1/67108864),(1/33554432),(1/16777216),(1/8388608),(1/4194304),(1/2097152),(1/1048576),(1/524288),(1/262144),(1/131072),(1/65536),(1/32768),(1/16384),(1/8192),(1/4096),(1/2048),(1/1024),(1/512),(1/256),(1/128),(1/64),(1/32),(1/16),(3/32),(1/8),(5/32),(3/16),(7/32),(1/4),(9/32),(5/16),(11/32),(3/8),(13/32),(7/16),(15/32),(1/2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem check4_1 : gridCheck row4 1 (1/2) (1/1099511627776) grid4_1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem good4_1 : ∀ x ∈ Icc (0:ℝ) (1/2), 0 ≤ curve row4 1 x := by
  have cc := grid_cover row4 1 0 (1/2) (1/1099511627776) (1/2) grid4_1 params4 check4_1 (by norm_num) (by norm_num)
  norm_num at cc ⊢
  apply cc
  · have ee := edgeL row4 1 params4 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
  · have ee := edgeMid row4 1 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private def grid4_2 : List ℚ := [(33/64),(17/32),(35/64),(9/16),(37/64),(19/32),(77/128),(39/64),(79/128),(5/8),(81/128),(163/256),(41/64),(165/256),(83/128),(167/256),(335/512),(21/32),(337/512),(169/256),(677/1024),(339/512),(679/1024),(85/128),(681/1024),(1363/2048),(341/512),(1365/2048),(683/1024),(1367/2048),(171/256),(2737/4096),(1369/2048),(2739/4096),(685/1024),(2741/4096),(1371/2048),(2743/4096),(343/512),(2745/4096),(1373/2048),(2747/4096),(687/1024),(1375/2048),(43/64),(1377/2048),(689/1024),(1379/2048),(345/512),(691/1024),(173/256),(693/1024),(347/512),(87/128),(349/512),(175/256),(351/512),(11/16),(177/256),(89/128),(179/256),(45/64),(91/128),(23/32),(93/128),(47/64),(3/4),(49/64),(25/32),(51/64),(13/16),(27/32),(7/8),(29/32),(15/16),(31/32),(63/64),(127/128),(255/256),(511/512),(1023/1024),(2047/2048),(4095/4096),(8191/8192),(16383/16384),(32767/32768),(65535/65536),(131071/131072),(262143/262144),(524287/524288),(1048575/1048576),(2097151/2097152),(4194303/4194304),(8388607/8388608),(16777215/16777216),(33554431/33554432),(67108863/67108864),(134217727/134217728),(268435455/268435456),(536870911/536870912),(1073741823/1073741824),(2147483647/2147483648),(4294967295/4294967296),(8589934591/8589934592),(17179869183/17179869184),(34359738367/34359738368),(68719476735/68719476736),(137438953471/137438953472),(274877906943/274877906944),(549755813887/549755813888),(1099511627775/1099511627776)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem check4_2 : gridCheck row4 2 (1099511627775/1099511627776) (1/2) grid4_2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem good4_2 : ∀ x ∈ Icc ((1/2):ℝ) 1, 0 ≤ curve row4 2 x := by
  have cc := grid_cover row4 2 (1/2) 1 (1/2) (1099511627775/1099511627776) grid4_2 params4 check4_2 (by norm_num) (by norm_num)
  norm_num at cc ⊢
  apply cc
  · have ee := edgeMid row4 2 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
  · have ee := edgeR row4 2 params4 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private def grid5_0 : List ℚ := [(1/549755813888),(1/274877906944),(1/137438953472),(1/68719476736),(1/34359738368),(1/17179869184),(1/8589934592),(1/4294967296),(1/2147483648),(1/1073741824),(1/536870912),(1/268435456),(1/134217728),(1/67108864),(1/33554432),(1/16777216),(1/8388608),(1/4194304),(1/2097152),(1/1048576),(1/524288),(1/262144),(1/131072),(1/65536),(1/32768),(1/16384),(1/8192),(1/4096),(1/2048),(1/1024),(1/512),(1/256),(1/128),(1/64),(1/32),(1/16),(1/8),(3/16),(1/4),(9/32),(5/16),(11/32),(3/8),(13/32),(7/16),(15/32),(1/2),(33/64),(17/32),(35/64),(9/16),(37/64),(19/32),(77/128),(39/64),(79/128),(5/8),(81/128),(163/256),(41/64),(165/256),(83/128),(167/256),(21/32),(337/512),(169/256),(339/512),(85/128),(681/1024),(341/512),(683/1024),(171/256),(685/1024),(343/512),(1373/2048),(687/1024),(1375/2048),(43/64),(1377/2048),(689/1024),(1379/2048),(345/512),(1381/2048),(691/1024),(1383/2048),(173/256),(1385/2048),(693/1024),(1387/2048),(347/512),(695/1024),(87/128),(697/1024),(349/512),(175/256),(351/512),(11/16),(353/512),(177/256),(89/128),(179/256),(45/64),(181/256),(91/128),(23/32),(93/128),(47/64),(95/128),(3/4),(49/64),(25/32),(51/64),(13/16),(27/32),(7/8),(29/32),(15/16),(31/32),(63/64),(127/128),(255/256),(511/512),(1023/1024),(2047/2048),(4095/4096),(8191/8192),(16383/16384),(32767/32768),(65535/65536),(131071/131072),(262143/262144),(524287/524288),(1048575/1048576),(2097151/2097152),(4194303/4194304),(8388607/8388608),(16777215/16777216),(33554431/33554432),(67108863/67108864),(134217727/134217728),(268435455/268435456),(536870911/536870912),(1073741823/1073741824),(2147483647/2147483648),(4294967295/4294967296),(8589934591/8589934592),(17179869183/17179869184),(34359738367/34359738368),(68719476735/68719476736),(137438953471/137438953472),(274877906943/274877906944),(549755813887/549755813888),(1099511627775/1099511627776)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem check5_0 : gridCheck row5 0 (1099511627775/1099511627776) (1/1099511627776) grid5_0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem good5_0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ curve row5 0 x := by
  have cc := grid_cover row5 0 0 1 (1/1099511627776) (1099511627775/1099511627776) grid5_0 params5 check5_0 (by norm_num) (by norm_num)
  norm_num at cc ⊢
  apply cc
  · have ee := edgeL row5 0 params5 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
  · have ee := edgeR row5 0 params5 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private def grid5_1 : List ℚ := [(1/549755813888),(1/274877906944),(1/137438953472),(1/68719476736),(1/34359738368),(1/17179869184),(1/8589934592),(1/4294967296),(1/2147483648),(1/1073741824),(1/536870912),(1/268435456),(1/134217728),(1/67108864),(1/33554432),(1/16777216),(1/8388608),(1/4194304),(1/2097152),(1/1048576),(1/524288),(1/262144),(1/131072),(1/65536),(1/32768),(1/16384),(1/8192),(1/4096),(1/2048),(1/1024),(1/512),(1/256),(1/128),(1/64),(1/32),(1/16),(3/32),(1/8),(5/32),(3/16),(7/32),(1/4),(9/32),(5/16),(11/32),(3/8),(13/32),(7/16),(15/32),(1/2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem check5_1 : gridCheck row5 1 (1/2) (1/1099511627776) grid5_1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem good5_1 : ∀ x ∈ Icc (0:ℝ) (1/2), 0 ≤ curve row5 1 x := by
  have cc := grid_cover row5 1 0 (1/2) (1/1099511627776) (1/2) grid5_1 params5 check5_1 (by norm_num) (by norm_num)
  norm_num at cc ⊢
  apply cc
  · have ee := edgeL row5 1 params5 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
  · have ee := edgeMid row5 1 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private def grid5_2 : List ℚ := [(33/64),(17/32),(35/64),(9/16),(37/64),(19/32),(77/128),(39/64),(79/128),(5/8),(81/128),(163/256),(41/64),(165/256),(83/128),(167/256),(21/32),(337/512),(169/256),(339/512),(85/128),(681/1024),(341/512),(683/1024),(171/256),(685/1024),(343/512),(1373/2048),(687/1024),(1375/2048),(43/64),(1377/2048),(689/1024),(1379/2048),(345/512),(1381/2048),(691/1024),(1383/2048),(173/256),(1385/2048),(693/1024),(1387/2048),(347/512),(695/1024),(87/128),(697/1024),(349/512),(175/256),(351/512),(11/16),(353/512),(177/256),(89/128),(179/256),(45/64),(181/256),(91/128),(23/32),(93/128),(47/64),(95/128),(3/4),(49/64),(25/32),(51/64),(13/16),(27/32),(7/8),(29/32),(15/16),(31/32),(63/64),(127/128),(255/256),(511/512),(1023/1024),(2047/2048),(4095/4096),(8191/8192),(16383/16384),(32767/32768),(65535/65536),(131071/131072),(262143/262144),(524287/524288),(1048575/1048576),(2097151/2097152),(4194303/4194304),(8388607/8388608),(16777215/16777216),(33554431/33554432),(67108863/67108864),(134217727/134217728),(268435455/268435456),(536870911/536870912),(1073741823/1073741824),(2147483647/2147483648),(4294967295/4294967296),(8589934591/8589934592),(17179869183/17179869184),(34359738367/34359738368),(68719476735/68719476736),(137438953471/137438953472),(274877906943/274877906944),(549755813887/549755813888),(1099511627775/1099511627776)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem check5_2 : gridCheck row5 2 (1099511627775/1099511627776) (1/2) grid5_2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem good5_2 : ∀ x ∈ Icc ((1/2):ℝ) 1, 0 ≤ curve row5 2 x := by
  have cc := grid_cover row5 2 (1/2) 1 (1/2) (1099511627775/1099511627776) grid5_2 params5 check5_2 (by norm_num) (by norm_num)
  norm_num at cc ⊢
  apply cc
  · have ee := edgeMid row5 2 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
  · have ee := edgeR row5 2 params5 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private def grid6_0 : List ℚ := [(1/549755813888),(1/274877906944),(1/137438953472),(1/68719476736),(1/34359738368),(1/17179869184),(1/8589934592),(1/4294967296),(1/2147483648),(1/1073741824),(1/536870912),(1/268435456),(1/134217728),(1/67108864),(1/33554432),(1/16777216),(1/8388608),(1/4194304),(1/2097152),(1/1048576),(1/524288),(1/262144),(1/131072),(1/65536),(1/32768),(1/16384),(1/8192),(1/4096),(1/2048),(1/1024),(1/512),(1/256),(1/128),(1/64),(1/32),(1/16),(1/8),(3/16),(1/4),(5/16),(11/32),(3/8),(13/32),(7/16),(15/32),(1/2),(33/64),(17/32),(35/64),(9/16),(37/64),(19/32),(39/64),(79/128),(5/8),(81/128),(41/64),(165/256),(83/128),(167/256),(21/32),(169/256),(339/512),(85/128),(341/512),(171/256),(343/512),(43/64),(689/1024),(345/512),(691/1024),(173/256),(693/1024),(347/512),(695/1024),(87/128),(697/1024),(349/512),(699/1024),(175/256),(701/1024),(351/512),(11/16),(353/512),(177/256),(355/512),(89/128),(179/256),(45/64),(181/256),(91/128),(183/256),(23/32),(93/128),(47/64),(95/128),(3/4),(49/64),(25/32),(51/64),(13/16),(27/32),(7/8),(29/32),(15/16),(31/32),(63/64),(127/128),(255/256),(511/512),(1023/1024),(2047/2048),(4095/4096),(8191/8192),(16383/16384),(32767/32768),(65535/65536),(131071/131072),(262143/262144),(524287/524288),(1048575/1048576),(2097151/2097152),(4194303/4194304),(8388607/8388608),(16777215/16777216),(33554431/33554432),(67108863/67108864),(134217727/134217728),(268435455/268435456),(536870911/536870912),(1073741823/1073741824),(2147483647/2147483648),(4294967295/4294967296),(8589934591/8589934592),(17179869183/17179869184),(34359738367/34359738368),(68719476735/68719476736),(137438953471/137438953472),(274877906943/274877906944),(549755813887/549755813888),(1099511627775/1099511627776)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem check6_0 : gridCheck row6 0 (1099511627775/1099511627776) (1/1099511627776) grid6_0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem good6_0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ curve row6 0 x := by
  have cc := grid_cover row6 0 0 1 (1/1099511627776) (1099511627775/1099511627776) grid6_0 params6 check6_0 (by norm_num) (by norm_num)
  norm_num at cc ⊢
  apply cc
  · have ee := edgeL row6 0 params6 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
  · have ee := edgeR row6 0 params6 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private def grid6_1 : List ℚ := [(1/549755813888),(1/274877906944),(1/137438953472),(1/68719476736),(1/34359738368),(1/17179869184),(1/8589934592),(1/4294967296),(1/2147483648),(1/1073741824),(1/536870912),(1/268435456),(1/134217728),(1/67108864),(1/33554432),(1/16777216),(1/8388608),(1/4194304),(1/2097152),(1/1048576),(1/524288),(1/262144),(1/131072),(1/65536),(1/32768),(1/16384),(1/8192),(1/4096),(1/2048),(1/1024),(1/512),(1/256),(1/128),(1/64),(1/32),(1/16),(3/32),(1/8),(5/32),(3/16),(7/32),(1/4),(9/32),(5/16),(11/32),(3/8),(13/32),(7/16),(15/32),(1/2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem check6_1 : gridCheck row6 1 (1/2) (1/1099511627776) grid6_1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem good6_1 : ∀ x ∈ Icc (0:ℝ) (1/2), 0 ≤ curve row6 1 x := by
  have cc := grid_cover row6 1 0 (1/2) (1/1099511627776) (1/2) grid6_1 params6 check6_1 (by norm_num) (by norm_num)
  norm_num at cc ⊢
  apply cc
  · have ee := edgeL row6 1 params6 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
  · have ee := edgeMid row6 1 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private def grid6_2 : List ℚ := [(33/64),(17/32),(35/64),(9/16),(37/64),(19/32),(39/64),(79/128),(5/8),(81/128),(41/64),(165/256),(83/128),(167/256),(21/32),(169/256),(339/512),(85/128),(341/512),(171/256),(343/512),(43/64),(689/1024),(345/512),(691/1024),(173/256),(693/1024),(347/512),(695/1024),(87/128),(697/1024),(349/512),(699/1024),(175/256),(701/1024),(351/512),(11/16),(353/512),(177/256),(355/512),(89/128),(179/256),(45/64),(181/256),(91/128),(183/256),(23/32),(93/128),(47/64),(95/128),(3/4),(49/64),(25/32),(51/64),(13/16),(27/32),(7/8),(29/32),(15/16),(31/32),(63/64),(127/128),(255/256),(511/512),(1023/1024),(2047/2048),(4095/4096),(8191/8192),(16383/16384),(32767/32768),(65535/65536),(131071/131072),(262143/262144),(524287/524288),(1048575/1048576),(2097151/2097152),(4194303/4194304),(8388607/8388608),(16777215/16777216),(33554431/33554432),(67108863/67108864),(134217727/134217728),(268435455/268435456),(536870911/536870912),(1073741823/1073741824),(2147483647/2147483648),(4294967295/4294967296),(8589934591/8589934592),(17179869183/17179869184),(34359738367/34359738368),(68719476735/68719476736),(137438953471/137438953472),(274877906943/274877906944),(549755813887/549755813888),(1099511627775/1099511627776)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem check6_2 : gridCheck row6 2 (1099511627775/1099511627776) (1/2) grid6_2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem good6_2 : ∀ x ∈ Icc ((1/2):ℝ) 1, 0 ≤ curve row6 2 x := by
  have cc := grid_cover row6 2 (1/2) 1 (1/2) (1099511627775/1099511627776) grid6_2 params6 check6_2 (by norm_num) (by norm_num)
  norm_num at cc ⊢
  apply cc
  · have ee := edgeMid row6 2 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
  · have ee := edgeR row6 2 params6 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private def grid7_0 : List ℚ := [(1/549755813888),(1/274877906944),(1/137438953472),(1/68719476736),(1/34359738368),(1/17179869184),(1/8589934592),(1/4294967296),(1/2147483648),(1/1073741824),(1/536870912),(1/268435456),(1/134217728),(1/67108864),(1/33554432),(1/16777216),(1/8388608),(1/4194304),(1/2097152),(1/1048576),(1/524288),(1/262144),(1/131072),(1/65536),(1/32768),(1/16384),(1/8192),(1/4096),(1/2048),(1/1024),(1/512),(1/256),(1/128),(1/64),(1/32),(1/16),(1/8),(3/16),(1/4),(5/16),(11/32),(3/8),(13/32),(7/16),(15/32),(1/2),(17/32),(35/64),(9/16),(37/64),(19/32),(39/64),(79/128),(5/8),(81/128),(41/64),(83/128),(167/256),(21/32),(169/256),(85/128),(171/256),(43/64),(345/512),(173/256),(347/512),(87/128),(349/512),(175/256),(351/512),(11/16),(353/512),(177/256),(355/512),(89/128),(357/512),(179/256),(359/512),(45/64),(181/256),(91/128),(183/256),(23/32),(93/128),(47/64),(95/128),(3/4),(49/64),(25/32),(51/64),(13/16),(27/32),(7/8),(29/32),(15/16),(31/32),(63/64),(127/128),(255/256),(511/512),(1023/1024),(2047/2048),(4095/4096),(8191/8192),(16383/16384),(32767/32768),(65535/65536),(131071/131072),(262143/262144),(524287/524288),(1048575/1048576),(2097151/2097152),(4194303/4194304),(8388607/8388608),(16777215/16777216),(33554431/33554432),(67108863/67108864),(134217727/134217728),(268435455/268435456),(536870911/536870912),(1073741823/1073741824),(2147483647/2147483648),(4294967295/4294967296),(8589934591/8589934592),(17179869183/17179869184),(34359738367/34359738368),(68719476735/68719476736),(137438953471/137438953472),(274877906943/274877906944),(549755813887/549755813888),(1099511627775/1099511627776)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem check7_0 : gridCheck row7 0 (1099511627775/1099511627776) (1/1099511627776) grid7_0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem good7_0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ curve row7 0 x := by
  have cc := grid_cover row7 0 0 1 (1/1099511627776) (1099511627775/1099511627776) grid7_0 params7 check7_0 (by norm_num) (by norm_num)
  norm_num at cc ⊢
  apply cc
  · have ee := edgeL row7 0 params7 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
  · have ee := edgeR row7 0 params7 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private def grid7_1 : List ℚ := [(1/549755813888),(1/274877906944),(1/137438953472),(1/68719476736),(1/34359738368),(1/17179869184),(1/8589934592),(1/4294967296),(1/2147483648),(1/1073741824),(1/536870912),(1/268435456),(1/134217728),(1/67108864),(1/33554432),(1/16777216),(1/8388608),(1/4194304),(1/2097152),(1/1048576),(1/524288),(1/262144),(1/131072),(1/65536),(1/32768),(1/16384),(1/8192),(1/4096),(1/2048),(1/1024),(1/512),(1/256),(1/128),(1/64),(1/32),(1/16),(3/32),(1/8),(5/32),(3/16),(1/4),(9/32),(5/16),(11/32),(3/8),(13/32),(7/16),(15/32),(1/2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem check7_1 : gridCheck row7 1 (1/2) (1/1099511627776) grid7_1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem good7_1 : ∀ x ∈ Icc (0:ℝ) (1/2), 0 ≤ curve row7 1 x := by
  have cc := grid_cover row7 1 0 (1/2) (1/1099511627776) (1/2) grid7_1 params7 check7_1 (by norm_num) (by norm_num)
  norm_num at cc ⊢
  apply cc
  · have ee := edgeL row7 1 params7 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
  · have ee := edgeMid row7 1 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private def grid7_2 : List ℚ := [(17/32),(35/64),(9/16),(37/64),(19/32),(39/64),(79/128),(5/8),(81/128),(41/64),(83/128),(167/256),(21/32),(169/256),(85/128),(171/256),(43/64),(345/512),(173/256),(347/512),(87/128),(349/512),(175/256),(351/512),(11/16),(353/512),(177/256),(355/512),(89/128),(357/512),(179/256),(359/512),(45/64),(181/256),(91/128),(183/256),(23/32),(93/128),(47/64),(95/128),(3/4),(49/64),(25/32),(51/64),(13/16),(53/64),(27/32),(7/8),(29/32),(15/16),(31/32),(63/64),(127/128),(255/256),(511/512),(1023/1024),(2047/2048),(4095/4096),(8191/8192),(16383/16384),(32767/32768),(65535/65536),(131071/131072),(262143/262144),(524287/524288),(1048575/1048576),(2097151/2097152),(4194303/4194304),(8388607/8388608),(16777215/16777216),(33554431/33554432),(67108863/67108864),(134217727/134217728),(268435455/268435456),(536870911/536870912),(1073741823/1073741824),(2147483647/2147483648),(4294967295/4294967296),(8589934591/8589934592),(17179869183/17179869184),(34359738367/34359738368),(68719476735/68719476736),(137438953471/137438953472),(274877906943/274877906944),(549755813887/549755813888),(1099511627775/1099511627776)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem check7_2 : gridCheck row7 2 (1099511627775/1099511627776) (1/2) grid7_2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem good7_2 : ∀ x ∈ Icc ((1/2):ℝ) 1, 0 ≤ curve row7 2 x := by
  have cc := grid_cover row7 2 (1/2) 1 (1/2) (1099511627775/1099511627776) grid7_2 params7 check7_2 (by norm_num) (by norm_num)
  norm_num at cc ⊢
  apply cc
  · have ee := edgeMid row7 2 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
  · have ee := edgeR row7 2 params7 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private def grid8_0 : List ℚ := [(1/549755813888),(1/274877906944),(1/137438953472),(1/68719476736),(1/34359738368),(1/17179869184),(1/8589934592),(1/4294967296),(1/2147483648),(1/1073741824),(1/536870912),(1/268435456),(1/134217728),(1/67108864),(1/33554432),(1/16777216),(1/8388608),(1/4194304),(1/2097152),(1/1048576),(1/524288),(1/262144),(1/131072),(1/65536),(1/32768),(1/16384),(1/8192),(1/4096),(1/2048),(1/1024),(1/512),(1/256),(1/128),(1/64),(1/32),(1/16),(1/8),(3/16),(1/4),(5/16),(11/32),(3/8),(13/32),(7/16),(15/32),(1/2),(17/32),(35/64),(9/16),(37/64),(19/32),(39/64),(5/8),(81/128),(41/64),(83/128),(21/32),(85/128),(171/256),(43/64),(173/256),(87/128),(175/256),(11/16),(177/256),(89/128),(179/256),(45/64),(181/256),(91/128),(183/256),(23/32),(185/256),(93/128),(187/256),(47/64),(95/128),(3/4),(97/128),(49/64),(25/32),(51/64),(13/16),(53/64),(27/32),(7/8),(29/32),(15/16),(31/32),(63/64),(127/128),(255/256),(511/512),(1023/1024),(2047/2048),(4095/4096),(8191/8192),(16383/16384),(32767/32768),(65535/65536),(131071/131072),(262143/262144),(524287/524288),(1048575/1048576),(2097151/2097152),(4194303/4194304),(8388607/8388608),(16777215/16777216),(33554431/33554432),(67108863/67108864),(134217727/134217728),(268435455/268435456),(536870911/536870912),(1073741823/1073741824),(2147483647/2147483648),(4294967295/4294967296),(8589934591/8589934592),(17179869183/17179869184),(34359738367/34359738368),(68719476735/68719476736),(137438953471/137438953472),(274877906943/274877906944),(549755813887/549755813888),(1099511627775/1099511627776)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem check8_0 : gridCheck row8 0 (1099511627775/1099511627776) (1/1099511627776) grid8_0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem good8_0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ curve row8 0 x := by
  have cc := grid_cover row8 0 0 1 (1/1099511627776) (1099511627775/1099511627776) grid8_0 params8 check8_0 (by norm_num) (by norm_num)
  norm_num at cc ⊢
  apply cc
  · have ee := edgeL row8 0 params8 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
  · have ee := edgeR row8 0 params8 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private def grid8_1 : List ℚ := [(1/549755813888),(1/274877906944),(1/137438953472),(1/68719476736),(1/34359738368),(1/17179869184),(1/8589934592),(1/4294967296),(1/2147483648),(1/1073741824),(1/536870912),(1/268435456),(1/134217728),(1/67108864),(1/33554432),(1/16777216),(1/8388608),(1/4194304),(1/2097152),(1/1048576),(1/524288),(1/262144),(1/131072),(1/65536),(1/32768),(1/16384),(1/8192),(1/4096),(1/2048),(1/1024),(1/512),(1/256),(1/128),(1/64),(1/32),(1/16),(3/32),(1/8),(5/32),(3/16),(1/4),(9/32),(5/16),(11/32),(3/8),(13/32),(7/16),(15/32),(1/2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem check8_1 : gridCheck row8 1 (1/2) (1/1099511627776) grid8_1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem good8_1 : ∀ x ∈ Icc (0:ℝ) (1/2), 0 ≤ curve row8 1 x := by
  have cc := grid_cover row8 1 0 (1/2) (1/1099511627776) (1/2) grid8_1 params8 check8_1 (by norm_num) (by norm_num)
  norm_num at cc ⊢
  apply cc
  · have ee := edgeL row8 1 params8 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
  · have ee := edgeMid row8 1 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private def grid8_2 : List ℚ := [(17/32),(35/64),(9/16),(37/64),(19/32),(39/64),(5/8),(81/128),(41/64),(83/128),(21/32),(85/128),(171/256),(43/64),(173/256),(87/128),(175/256),(11/16),(177/256),(89/128),(179/256),(45/64),(181/256),(91/128),(183/256),(23/32),(185/256),(93/128),(187/256),(47/64),(95/128),(3/4),(97/128),(49/64),(25/32),(51/64),(13/16),(53/64),(27/32),(7/8),(29/32),(15/16),(31/32),(63/64),(127/128),(255/256),(511/512),(1023/1024),(2047/2048),(4095/4096),(8191/8192),(16383/16384),(32767/32768),(65535/65536),(131071/131072),(262143/262144),(524287/524288),(1048575/1048576),(2097151/2097152),(4194303/4194304),(8388607/8388608),(16777215/16777216),(33554431/33554432),(67108863/67108864),(134217727/134217728),(268435455/268435456),(536870911/536870912),(1073741823/1073741824),(2147483647/2147483648),(4294967295/4294967296),(8589934591/8589934592),(17179869183/17179869184),(34359738367/34359738368),(68719476735/68719476736),(137438953471/137438953472),(274877906943/274877906944),(549755813887/549755813888),(1099511627775/1099511627776)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem check8_2 : gridCheck row8 2 (1099511627775/1099511627776) (1/2) grid8_2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem good8_2 : ∀ x ∈ Icc ((1/2):ℝ) 1, 0 ≤ curve row8 2 x := by
  have cc := grid_cover row8 2 (1/2) 1 (1/2) (1099511627775/1099511627776) grid8_2 params8 check8_2 (by norm_num) (by norm_num)
  norm_num at cc ⊢
  apply cc
  · have ee := edgeMid row8 2 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
  · have ee := edgeR row8 2 params8 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private def grid9_0 : List ℚ := [(1/549755813888),(1/274877906944),(1/137438953472),(1/68719476736),(1/34359738368),(1/17179869184),(1/8589934592),(1/4294967296),(1/2147483648),(1/1073741824),(1/536870912),(1/268435456),(1/134217728),(1/67108864),(1/33554432),(1/16777216),(1/8388608),(1/4194304),(1/2097152),(1/1048576),(1/524288),(1/262144),(1/131072),(1/65536),(1/32768),(1/16384),(1/8192),(1/4096),(1/2048),(1/1024),(1/512),(1/256),(1/128),(1/64),(1/32),(1/16),(1/8),(3/16),(1/4),(5/16),(3/8),(13/32),(7/16),(15/32),(1/2),(17/32),(9/16),(19/32),(39/64),(5/8),(41/64),(21/32),(43/64),(87/128),(11/16),(89/128),(45/64),(91/128),(23/32),(185/256),(93/128),(187/256),(47/64),(189/256),(95/128),(191/256),(3/4),(193/256),(97/128),(195/256),(49/64),(197/256),(99/128),(25/32),(101/128),(51/64),(103/128),(13/16),(53/64),(27/32),(55/64),(7/8),(29/32),(15/16),(31/32),(63/64),(127/128),(255/256),(511/512),(1023/1024),(2047/2048),(4095/4096),(8191/8192),(16383/16384),(32767/32768),(65535/65536),(131071/131072),(262143/262144),(524287/524288),(1048575/1048576),(2097151/2097152),(4194303/4194304),(8388607/8388608),(16777215/16777216),(33554431/33554432),(67108863/67108864),(134217727/134217728),(268435455/268435456),(536870911/536870912),(1073741823/1073741824),(2147483647/2147483648),(4294967295/4294967296),(8589934591/8589934592),(17179869183/17179869184),(34359738367/34359738368),(68719476735/68719476736),(137438953471/137438953472),(274877906943/274877906944),(549755813887/549755813888),(1099511627775/1099511627776)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem check9_0 : gridCheck row9 0 (1099511627775/1099511627776) (1/1099511627776) grid9_0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem good9_0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ curve row9 0 x := by
  have cc := grid_cover row9 0 0 1 (1/1099511627776) (1099511627775/1099511627776) grid9_0 params9 check9_0 (by norm_num) (by norm_num)
  norm_num at cc ⊢
  apply cc
  · have ee := edgeL row9 0 params9 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
  · have ee := edgeR row9 0 params9 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private def grid9_1 : List ℚ := [(1/549755813888),(1/274877906944),(1/137438953472),(1/68719476736),(1/34359738368),(1/17179869184),(1/8589934592),(1/4294967296),(1/2147483648),(1/1073741824),(1/536870912),(1/268435456),(1/134217728),(1/67108864),(1/33554432),(1/16777216),(1/8388608),(1/4194304),(1/2097152),(1/1048576),(1/524288),(1/262144),(1/131072),(1/65536),(1/32768),(1/16384),(1/8192),(1/4096),(1/2048),(1/1024),(1/512),(1/256),(1/128),(1/64),(1/32),(1/16),(3/32),(1/8),(3/16),(1/4),(5/16),(3/8),(13/32),(7/16),(15/32),(1/2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem check9_1 : gridCheck row9 1 (1/2) (1/1099511627776) grid9_1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem good9_1 : ∀ x ∈ Icc (0:ℝ) (1/2), 0 ≤ curve row9 1 x := by
  have cc := grid_cover row9 1 0 (1/2) (1/1099511627776) (1/2) grid9_1 params9 check9_1 (by norm_num) (by norm_num)
  norm_num at cc ⊢
  apply cc
  · have ee := edgeL row9 1 params9 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
  · have ee := edgeMid row9 1 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private def grid9_2 : List ℚ := [(17/32),(9/16),(19/32),(39/64),(5/8),(41/64),(21/32),(43/64),(87/128),(11/16),(89/128),(45/64),(91/128),(23/32),(185/256),(93/128),(187/256),(47/64),(189/256),(95/128),(191/256),(3/4),(193/256),(97/128),(195/256),(49/64),(197/256),(99/128),(25/32),(101/128),(51/64),(103/128),(13/16),(105/128),(53/64),(27/32),(55/64),(7/8),(57/64),(29/32),(15/16),(31/32),(63/64),(127/128),(255/256),(511/512),(1023/1024),(2047/2048),(4095/4096),(8191/8192),(16383/16384),(32767/32768),(65535/65536),(131071/131072),(262143/262144),(524287/524288),(1048575/1048576),(2097151/2097152),(4194303/4194304),(8388607/8388608),(16777215/16777216),(33554431/33554432),(67108863/67108864),(134217727/134217728),(268435455/268435456),(536870911/536870912),(1073741823/1073741824),(2147483647/2147483648),(4294967295/4294967296),(8589934591/8589934592),(17179869183/17179869184),(34359738367/34359738368),(68719476735/68719476736),(137438953471/137438953472),(274877906943/274877906944),(549755813887/549755813888),(1099511627775/1099511627776)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem check9_2 : gridCheck row9 2 (1099511627775/1099511627776) (1/2) grid9_2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem good9_2 : ∀ x ∈ Icc ((1/2):ℝ) 1, 0 ≤ curve row9 2 x := by
  have cc := grid_cover row9 2 (1/2) 1 (1/2) (1099511627775/1099511627776) grid9_2 params9 check9_2 (by norm_num) (by norm_num)
  norm_num at cc ⊢
  apply cc
  · have ee := edgeMid row9 2 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
  · have ee := edgeR row9 2 params9 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private def grid10_0 : List ℚ := [(1/549755813888),(1/274877906944),(1/137438953472),(1/68719476736),(1/34359738368),(1/17179869184),(1/8589934592),(1/4294967296),(1/2147483648),(1/1073741824),(1/536870912),(1/268435456),(1/134217728),(1/67108864),(1/33554432),(1/16777216),(1/8388608),(1/4194304),(1/2097152),(1/1048576),(1/524288),(1/262144),(1/131072),(1/65536),(1/32768),(1/16384),(1/8192),(1/4096),(1/2048),(1/1024),(1/512),(1/256),(1/128),(1/64),(1/32),(1/16),(1/8),(3/16),(1/4),(5/16),(3/8),(7/16),(15/32),(1/2),(17/32),(9/16),(19/32),(5/8),(21/32),(11/16),(45/64),(23/32),(47/64),(3/4),(49/64),(99/128),(25/32),(101/128),(51/64),(103/128),(13/16),(105/128),(53/64),(107/128),(27/32),(109/128),(55/64),(111/128),(7/8),(57/64),(29/32),(59/64),(15/16),(61/64),(31/32),(63/64),(127/128),(255/256),(511/512),(1023/1024),(2047/2048),(4095/4096),(8191/8192),(16383/16384),(32767/32768),(65535/65536),(131071/131072),(262143/262144),(524287/524288),(1048575/1048576),(2097151/2097152),(4194303/4194304),(8388607/8388608),(16777215/16777216),(33554431/33554432),(67108863/67108864),(134217727/134217728),(268435455/268435456),(536870911/536870912),(1073741823/1073741824),(2147483647/2147483648),(4294967295/4294967296),(8589934591/8589934592),(17179869183/17179869184),(34359738367/34359738368),(68719476735/68719476736),(137438953471/137438953472),(274877906943/274877906944),(549755813887/549755813888),(1099511627775/1099511627776)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem check10_0 : gridCheck row10 0 (1099511627775/1099511627776) (1/1099511627776) grid10_0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem good10_0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ curve row10 0 x := by
  have cc := grid_cover row10 0 0 1 (1/1099511627776) (1099511627775/1099511627776) grid10_0 params10 check10_0 (by norm_num) (by norm_num)
  norm_num at cc ⊢
  apply cc
  · have ee := edgeL row10 0 params10 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
  · have ee := edgeR row10 0 params10 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private def grid10_1 : List ℚ := [(1/549755813888),(1/274877906944),(1/137438953472),(1/68719476736),(1/34359738368),(1/17179869184),(1/8589934592),(1/4294967296),(1/2147483648),(1/1073741824),(1/536870912),(1/268435456),(1/134217728),(1/67108864),(1/33554432),(1/16777216),(1/8388608),(1/4194304),(1/2097152),(1/1048576),(1/524288),(1/262144),(1/131072),(1/65536),(1/32768),(1/16384),(1/8192),(1/4096),(1/2048),(1/1024),(1/512),(1/256),(1/128),(1/64),(1/32),(1/16),(3/32),(1/8),(3/16),(1/4),(5/16),(3/8),(7/16),(1/2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem check10_1 : gridCheck row10 1 (1/2) (1/1099511627776) grid10_1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem good10_1 : ∀ x ∈ Icc (0:ℝ) (1/2), 0 ≤ curve row10 1 x := by
  have cc := grid_cover row10 1 0 (1/2) (1/1099511627776) (1/2) grid10_1 params10 check10_1 (by norm_num) (by norm_num)
  norm_num at cc ⊢
  apply cc
  · have ee := edgeL row10 1 params10 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
  · have ee := edgeMid row10 1 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private def grid10_2 : List ℚ := [(17/32),(9/16),(19/32),(5/8),(21/32),(11/16),(23/32),(47/64),(3/4),(49/64),(25/32),(51/64),(13/16),(53/64),(27/32),(55/64),(7/8),(57/64),(29/32),(59/64),(15/16),(61/64),(31/32),(63/64),(127/128),(255/256),(511/512),(1023/1024),(2047/2048),(4095/4096),(8191/8192),(16383/16384),(32767/32768),(65535/65536),(131071/131072),(262143/262144),(524287/524288),(1048575/1048576),(2097151/2097152),(4194303/4194304),(8388607/8388608),(16777215/16777216),(33554431/33554432),(67108863/67108864),(134217727/134217728),(268435455/268435456),(536870911/536870912),(1073741823/1073741824),(2147483647/2147483648),(4294967295/4294967296),(8589934591/8589934592),(17179869183/17179869184),(34359738367/34359738368),(68719476735/68719476736),(137438953471/137438953472),(274877906943/274877906944),(549755813887/549755813888),(1099511627775/1099511627776)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem check10_2 : gridCheck row10 2 (1099511627775/1099511627776) (1/2) grid10_2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem good10_2 : ∀ x ∈ Icc ((1/2):ℝ) 1, 0 ≤ curve row10 2 x := by
  have cc := grid_cover row10 2 (1/2) 1 (1/2) (1099511627775/1099511627776) grid10_2 params10 check10_2 (by norm_num) (by norm_num)
  norm_num at cc ⊢
  apply cc
  · have ee := edgeMid row10 2 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
  · have ee := edgeR row10 2 params10 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private def grid11_0 : List ℚ := [(1/549755813888),(1/274877906944),(1/137438953472),(1/68719476736),(1/34359738368),(1/17179869184),(1/8589934592),(1/4294967296),(1/2147483648),(1/1073741824),(1/536870912),(1/268435456),(1/134217728),(1/67108864),(1/33554432),(1/16777216),(1/8388608),(1/4194304),(1/2097152),(1/1048576),(1/524288),(1/262144),(1/131072),(1/65536),(1/32768),(1/16384),(1/8192),(1/4096),(1/2048),(1/1024),(1/512),(1/256),(1/128),(1/64),(1/32),(1/16),(3/32),(1/8),(3/16),(1/4),(5/16),(3/8),(7/16),(1/2),(17/32),(9/16),(19/32),(5/8),(21/32),(11/16),(23/32),(47/64),(3/4),(49/64),(25/32),(51/64),(103/128),(13/16),(105/128),(53/64),(107/128),(215/256),(27/32),(217/256),(109/128),(437/512),(219/256),(439/512),(55/64),(441/512),(883/1024),(221/256),(885/1024),(443/512),(887/1024),(111/128),(889/1024),(445/512),(891/1024),(223/256),(893/1024),(447/512),(895/1024),(7/8),(897/1024),(449/512),(225/256),(451/512),(113/128),(453/512),(227/256),(57/64),(229/256),(115/128),(231/256),(29/32),(117/128),(59/64),(119/128),(15/16),(121/128),(61/64),(31/32),(63/64),(127/128),(255/256),(511/512),(1023/1024),(2047/2048),(4095/4096),(8191/8192),(16383/16384),(32767/32768),(65535/65536),(131071/131072),(262143/262144),(524287/524288),(1048575/1048576),(2097151/2097152),(4194303/4194304),(8388607/8388608),(16777215/16777216),(33554431/33554432),(67108863/67108864),(134217727/134217728),(268435455/268435456),(536870911/536870912),(1073741823/1073741824),(2147483647/2147483648),(4294967295/4294967296),(8589934591/8589934592),(17179869183/17179869184),(34359738367/34359738368),(68719476735/68719476736),(137438953471/137438953472),(274877906943/274877906944),(549755813887/549755813888),(1099511627775/1099511627776)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem check11_0 : gridCheck row11 0 (1099511627775/1099511627776) (1/1099511627776) grid11_0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem good11_0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ curve row11 0 x := by
  have cc := grid_cover row11 0 0 1 (1/1099511627776) (1099511627775/1099511627776) grid11_0 params11 check11_0 (by norm_num) (by norm_num)
  norm_num at cc ⊢
  apply cc
  · have ee := edgeL row11 0 params11 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
  · have ee := edgeR row11 0 params11 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private def grid11_1 : List ℚ := [(1/549755813888),(1/274877906944),(1/137438953472),(1/68719476736),(1/34359738368),(1/17179869184),(1/8589934592),(1/4294967296),(1/2147483648),(1/1073741824),(1/536870912),(1/268435456),(1/134217728),(1/67108864),(1/33554432),(1/16777216),(1/8388608),(1/4194304),(1/2097152),(1/1048576),(1/524288),(1/262144),(1/131072),(1/65536),(1/32768),(1/16384),(1/8192),(1/4096),(1/2048),(1/1024),(1/512),(1/256),(1/128),(1/64),(1/32),(1/16),(3/32),(1/8),(3/16),(1/4),(5/16),(3/8),(7/16),(1/2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem check11_1 : gridCheck row11 1 (1/2) (1/1099511627776) grid11_1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem good11_1 : ∀ x ∈ Icc (0:ℝ) (1/2), 0 ≤ curve row11 1 x := by
  have cc := grid_cover row11 1 0 (1/2) (1/1099511627776) (1/2) grid11_1 params11 check11_1 (by norm_num) (by norm_num)
  norm_num at cc ⊢
  apply cc
  · have ee := edgeL row11 1 params11 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
  · have ee := edgeMid row11 1 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private def grid11_2 : List ℚ := [(9/16),(5/8),(21/32),(11/16),(23/32),(3/4),(25/32),(13/16),(27/32),(7/8),(29/32),(59/64),(15/16),(61/64),(31/32),(63/64),(127/128),(255/256),(511/512),(1023/1024),(2047/2048),(4095/4096),(8191/8192),(16383/16384),(32767/32768),(65535/65536),(131071/131072),(262143/262144),(524287/524288),(1048575/1048576),(2097151/2097152),(4194303/4194304),(8388607/8388608),(16777215/16777216),(33554431/33554432),(67108863/67108864),(134217727/134217728),(268435455/268435456),(536870911/536870912),(1073741823/1073741824),(2147483647/2147483648),(4294967295/4294967296),(8589934591/8589934592),(17179869183/17179869184),(34359738367/34359738368),(68719476735/68719476736),(137438953471/137438953472),(274877906943/274877906944),(549755813887/549755813888),(1099511627775/1099511627776)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem check11_2 : gridCheck row11 2 (1099511627775/1099511627776) (1/2) grid11_2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem good11_2 : ∀ x ∈ Icc ((1/2):ℝ) 1, 0 ≤ curve row11 2 x := by
  have cc := grid_cover row11 2 (1/2) 1 (1/2) (1099511627775/1099511627776) grid11_2 params11 check11_2 (by norm_num) (by norm_num)
  norm_num at cc ⊢
  apply cc
  · have ee := edgeMid row11 2 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
  · have ee := edgeR row11 2 params11 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private def grid12_0 : List ℚ := [(1/549755813888),(1/274877906944),(1/137438953472),(1/68719476736),(1/34359738368),(1/17179869184),(1/8589934592),(1/4294967296),(1/2147483648),(1/1073741824),(1/536870912),(1/268435456),(1/134217728),(1/67108864),(1/33554432),(1/16777216),(1/8388608),(1/4194304),(1/2097152),(1/1048576),(1/524288),(1/262144),(1/131072),(1/65536),(1/32768),(1/16384),(1/8192),(1/4096),(1/2048),(1/1024),(1/512),(1/256),(1/128),(1/64),(1/32),(1/16),(3/32),(1/8),(3/16),(1/4),(5/16),(3/8),(7/16),(1/2),(9/16),(19/32),(5/8),(21/32),(11/16),(23/32),(3/4),(25/32),(51/64),(13/16),(53/64),(27/32),(55/64),(7/8),(113/128),(57/64),(115/128),(29/32),(117/128),(59/64),(119/128),(15/16),(121/128),(61/64),(123/128),(31/32),(125/128),(63/64),(127/128),(255/256),(511/512),(1023/1024),(2047/2048),(4095/4096),(8191/8192),(16383/16384),(32767/32768),(65535/65536),(131071/131072),(262143/262144),(524287/524288),(1048575/1048576),(2097151/2097152),(4194303/4194304),(8388607/8388608),(16777215/16777216),(33554431/33554432),(67108863/67108864),(134217727/134217728),(268435455/268435456),(536870911/536870912),(1073741823/1073741824),(2147483647/2147483648),(4294967295/4294967296),(8589934591/8589934592),(17179869183/17179869184),(34359738367/34359738368),(68719476735/68719476736),(137438953471/137438953472),(274877906943/274877906944),(549755813887/549755813888),(1099511627775/1099511627776)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem check12_0 : gridCheck row12 0 (1099511627775/1099511627776) (1/1099511627776) grid12_0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem good12_0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ curve row12 0 x := by
  have cc := grid_cover row12 0 0 1 (1/1099511627776) (1099511627775/1099511627776) grid12_0 params12 check12_0 (by norm_num) (by norm_num)
  norm_num at cc ⊢
  apply cc
  · intro x hx hy
    apply finalEdge 0
    · constructor <;> linarith [hx,hy]
    · exact le_trans (min_le_left _ _) (by linarith [hy])
  · intro x hx hy
    apply finalEdge 0
    · constructor <;> linarith [hx,hy]
    · exact le_trans (min_le_right _ _) (by linarith [hx])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private def grid12_1 : List ℚ := [(1/549755813888),(1/274877906944),(1/137438953472),(1/68719476736),(1/34359738368),(1/17179869184),(1/8589934592),(1/4294967296),(1/2147483648),(1/1073741824),(1/536870912),(1/268435456),(1/134217728),(1/67108864),(1/33554432),(1/16777216),(1/8388608),(1/4194304),(1/2097152),(1/1048576),(1/524288),(1/262144),(1/131072),(1/65536),(1/32768),(1/16384),(1/8192),(1/4096),(1/2048),(1/1024),(1/512),(1/256),(1/128),(1/64),(1/32),(1/16),(1/8),(3/16),(1/4),(5/16),(3/8),(7/16),(1/2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem check12_1 : gridCheck row12 1 (1/2) (1/1099511627776) grid12_1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem good12_1 : ∀ x ∈ Icc (0:ℝ) (1/2), 0 ≤ curve row12 1 x := by
  have cc := grid_cover row12 1 0 (1/2) (1/1099511627776) (1/2) grid12_1 params12 check12_1 (by norm_num) (by norm_num)
  norm_num at cc ⊢
  apply cc
  · intro x hx hy
    apply finalEdge 1
    · constructor <;> linarith [hx,hy]
    · exact le_trans (min_le_left _ _) (by linarith [hy])
  · have ee := edgeMid row12 1 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private def grid12_2 : List ℚ := [(9/16),(5/8),(11/16),(23/32),(3/4),(25/32),(13/16),(27/32),(7/8),(29/32),(15/16),(61/64),(31/32),(63/64),(127/128),(255/256),(511/512),(1023/1024),(2047/2048),(4095/4096),(8191/8192),(16383/16384),(32767/32768),(65535/65536),(131071/131072),(262143/262144),(524287/524288),(1048575/1048576),(2097151/2097152),(4194303/4194304),(8388607/8388608),(16777215/16777216),(33554431/33554432),(67108863/67108864),(134217727/134217728),(268435455/268435456),(536870911/536870912),(1073741823/1073741824),(2147483647/2147483648),(4294967295/4294967296),(8589934591/8589934592),(17179869183/17179869184),(34359738367/34359738368),(68719476735/68719476736),(137438953471/137438953472),(274877906943/274877906944),(549755813887/549755813888),(1099511627775/1099511627776)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem check12_2 : gridCheck row12 2 (1099511627775/1099511627776) (1/2) grid12_2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem good12_2 : ∀ x ∈ Icc ((1/2):ℝ) 1, 0 ≤ curve row12 2 x := by
  have cc := grid_cover row12 2 (1/2) 1 (1/2) (1099511627775/1099511627776) grid12_2 params12 check12_2 (by norm_num) (by norm_num)
  norm_num at cc ⊢
  apply cc
  · have ee := edgeMid row12 2 (by decide +kernel)
    norm_num at ee ⊢
    exact ee
  · intro x hx hy
    apply finalEdge 2
    · constructor <;> linarith [hx,hy]
    · exact le_trans (min_le_right _ _) (by linarith [hx])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem rowOK (d : Row)
    (hB : 0 ≤ d.B) (hD : 0 ≤ d.D)
    (base : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ curve d 0 x)
    (low : ∀ x ∈ Icc (0:ℝ) (1/2), 0 ≤ curve d 1 x)
    (high : ∀ x ∈ Icc (1/2:ℝ) 1, 0 ≤ curve d 2 x)
    (t : ℝ) (hl : (d.l:ℝ) ≤ t) (hu : t ≤ (d.u:ℝ)) :
    ∃ l u A B D L : ℝ, l ≤ t ∧ t ≤ u ∧ 0 ≤ B ∧ 0 ≤ D ∧
      (∀ x ∈ Icc (0:ℝ) 1, L ≤ C6Intermediate.residual C6Projected.moment
        0.61766 0.0356 1.000000001 (121/174) l u A B D x) ∧
      (∀ x ∈ Icc (0:ℝ) (1/2), -L ≤ C6Intermediate.residual C6Projected.moment
        0.61766 0.0356 1.000000001 (121/174) l u A B D x + 2*0.0356*binEntropy x) ∧
      (∀ x ∈ Icc (1/2:ℝ) 1, 0 ≤ C6Intermediate.residual C6Projected.moment
        0.61766 0.0356 1.000000001 (121/174) l u A B D x + 0.0356*binEntropy (C6Intermediate.capUpper x)) := by
  refine ⟨d.l,d.u,d.A,d.B,d.D,d.L,hl,hu,by exact_mod_cast hB,by exact_mod_cast hD,?_,?_,?_⟩
  · intro x hx; have h := base x hx; norm_num [curve,C6Poly.P] at h; unfold C6Intermediate.residual; linarith only [h]
  · intro x hx; have h := low x hx; norm_num [curve,C6Poly.P] at h; unfold C6Intermediate.residual; linarith only [h]
  · intro x hx; have h := high x hx; norm_num [curve,C6Poly.P] at h; unfold C6Intermediate.residual C6Intermediate.capUpper; linarith only [h]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
theorem certificate : C6Intermediate.DualCells C6Projected.moment 0.61766 0.0356 1.000000001 (121/174) := by
  intro t ht
  obtain ⟨ht₀,ht₁⟩ := ht

  by_cases h0 : t ≤ (12/25)
  · apply rowOK row0 (by decide +kernel) (by decide +kernel) good0_0 good0_1 good0_2 t (by norm_num [row0] at * <;> linarith) (by norm_num [row0] at * <;> linarith)
  by_cases h1 : t ≤ (41/80)
  · apply rowOK row1 (by decide +kernel) (by decide +kernel) good1_0 good1_1 good1_2 t (by norm_num [row1] at * <;> linarith) (by norm_num [row1] at * <;> linarith)
  by_cases h2 : t ≤ (423/800)
  · apply rowOK row2 (by decide +kernel) (by decide +kernel) good2_0 good2_1 good2_2 t (by norm_num [row2] at * <;> linarith) (by norm_num [row2] at * <;> linarith)
  by_cases h3 : t ≤ (859/1600)
  · apply rowOK row3 (by decide +kernel) (by decide +kernel) good3_0 good3_1 good3_2 t (by norm_num [row3] at * <;> linarith) (by norm_num [row3] at * <;> linarith)
  by_cases h4 : t ≤ (109/200)
  · apply rowOK row4 (by decide +kernel) (by decide +kernel) good4_0 good4_1 good4_2 t (by norm_num [row4] at * <;> linarith) (by norm_num [row4] at * <;> linarith)
  by_cases h5 : t ≤ (177/320)
  · apply rowOK row5 (by decide +kernel) (by decide +kernel) good5_0 good5_1 good5_2 t (by norm_num [row5] at * <;> linarith) (by norm_num [row5] at * <;> linarith)
  by_cases h6 : t ≤ (449/800)
  · apply rowOK row6 (by decide +kernel) (by decide +kernel) good6_0 good6_1 good6_2 t (by norm_num [row6] at * <;> linarith) (by norm_num [row6] at * <;> linarith)
  by_cases h7 : t ≤ (231/400)
  · apply rowOK row7 (by decide +kernel) (by decide +kernel) good7_0 good7_1 good7_2 t (by norm_num [row7] at * <;> linarith) (by norm_num [row7] at * <;> linarith)
  by_cases h8 : t ≤ (61/100)
  · apply rowOK row8 (by decide +kernel) (by decide +kernel) good8_0 good8_1 good8_2 t (by norm_num [row8] at * <;> linarith) (by norm_num [row8] at * <;> linarith)
  by_cases h9 : t ≤ (37/50)
  · apply rowOK row9 (by decide +kernel) (by decide +kernel) good9_0 good9_1 good9_2 t (by norm_num [row9] at * <;> linarith) (by norm_num [row9] at * <;> linarith)
  by_cases h10 : t ≤ (87/100)
  · apply rowOK row10 (by decide +kernel) (by decide +kernel) good10_0 good10_1 good10_2 t (by norm_num [row10] at * <;> linarith) (by norm_num [row10] at * <;> linarith)
  by_cases h11 : t ≤ (187/200)
  · apply rowOK row11 (by decide +kernel) (by decide +kernel) good11_0 good11_1 good11_2 t (by norm_num [row11] at * <;> linarith) (by norm_num [row11] at * <;> linarith)
  apply rowOK row12 (by decide +kernel) (by decide +kernel) good12_0 good12_1 good12_2 t (by norm_num [row12] at * <;> linarith) (by norm_num [row12] at * <;> linarith)
end C6Cell
end

theorem OMA.solution : type_of% @Constant6a.c6a_lower_bound_intermediate :=
  C6Intermediate.bound_of_cells C6Cell.certificate
