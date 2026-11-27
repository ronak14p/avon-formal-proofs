import FormalConjectures.OptimizationConstants.«6a»
import Mathlib

/-!
# A frequency bound for union-closed families

Credit: Ronak Patel / Avon Labs (@ronak14p).
We use the shared-sign coupling of Liu (arXiv:2306.08824, Example 5) with the
quadratic amplitude of Costa and Sadhu (arXiv:2610.02295). The correlation
parameter is 7/10. Nonnegative covariance for every statistic of the two
prefixes is preserved when we append a bit using the shared sign.

The entropy defect x H(y) + y H(x) - H(xy) is a sum of products with positive
coefficients. Cauchy–Schwarz bounds it by the geometric mean of the two
diagonal defects. This reduces the numerical verification to a univariate
inequality. The kernel checks the rational logarithm enclosures and all grid
segments. Analytic bounds cover both endpoints. At mean 0.382725 the
entropy multiplier is 123455/123454, giving strict entropy growth.
-/

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

def independent (p q : ℝ) : ℝ := p+q-p*q

/-- Feasible values of the union probability for two Bernoulli laws. -/
def Feasible (p q r : ℝ) : Prop := p ≤ r ∧ q ≤ r ∧ r ≤ 1 ∧ r ≤ p+q

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

section
namespace C6CIID
open C6Coupled Finset Real
noncomputable section
variable {I : Type*} [Fintype I]

/-- Every real statistic has nonnegative covariance between the two prefixes. -/
def PSD {w : I → ℝ} (c : Coupling w) : Prop :=
  ∀ ψ : I → ℝ, (∑ i, w i * ψ i)^2 ≤ ∑ a, c.mass a * (ψ a.1 * ψ a.2)

theorem PSD_product (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (ht : ∑ i, w i = 1) :
    PSD (productCoupling w hw ht) := by
  intro ψ
  rw [Fintype.sum_prod_type,sq,Finset.sum_mul]
  apply le_of_eq
  apply sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  exact sum_congr rfl (fun j _ => by dsimp [productCoupling,product]; ring)

def Admissible (f : ℝ → ℝ) : Prop :=
  ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ f x ∧ f x ≤ min x (1-x)

def overlap (f : ℝ → ℝ) (p q : ℝ) :=
  (1-p)*(1-q) + f (1-p)*f (1-q)

private def splitUnion (f : ℝ → ℝ) (p q : ℝ) := 1-overlap f p q

private theorem splitFeasible (f : ℝ → ℝ) (hf : Admissible f)
    {p q : ℝ} (hp : p ∈ Set.Icc 0 1) (hq : q ∈ Set.Icc 0 1) :
    Feasible p q (splitUnion f p q) := by
  have h (x : ℝ) (hx : x ∈ Set.Icc 0 1) : 0 ≤ f (1-x) ∧ f (1-x) ≤ 1-x ∧ f (1-x) ≤ x := by
    have h := hf (1-x) ⟨by linarith [hx.2],by linarith [hx.1]⟩
    exact ⟨h.1,h.2.trans (min_le_left ..),by linarith [h.2.trans (min_le_right ..)]⟩
  have a := h p hp
  have b := h q hq
  unfold Feasible splitUnion overlap
  refine ⟨?_,?_,?_,?_⟩
  · nlinarith [mul_le_mul a.2.1 b.2.2 b.1 (sub_nonneg.mpr hp.2)]
  · nlinarith [mul_le_mul a.2.2 b.2.1 b.1 hp.1]
  · nlinarith [mul_nonneg a.1 b.1,mul_nonneg (sub_nonneg.mpr hp.2) (sub_nonneg.mpr hq.2)]
  · nlinarith [mul_nonneg hp.1 hq.1,mul_nonneg a.1 b.1]

private theorem splitSymm (f : ℝ → ℝ) (p q : ℝ) : splitUnion f p q = splitUnion f q p := by
  unfold splitUnion overlap; ring

/-- Conditional on a common fair sign, the two coordinates transition independently. -/
private theorem kernel_split (f : ℝ → ℝ) (p q : ℝ) (b d : Bool) :
    kernel p q (splitUnion f p q) b d =
      (bern (p+f (1-p)) b * bern (q+f (1-q)) d +
       bern (p-f (1-p)) b * bern (q-f (1-q)) d)/2 := by
  cases b <;> cases d <;> dsimp [kernel,bern,splitUnion,overlap] <;> ring

private def liftStat (v : I → ℝ) (ψ : I × Bool → ℝ) (x : I) :=
  ∑ b, bern (v x) b * ψ (x,b)

private theorem lift_expectation (w p : I → ℝ) (f : ℝ → ℝ) (ψ : I × Bool → ℝ) :
    (∑ a, extendMass w p a * ψ a) =
      ((∑ i, w i * liftStat (fun j => p j+f (1-p j)) ψ i) +
      (∑ i, w i * liftStat (fun j => p j-f (1-p j)) ψ i))/2 := by
  rw [Fintype.sum_prod_type,← sum_add_distrib,Finset.sum_div]
  apply sum_congr rfl
  intro x _
  simp only [liftStat,Fintype.sum_bool,extendMass,bern]
  ring

private theorem split_moment {w : I → ℝ} (c : Coupling w) (p : I → ℝ) (f : ℝ → ℝ)
    (hf : Admissible f) (hp : ∀ i, p i ∈ Set.Icc 0 1) (ψ : I × Bool → ℝ) :
    let c' := extend c p (splitUnion f) (fun i j => splitFeasible f hf (hp i) (hp j)) (splitSymm f)
    let plus := liftStat (fun i => p i + f (1-p i)) ψ
    let minus := liftStat (fun i => p i - f (1-p i)) ψ
    (∑ a, c'.mass a * (ψ a.1 * ψ a.2)) =
      ((∑ a, c.mass a * (plus a.1 * plus a.2)) + (∑ a, c.mass a * (minus a.1 * minus a.2)))/2 := by
  dsimp only
  simp only [Fintype.sum_prod_type, ← sum_add_distrib, Finset.sum_div]
  apply sum_congr rfl
  intro x _
  rw [sum_comm]
  apply sum_congr rfl
  intro y _
  simp only [Fintype.sum_bool,extend,kernel_split,liftStat,bern]
  ring

/-- Extend a positive-covariance prefix law using the shared sign transition
of Liu's Example 5. The entropy increment is measured by the absence probability. -/
theorem step (f : ℝ → ℝ) (hf : Admissible f) {w : I → ℝ} (p : I → ℝ)
    (u : I × I → I) (c : Coupling w) (hp : ∀ i, p i ∈ Set.Icc 0 1) (hc : PSD c) :
    ∃ c' : Coupling (extendMass w p), PSD c' ∧
      H (unionMass u c.mass) + ∑ a, c.mass a * binEntropy (overlap f (p a.1) (p a.2)) ≤
        H (unionMass (nextJoin u) c'.mass) := by
  let c' := extend c p (splitUnion f) (fun i j => splitFeasible f hf (hp i) (hp j)) (splitSymm f)
  refine ⟨c',?_,?_⟩
  · intro ψ
    let a := liftStat (fun i => p i + f (1-p i)) ψ
    let b := liftStat (fun i => p i - f (1-p i)) ψ
    have H₁ := hc a
    have H₂ := hc b
    rw [lift_expectation w p f ψ,split_moment c p f hf hp ψ]
    change (((∑ i, w i * a i) + ∑ i, w i * b i)/2)^2 ≤
      ((∑ z, c.mass z * (a z.1 * a z.2)) + ∑ z, c.mass z * (b z.1 * b z.2))/2
    nlinarith only [H₁,H₂,sq_nonneg ((∑ i, w i * a i) - (∑ i, w i * b i))]
  · have h := C6Coupled.growthStep u c p hp (splitUnion f)
      (fun i j => splitFeasible f hf (hp i) (hp j)) (splitSymm f)
    simpa only [splitUnion,binEntropy_one_sub] using h

end
end C6CIID
end

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

def ScalarBound (f : ℝ → ℝ) (t α k : ℝ) : Prop :=
  ∀ {I : Type} [Fintype I] (w p : I → ℝ) (c : Coupling w),
  C6CIID.PSD c → (∀ a, 0 ≤ w a) → (∑ a, w a) = 1 → (∀ a, p a ∈ Set.Icc 0 1) →
  (∑ a, w a * p a) ≤ t →
  k * (∑ a, w a * binEntropy (p a)) ≤
    (1-α) * (∑ a, product w a * binEntropy (independent (p a.1) (p a.2))) +
    α * (∑ a, c.mass a * binEntropy (C6CIID.overlap f (p a.1) (p a.2)))

private lemma sum_unit (v : Unit → ℝ) : ∑ a, v a = v () := by simp

private lemma sum_last {I : Type} [Fintype I] (v : I × Bool → ℝ) :
    ∑ a, v a = ∑ x, (v (x,true) + v (x,false)) := by simp only [Fintype.sum_prod_type, Fintype.sum_bool]

theorem cubeGrowth {f : ℝ → ℝ} (hf : C6CIID.Admissible f) {t α k : ℝ} (scalar : ScalarBound f t α k) (hα : α ∈ Set.Icc 0 1)
    (n : ℕ) (w : Cube n → ℝ) (hw : ∀ a, 0 ≤ w a) (hs : ∑ a, w a = 1)
    (hm : ∀ i, coordinateMean w i ≤ t) :
    ∃ c : Coupling w, C6CIID.PSD c ∧ k * H w ≤
      (1-α) * H (unionMass (fun a => join n a.1 a.2) (product w)) +
      α * H (unionMass (fun a => join n a.1 a.2) c.mass) := by
  classical
  induction n with
  | zero =>
    refine ⟨productCoupling w hw hs, C6CIID.PSD_product w hw hs, ?_⟩
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
    obtain ⟨c, hc, hprev⟩ := ih w₀ hw₀ hs₀ hm₀
    let u := fun a : Cube n × Cube n => join n a.1 a.2
    obtain ⟨c', hc', hdep⟩ := C6CIID.step f hf p u c hp hc
    have hind := independentStep w₀ p u hw₀ hs₀ hp
    have hl := scalar w₀ p c hc hw₀ hs₀ hp hmean
    rw [split]
    refine ⟨c', hc', ?_⟩
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

theorem lowerBound_of_scalar {f : ℝ → ℝ} (hf : C6CIID.Admissible f) {t α k : ℝ} (ht : t ≤ 1) (hα : α ∈ Set.Icc 0 1)
    (hk : 1 < k) (scalar : ScalarBound f t α k) : t ≤ Constant6a.C6a := by
  apply of_cube t ht
  intro n S hsize closed
  classical
  have hS : S.Nonempty := card_pos.mp (by omega)
  have hcard : 0 < (S.card : ℝ) := by exact_mod_cast hS.card_pos
  by_contra! h
  have hm (i : Coord n) : coordinateMean (uniform S) i ≤ t := by
    rw [uniform_mean]
    exact (div_le_iff₀ hcard).mpr (h i).le
  obtain ⟨c, _, hbound⟩ := cubeGrowth hf scalar hα n _ (uniform_nonneg S) (uniform_sum S hS) hm
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
namespace C6BDefect
open Finset Filter Real
noncomputable section

def defect (x y : ℝ) := x * binEntropy y + y * binEntropy x - binEntropy (x*y)

private def feat (x : ℝ) (n : ℕ) := (x-x^(n+2)) / sqrt (((n:ℝ)+1)*(n+2))

private theorem gram {x y : ℝ} (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1) :
    HasSum (fun n => feat x n * feat y n) (defect x y) := by
  have hs := C6Reduction.entropy_series (x := 1) (by norm_num) (by norm_num)
  simp only [one_pow, sub_self, negMulLog_zero, sub_zero] at hs
  have h := ((((hs.mul_left (x*y)).sub ((C6Reduction.entropy_series hx.1 hx.2).mul_left y)).sub
    ((C6Reduction.entropy_series hy.1 hy.2).mul_left x)).add
    (C6Reduction.entropy_series (mul_nonneg hx.1 hy.1) (mul_le_one₀ hx.2 hy.1 hy.2)))
  convert! h using 1
  · funext n
    dsimp [feat]
    rw [div_mul_div_comm, ← sq, sq_sqrt (by positivity), mul_pow]
    ring
  · simp only [defect, binEntropy_eq_negMulLog_add_negMulLog_one_sub, negMulLog_mul]
    ring

theorem cauchy {x y : ℝ} (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1) :
    defect x y ≤ sqrt (defect x x) * sqrt (defect y y) := by
  have a := (gram hx hx).tendsto_sum_nat
  have b := (gram hy hy).tendsto_sum_nat
  apply le_of_tendsto_of_tendsto' (gram hx hy).tendsto_sum_nat (a.sqrt.mul b.sqrt)
  intro n
  simpa only [sq] using sum_mul_le_sqrt_mul_sqrt (range n) (feat x) (feat y)

theorem mixed {f ψ : ℝ → ℝ} {m : ℝ} (hm : 1/2 < m)
    (diag : ∀ x ∈ Set.Icc (0:ℝ) 1, 2*x*binEntropy x - binEntropy (x^2) ≤
        (2*m-1) * binEntropy (x*x+f x*f x))
    (psi : ∀ x, ψ x = sqrt (binEntropy (x*x+f x*f x)))
    {x y : ℝ} (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1) :
    x*binEntropy y + y*binEntropy x ≤ binEntropy (x*y) + (2*m-1)*ψ x*ψ y := by
  have hpos : 0 ≤ 2*m-1 := by linarith
  have h (z : ℝ) (hz : z ∈ Set.Icc 0 1) : sqrt (defect z z) ≤ sqrt (2*m-1)*ψ z := by
    rw [psi, ← sqrt_mul hpos]
    apply sqrt_le_sqrt
    simpa only [defect,sq,two_mul,add_mul] using diag z hz
  have hp (z : ℝ) : 0 ≤ ψ z := by rw [psi]; positivity
  have hh := (cauchy hx hy).trans (mul_le_mul (h x hx) (h y hy) (sqrt_nonneg _) (mul_nonneg (sqrt_nonneg _) (hp _)))
  rw [mul_mul_mul_comm, ← sq, sq_sqrt hpos] at hh
  unfold defect at hh
  linarith only [hh]
end
end C6BDefect
end

section
namespace C6B
open Finset Real C6Coupled C6CIID
noncomputable section

def amplitude (x : ℝ) := (7/10)*x*(1-x)
def diagonal (x : ℝ) := x^2*(1+(49/100)*(1-x)^2)
def profile (x : ℝ) := sqrt (binEntropy (diagonal x))

theorem admissible : Admissible amplitude := by
  intro x ⟨hx,h1⟩
  have hh := mul_nonneg hx (sub_nonneg.mpr h1)
  dsimp [amplitude]
  constructor
  · linarith
  · apply le_min <;> nlinarith [sq_nonneg x,sq_nonneg (1-x)]

private theorem diagonal_eq (x : ℝ) : diagonal x = x*x+amplitude x*amplitude x := by
  dsimp [diagonal,amplitude]; ring

theorem scalar (K : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
    profile x * profile y ≤ binEntropy (x*y+amplitude x*amplitude y))
    (D : ∀ x ∈ Set.Icc (0:ℝ) 1,
      2*x*binEntropy x - binEntropy (x^2) ≤ (2*0.61727-1)*binEntropy (diagonal x))
    {I : Type} [Fintype I] (w p : I → ℝ) (c : Coupling w) (hcov : PSD c)
    (hw : ∀ a, 0 ≤ w a) (hs : ∑ a, w a = 1) (hp : ∀ a, p a ∈ Set.Icc 0 1)
    (hmean : (∑ a, w a*p a) ≤ 0.382725) :
    ((1-0.382725)/0.61727) * (∑ a, w a * binEntropy (p a)) ≤
      (1-(1-1/(2*0.61727))) * (∑ a, product w a * binEntropy (independent (p a.1) (p a.2))) +
      (1-1/(2*0.61727)) * (∑ a, c.mass a * binEntropy (overlap amplitude (p a.1) (p a.2))) := by
  let x := fun i => 1-p i
  let P := fun i => profile (x i)
  let h := fun i => binEntropy (p i)
  let O := fun a : I × I => binEntropy (overlap amplitude (p a.1) (p a.2))
  let U := fun a : I × I => binEntropy (independent (p a.1) (p a.2))
  have hx i : x i ∈ Set.Icc 0 1 := ⟨sub_nonneg.mpr (hp i).2,sub_le_self _ (hp i).1⟩
  have d z hz := (D z hz).trans_eq (by rw [diagonal_eq z])
  have hh (a : I × I) :
      x a.1 * h a.2 + h a.1 * x a.2 ≤ U a + (2*0.61727-1)*(P a.1*P a.2) := by
    have dh := C6BDefect.mixed (f := amplitude) (ψ := profile) (m := 0.61727)
      (by norm_num) d (fun z => congrArg (fun t => sqrt (binEntropy t)) (diagonal_eq z))
      (hx a.1) (hx a.2)
    have hu : binEntropy (x a.1*x a.2) = U a := by
      rw [← binEntropy_one_sub (x a.1*x a.2)]
      congr 1; dsimp [x, U,independent]; ring
    rw [hu] at dh
    simpa only [x,binEntropy_one_sub,h,P, mul_assoc, mul_comm (1 - p a.2) (binEntropy (p a.1))] using dh
  have hsep (g j : I → ℝ) :
      (∑ a, product w a * (g a.1*j a.2)) = (∑ i, w i*g i)*(∑ i, w i*j i) := by
    simp only [product, Fintype.sum_prod_type,mul_mul_mul_comm (w _) (w _),← mul_sum,← sum_mul]
  have he := sum_le_sum (s := univ) (fun (a : I × I) _ => mul_le_mul_of_nonneg_left (hh a)
    (show 0 ≤ product w a from mul_nonneg (hw a.1) (hw a.2)))
  simp only [mul_add,sum_add_distrib,hsep,
    mul_left_comm _ (2*(0.61727:ℝ)-1) _, ← mul_sum] at he
  have hk := (hcov P).trans (sum_le_sum (s := univ) (fun a _ =>
    mul_le_mul_of_nonneg_left (K _ (hx a.1) _ (hx a.2)) (c.nonneg a)))
  change (∑ i, w i*P i)^2 ≤ ∑ a, c.mass a * O a at hk
  have hn : (1-0.382725 : ℝ) ≤ ∑ i, w i*x i := by
    simp only [x,mul_sub,mul_one,sum_sub_distrib,hs]; linarith
  have hn' : 0 ≤ ∑ i, w i*h i := sum_nonneg fun i _ =>
    mul_nonneg (hw i) (binEntropy_nonneg (hp i).1 (hp i).2)
  change _ * (∑ i, w i * h i) ≤ _ * (∑ a, product w a * U a) + _ * (∑ a, c.mass a * O a)
  nlinarith only [he, hk, mul_le_mul_of_nonneg_right hn hn']

end
end C6B
end

section
namespace C6Kernel
open Real Set
noncomputable section

/-- Joint zero probability of the two outcomes in a shared binary protocol. -/
def joint (τ x y : ℝ) := x*y*(1 + τ*(1-x)*(1-y))
def diag (τ x : ℝ) := joint τ x x

private def W (τ x y : ℝ) := 1 + τ*(1-x)*(1-y)
private def U (τ x y : ℝ) := 1 + τ*(1-2*x)*(1-y)
private def X (τ x y : ℝ) := y * U τ x y
private def Y (τ x y : ℝ) := x * U τ y x
private def T (τ x y : ℝ) := 1 + τ*(1-2*x)*(1-2*y)

private lemma u_lower {τ x y : ℝ} (ht : 0 ≤ τ) (hx : x ∈ Icc 0 1) (hy : y ∈ Icc 0 1) :
    1-τ*(1-y) ≤ U τ x y := by
  dsimp [U]
  nlinarith only [mul_nonneg ht (mul_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr hy.2))]

private lemma product_bound {τ x y : ℝ} (ht : τ ∈ Icc 0 (1/2))
    (hx : x ∈ Icc 0 1) (hy : y ∈ Icc 0 1) :
    τ ≤ W τ x y * U τ x y * U τ y x := by
  have hW : 1 ≤ W τ x y := by unfold W; nlinarith only [mul_nonneg ht.1 (mul_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr hy.2))]
  have h₁ := u_lower ht.1 hx hy
  have h₂ := u_lower ht.1 hy hx
  have hx' : 1-τ ≤ U τ x y := by nlinarith [mul_nonneg ht.1 hy.1]
  have hy' : 1-τ ≤ U τ y x := by nlinarith [mul_nonneg ht.1 hx.1]
  have u0 : 0 ≤ U τ x y := by linarith [ht.2]
  have v0 : 0 ≤ U τ y x := by linarith [ht.2]
  calc
    τ ≤ U τ x y * U τ y x := by
      by_cases ex : x ≤ 1/2
      · have h : 1 ≤ U τ x y := by dsimp [U]; nlinarith only [mul_nonneg ht.1 (mul_nonneg (by linarith : 0 ≤ 1-2*x) (sub_nonneg.mpr hy.2))]
        linarith [mul_le_mul_of_nonneg_right h v0, ht.2]
      by_cases ey : y ≤ 1/2
      · have h : 1 ≤ U τ y x := by dsimp [U]; nlinarith only [mul_nonneg ht.1 (mul_nonneg (by linarith : 0 ≤ 1-2*y) (sub_nonneg.mpr hx.2))]
        linarith [mul_le_mul_of_nonneg_left h u0, ht.2]
      have h₃ : 3/4 ≤ U τ x y := by nlinarith [ht.2, mul_nonneg ht.1 (by linarith : 0 ≤ y-1/2)]
      have h₄ : 3/4 ≤ U τ y x := by nlinarith [ht.2, mul_nonneg ht.1 (by linarith : 0 ≤ x-1/2)]
      nlinarith [mul_le_mul h₃ h₄ (by norm_num) u0, ht.2]
    _ ≤ _ := by simpa [mul_assoc] using mul_le_mul_of_nonneg_right hW (mul_nonneg u0 v0)

private theorem joint_open {τ x y : ℝ} (ht : τ ∈ Icc 0 (1/2))
    (hx : x ∈ Ioo 0 1) (hy : y ∈ Ioo 0 1) : joint τ x y ∈ Ioo 0 1 := by
  have hquad := mul_le_one₀ (show τ*(1-x) ≤ 1 from
    mul_le_one₀ (by linarith [ht.2]) (by linarith [hx.2]) (by linarith [hx.1]))
    hy.1.le hy.2.le
  constructor
  · dsimp [joint]; exact mul_pos (mul_pos hx.1 hy.1)
      (by nlinarith only [mul_nonneg ht.1 (mul_nonneg (sub_nonneg.mpr hx.2.le) (sub_nonneg.mpr hy.2.le))])
  · apply lt_of_le_of_lt _ hx.2
    dsimp [joint]
    have := mul_le_mul_of_nonneg_right hquad (mul_nonneg hx.1.le (sub_nonneg.mpr hy.2.le))
    linarith only [this]

private lemma shape {τ x y : ℝ} (ht : τ ∈ Icc 0 (1/2)) (hx : x ∈ Ioo 0 1)
    (hy : y ∈ Ioo 0 1) : 0 ≤ X τ x y ∧ 0 ≤ Y τ x y ∧ 0 ≤ T τ x y ∧
    joint τ x y * (1-joint τ x y) * T τ x y ≤ X τ x y * Y τ x y := by
  have H := joint_open ht hx hy
  have h₁ := u_lower ht.1 (Ioo_subset_Icc_self hx) (Ioo_subset_Icc_self hy)
  have h₂ := u_lower ht.1 (Ioo_subset_Icc_self hy) (Ioo_subset_Icc_self hx)
  have hu : 0 ≤ U τ x y := by nlinarith [mul_nonneg ht.1 hy.1.le, ht.2]
  have hv : 0 ≤ U τ y x := by nlinarith [mul_nonneg ht.1 hx.1.le, ht.2]
  refine ⟨mul_nonneg hy.1.le hu, mul_nonneg hx.1.le hv, ?_, ?_⟩
  · unfold T
    have b₁ : |1-2*x| ≤ 1 := abs_le.mpr ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have b₂ : |1-2*y| ≤ 1 := abs_le.mpr ⟨by linarith [hy.2], by linarith [hy.1]⟩
    have b₃ := mul_le_mul b₁ b₂ (abs_nonneg _) (by norm_num)
    rw [← abs_mul] at b₃
    nlinarith [mul_le_mul_of_nonneg_left (abs_le.mp (le_trans b₃ (by norm_num : (1:ℝ)*1 ≤ 1))).1 ht.1, ht.2]
  · have hw : 0 < W τ x y := by dsimp [W]; nlinarith only [mul_nonneg ht.1 (mul_nonneg (sub_nonneg.mpr hx.2.le) (sub_nonneg.mpr hy.2.le))]
    have hb := product_bound ht (Ioo_subset_Icc_self hx) (Ioo_subset_Icc_self hy)
    have e : W τ x y*T τ x y = U τ x y*U τ y x + τ*x*y := by unfold W T U; ring
    have hr : joint τ x y = x*y*W τ x y := rfl
    have hb' : τ*(1-joint τ x y) ≤ W τ x y*U τ x y*U τ y x :=
      (by nlinarith [mul_nonneg ht.1 H.1.le] : τ*(1-joint τ x y) ≤ τ) |>.trans hb
    rw [hr] at hb' ⊢
    dsimp only [X, Y]
    nlinarith only [mul_nonneg (mul_nonneg hx.1.le hy.1.le)
      (mul_nonneg (mul_nonneg hx.1.le hy.1.le) (sub_nonneg.mpr hb')),
      congrArg ((x*y*(1-x*y*W τ x y))*·) e]

private def slope (r : ℝ) := log (1-r) - log r

/-- Logarithmic curvature inequality for binary entropy below its maximum. -/
private lemma entropy_curve {r : ℝ} (hr : r ∈ Ioo 0 1) (hl : 0 ≤ slope r) :
    binEntropy r * slope r ≤ binEntropy r + r*(1-r)*(slope r)^2 := by
  let L := slope r
  let Q := -log (1-r)
  have hQ : 0 ≤ Q := neg_nonneg.mpr (log_nonpos (by linarith [hr.2]) (by linarith [hr.1]))
  have hH : binEntropy r = r*L + Q := by dsimp [L,slope,Q,binEntropy]; rw [log_inv,log_inv]; ring
  change 0 ≤ L at hl
  change binEntropy r * L ≤ binEntropy r + r*(1-r)*L^2
  rw [hH]
  by_cases h : L ≤ 1
  · have hz := mul_le_mul_of_nonneg_left h hr.1.le
    nlinarith only [mul_nonneg hQ (sub_nonneg.mpr h), mul_nonneg (mul_nonneg hr.1.le hl)
      (show 0 ≤ 1-r*L by linarith [hr.2])]
  · have hq' := one_sub_inv_le_log_of_pos (sub_pos.mpr hr.2)
    have hq : Q*(1-r) ≤ r := by
      dsimp [Q]
      have := mul_le_mul_of_nonneg_right hq' (sub_nonneg.mpr hr.2.le)
      rw [sub_mul, one_mul, inv_mul_cancel₀ (sub_pos.mpr hr.2).ne'] at this
      linarith
    have he : exp L = (1-r)/r := by dsimp [L,slope]; rw [exp_sub, exp_log (sub_pos.mpr hr.2), exp_log hr.1]
    have hpow := sum_le_exp_of_nonneg hl 4
    norm_num [Finset.sum_range_succ, Nat.factorial] at hpow
    have h1 : L*(L+1) ≤ exp L := by
      nlinarith only [hpow, mul_nonneg (sq_nonneg (L-2)) (by linarith : 0 ≤ L+1)]
    rw [he] at h1
    have h2 := (le_div_iff₀ hr.1).mp h1
    apply (mul_le_mul_iff_left₀ (sub_pos.mpr hr.2)).mp
    nlinarith only [mul_nonneg (show 0 ≤ L-1 by linarith) (sub_nonneg.mpr hq),
      mul_nonneg hr.1.le (show 0 ≤ 1-r*L*(L+1) by linarith [hr.1]),
      sq_nonneg (r*L), mul_nonneg hr.1.le (sq_nonneg (r*L))]

private def logK (τ x y : ℝ) := log (binEntropy (joint τ x y))
private def Ly (τ x y : ℝ) := Y τ x y * slope (joint τ x y) / binEntropy (joint τ x y)

private theorem dJointX (τ x y : ℝ) :
    HasDerivAt (fun s => joint τ s y) (X τ x y) x := by
  unfold joint X U
  convert! (((hasDerivAt_id x).mul_const y).mul (((((hasDerivAt_const x (1:ℝ)).sub
    (hasDerivAt_id x)).const_mul τ).mul_const (1-y)).const_add 1)) using 1 <;> simp <;> ring

private theorem joint_swap (τ x y : ℝ) : joint τ x y = joint τ y x := by unfold joint; ring

private theorem dJointY (τ x y : ℝ) :
    HasDerivAt (joint τ x) (Y τ x y) y := by
  have he : joint τ x = fun s => joint τ s x := funext (joint_swap τ x)
  rw [he]
  exact dJointX τ y x

private theorem dYX (τ x y : ℝ) : HasDerivAt (fun s => Y τ s y) (T τ x y) x := by
  unfold Y T U
  convert! (hasDerivAt_id x).mul ((((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)).const_mul
    (τ*(1-2*y))).const_add 1) using 1 <;> simp <;> ring

private theorem dLogY {τ x y : ℝ} (ht : τ ∈ Icc 0 (1/2)) (hx : x ∈ Ioo 0 1)
    (hy : y ∈ Ioo 0 1) : HasDerivAt (logK τ x) (Ly τ x y) y := by
  have hr := joint_open ht hx hy
  have hh := binEntropy_pos hr.1 hr.2
  have hd := ((hasDerivAt_binEntropy hr.1.ne' hr.2.ne).comp y (dJointY τ x y)).log hh.ne'
  convert! hd using 1 <;> simp only [Ly, slope, Function.comp_apply] <;> ring

private theorem dLogDiag {τ y : ℝ} (ht : τ ∈ Icc 0 (1/2)) (hy : y ∈ Ioo 0 1) :
    HasDerivAt (fun s => logK τ s s) (2*Ly τ y y) y := by
  have hr := joint_open ht hy hy
  have hh := binEntropy_pos hr.1 hr.2
  have hj : HasDerivAt (fun s => joint τ s s) (2*Y τ y y) y := by
    unfold joint Y U
    have hi := hasDerivAt_id y
    have h := (hasDerivAt_const y (1:ℝ)).sub hi
    convert! (hi.mul hi).mul ((((h.const_mul τ).mul h).const_add 1)) using 1 <;> simp <;> ring
  convert! (((hasDerivAt_binEntropy hr.1.ne' hr.2.ne).comp (h := fun s => joint τ s s) y hj).log hh.ne') using 1 <;>
    simp only [Ly, slope, Function.comp_apply] <;> ring

private theorem mixed {τ x y : ℝ} (ht : τ ∈ Icc 0 (1/2)) (hx : x ∈ Ioo 0 1)
    (hy : y ∈ Ioo 0 1) : ∃ v ≤ 0, HasDerivAt (fun s => Ly τ s y) v x := by
  let r := joint τ x y
  let H := binEntropy r
  let L := slope r
  let A := X τ x y
  let B := Y τ x y
  let C := T τ x y
  let D := r*(1-r)
  have hr : r ∈ Ioo 0 1 := joint_open ht hx hy
  have hh : 0 < H := binEntropy_pos hr.1 hr.2
  have hd : 0 < D := mul_pos hr.1 (sub_pos.mpr hr.2)
  obtain ⟨hA,hB,hC,hcb⟩ := shape ht hx hy
  change D*C ≤ A*B at hcb
  have hl' : HasDerivAt slope (-1/D) r := by
    have h := (((hasDerivAt_const r (1:ℝ)).sub (hasDerivAt_id r)).log (sub_pos.mpr hr.2).ne').sub
      (hasDerivAt_log hr.1.ne')
    convert! h using 1 <;> simp [D] <;> field_simp [hr.1.ne',(sub_pos.mpr hr.2).ne'] <;> ring
  let v := ((C*L + B*((-1/D)*A))*H - B*L*(L*A))/H^2
  refine ⟨v, ?_, ?_⟩
  · apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    apply nonpos_of_mul_nonpos_right _ hd
    rw [show D*((C*L+B*(-1/D*A))*H-B*L*(L*A)) = D*C*(L*H) - A*B*(H+D*L^2) by
      field_simp [hd.ne']; ring]
    by_cases hl : 0 ≤ L
    · have h₁ := mul_le_mul_of_nonneg_right hcb (mul_nonneg hl hh.le)
      have h₂ := mul_le_mul_of_nonneg_left (entropy_curve hr hl) (mul_nonneg hA hB)
      change A*B*(H*L) ≤ A*B*(H+D*L^2) at h₂
      linarith only [h₁,h₂]
    · have h₁ : D*C*(L*H) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hd.le hC)
        (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hl) hh.le)
      have h₂ : 0 ≤ A*B*(H+D*L^2) :=
        mul_nonneg (mul_nonneg hA hB) (add_nonneg hh.le (mul_nonneg hd.le (sq_nonneg _)))
      linarith only [h₁,h₂]
  · have dj := dJointX τ x y
    have d := ((dYX τ x y).mul (hl'.comp (h := fun z => joint τ z y) x dj)).div ((hasDerivAt_binEntropy hr.1.ne' hr.2.ne).comp (h := fun z => joint τ z y) x dj) hh.ne'
    convert! d using 1 <;> simp only [v,A,B,C,D,H,L,r,slope,Function.comp_apply] <;> ring
private theorem log_diagonal_le {τ x y : ℝ} (ht : τ ∈ Icc 0 (1/2)) (hx : x ∈ Ioo 0 1)
    (hy : y ∈ Ioo 0 1) (hxy : x ≤ y) :
    logK τ x x + logK τ y y ≤ logK τ x y + logK τ x y := by
  have anti (z : ℝ) (hz : z ∈ Ioo 0 1) : AntitoneOn (fun s => Ly τ s z) (Ioo 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioo ..)
    · intro s hs
      obtain ⟨v,_,hd⟩ := mixed ht hs hz
      exact hd.continuousAt.continuousWithinAt
    · intro s hs
      obtain ⟨v,_,hd⟩ := mixed ht (interior_subset hs) hz
      exact hd.differentiableAt.differentiableWithinAt
    · intro s hs
      obtain ⟨v,hv,hd⟩ := mixed ht (interior_subset hs) hz
      exact hd.deriv.trans_le hv
  let g := fun z => 2 * logK τ x z - logK τ z z
  have inside {z : ℝ} (hz : z ∈ Icc x y) : z ∈ Ioo 0 1 :=
    ⟨hx.1.trans_le hz.1, hz.2.trans_lt hy.2⟩
  have hd (z : ℝ) (hz : z ∈ Icc x y) :
      HasDerivAt g (2*Ly τ x z - 2*Ly τ z z) z :=
    ((dLogY ht hx (inside hz)).const_mul 2).sub (dLogDiag ht (inside hz))
  have hmono : MonotoneOn g (Icc x y) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc ..)
    · exact fun z hz => (hd z hz).continuousAt.continuousWithinAt
    · exact fun z hz => (hd z (interior_subset hz)).hasDerivWithinAt
    · intro z hz
      have h := interior_subset hz
      linarith only [anti z (inside h) hx (inside h) h.1]
  have h := hmono (left_mem_Icc.mpr hxy) (right_mem_Icc.mpr hxy) hxy
  dsimp [g] at h
  linarith only [h]

theorem product_lower {τ x y : ℝ} (ht : τ ∈ Icc 0 (1/2)) (hx : x ∈ Icc 0 1)
    (hy : y ∈ Icc 0 1) :
    sqrt (binEntropy (diag τ x)) * sqrt (binEntropy (diag τ y)) ≤ binEntropy (joint τ x y) := by
  wlog hxy : x ≤ y generalizing x y
  · rw [mul_comm, joint_swap τ x y]
    exact this hy hx (le_of_not_ge hxy)
  rcases hx.1.eq_or_lt with h0|h0
  · subst x; simp [diag,joint]
  rcases hy.2.eq_or_lt with h1|h1
  · subst y; simpa [diag,joint] using binEntropy_nonneg hx.1 hx.2
  have hxo : x ∈ Ioo 0 1 := ⟨h0,hxy.trans_lt h1⟩
  have hyo : y ∈ Ioo 0 1 := ⟨h0.trans_le hxy,h1⟩
  have pos {a b : ℝ} (ha : a ∈ Ioo 0 1) (hb : b ∈ Ioo 0 1) :
      0 < binEntropy (joint τ a b) :=
    binEntropy_pos (joint_open ht ha hb).1 (joint_open ht ha hb).2
  have he := exp_le_exp.mpr (log_diagonal_le ht hxo hyo hxy)
  simp only [exp_add,logK, exp_log (pos hxo hxo), exp_log (pos hyo hyo), exp_log (pos hxo hyo)] at he
  have hh := sqrt_le_sqrt he
  simpa only [diag,sqrt_mul (pos hxo hxo).le, Real.sqrt_mul_self (pos hxo hyo).le] using hh

end
end C6Kernel
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

/-- The entropy minimum is at an endpoint. Its maximum is at the interval
point nearest one half. -/
def entropyInterval (n fuel : ℕ) (l u : ℚ) : ℚ × ℚ :=
  (min (entropyBounds n fuel l).1 (entropyBounds n fuel u).1,
   (entropyBounds n fuel (max l (min u (1/2)))).2)

theorem entropyInterval_spec (n fuel : ℕ) {l u : ℚ} {x : ℝ}
    (hl : 0 ≤ l) (hu : u ≤ 1) (hx : (l : ℝ) ≤ x) (hy : x ≤ (u : ℝ)) :
    ((entropyInterval n fuel l u).1 : ℝ) ≤ binEntropy x ∧
      binEntropy x ≤ ((entropyInterval n fuel l u).2 : ℝ) := by
  have hlu : l ≤ u := by exact_mod_cast hx.trans hy
  have hl' : (0:ℝ) ≤ l := by exact_mod_cast hl
  have hu' : (u:ℝ) ≤ 1 := by exact_mod_cast hu
  have m := binEntropy_strictMonoOn.monotoneOn
  have a := binEntropy_strictAntiOn.antitoneOn
  have bl := entropyBounds_spec n fuel hl (hlu.trans hu)
  have bu := entropyBounds_spec n fuel (hl.trans hlu) hu
  constructor
  · simp only [entropyInterval, Rat.cast_min]
    by_cases h : x ≤ 2⁻¹
    · exact (min_le_left ..).trans (bl.1.trans (m ⟨hl',hx.trans h⟩ ⟨hl'.trans hx,h⟩ hx))
    · exact (min_le_right ..).trans (bu.1.trans (a ⟨le_of_not_ge h,hy.trans hu'⟩ ⟨(le_of_not_ge h).trans hy,hu'⟩ hy))
  · by_cases h : u ≤ 1/2
    · have hu2 : (u:ℝ) ≤ 2⁻¹ := by have ht := Rat.cast_le (K := ℝ) |>.mpr h; simpa [one_div] using ht
      simp only [entropyInterval, min_eq_left h, max_eq_right hlu]
      exact (m ⟨hl'.trans hx,hy.trans hu2⟩ ⟨hl'.trans (hx.trans hy),hu2⟩ hy).trans bu.2
    · rw [show (entropyInterval n fuel l u).2 = (entropyBounds n fuel (max l (1/2))).2 by simp only [entropyInterval,min_eq_right (le_of_not_ge h)]]
      by_cases h' : 1/2 ≤ l
      · have hl2 : (2:ℝ)⁻¹ ≤ l := by have ht := Rat.cast_le (K := ℝ) |>.mpr h'; simpa [one_div] using ht
        rw [max_eq_left h']
        exact (a ⟨hl2,hx.trans (hy.trans hu')⟩ ⟨hl2.trans hx,hy.trans hu'⟩ hx).trans bl.2
      · rw [max_eq_right (le_of_not_ge h')]
        have hh := (entropyBounds_spec n fuel (q := 1/2) (by norm_num) (by norm_num)).2
        rw [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, one_div, binEntropy_two_inv] at hh
        exact binEntropy_le_log_two.trans hh


end C6Interval
end

section
namespace C6BDiag
open Real Set C6Interval
noncomputable section
private def g (x : ℝ) := x^2 * (1 + (49/100) * (1-x)^2)
private lemma g_bounds {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    x^2 ≤ g x ∧ g x ≤ x ∧ g x ≤ 2*x^2 := by
  have hm : 0 ≤ 1-x := sub_nonneg.mpr h1
  have hs : (1-x)^2 ≤ 1 := by nlinarith [mul_nonneg h0 (show 0 ≤ 2-x by linarith)]
  have hal : x*(1-x) ≤ 1 := by nlinarith [sq_nonneg (x-1/2)]
  constructor
  · unfold g; nlinarith [mul_nonneg (sq_nonneg x) (sq_nonneg (1-x))]
  constructor
  · unfold g; nlinarith only [mul_nonneg (mul_nonneg h0 hm) (show 0 ≤ 1-49/100*(x*(1-x)) by linarith)]
  · unfold g; nlinarith only [mul_nonneg (sq_nonneg x) (show 0 ≤ 1-49/100*(1-x)^2 by linarith)]

private lemma mono {x y : ℝ} (h0 : 0 ≤ x) (hxy : x ≤ y) (h1 : y ≤ 1) : g x ≤ g y := by
  have hsum : 0 ≤ x*(1-x)+y*(1-y) := by
    have := mul_nonneg h0 (sub_nonneg.mpr (hxy.trans h1))
    have := mul_nonneg (h0.trans hxy) (sub_nonneg.mpr h1); linarith
  have hprod := mul_nonneg (show 0 ≤ 2-x-y by linarith) hsum
  have hp : 0 ≤ (x+y) + 49/100*(1-x-y)*(x*(1-x)+y*(1-y)) := by
    linarith [sq_nonneg x, sq_nonneg y]
  unfold g
  nlinarith only [mul_nonneg (sub_nonneg.mpr hxy) hp]

private lemma D_formula {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    2*x*binEntropy x-binEntropy (x^2) =
      (1-x)*((1-x)*log (1-x)+(1+x)*log (1+x)) := by
  simp only [binEntropy,log_inv, log_pow]
  rw [show 1-x^2 = (1-x)*(1+x) by ring,
    log_mul (by linarith : 1-x ≠ 0) (by linarith : 1+x ≠ 0)]
  ring

private lemma D_mid {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    2*x*binEntropy x-binEntropy (x^2) =
       2*(1-x)*(log 2 - binEntropy ((1+x)/2)) := by
  rw [D_formula h0 h1]
  simp only [binEntropy, log_inv]
  rw [show 1 - (1+x)/2 = (1-x)/2 by ring,
    log_div (by linarith : 1+x ≠ 0) (by norm_num),
    log_div (by linarith : 1-x ≠ 0) (by norm_num)]
  ring

private lemma hlog {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    u*(-log u) ≤ binEntropy u := by
  rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  have h := negMulLog_nonneg (sub_nonneg.mpr h1) (sub_le_self _ h0)
  simp only [negMulLog] at *; linarith

private lemma bigLog {u : ℝ} (hp : 0 < u) {n : ℕ} (h : u ≤ 1/(2:ℝ)^n) :
    n*0.6931471803 ≤ -log u := by
  have hl := log_le_log hp h
  rw [one_div, log_inv, log_pow] at hl
  linarith [mul_le_mul_of_nonneg_left (le_of_lt log_two_gt_d9) (Nat.cast_nonneg (α := ℝ) n)]

private lemma left {x : ℝ} (h0 : 0 ≤ x) (hx : x ≤ 1/128) :
    2*x*binEntropy x-binEntropy (x^2) ≤ (2*0.61727-1)*binEntropy (g x) := by
  rcases h0.eq_or_lt with he|hp
  · simp [←he,g]
  have h1 : x < 1 := by linarith
  have hg := g_bounds hp.le h1.le
  have hpos := lt_of_lt_of_le (sq_pos_of_pos hp) hg.1
  have hG := hlog hpos.le (hg.2.1.trans h1.le)
  have hlog' := bigLog (n := 13) hpos (by
    have hh := mul_self_le_mul_self hp.le hx
    norm_num at hh ⊢; nlinarith [hg.2.2])
  norm_num1 at hlog'
  rw [D_formula hp.le h1]
  have hL := log_le_sub_one_of_pos (show 0 < 1-x by linarith)
  have hR := log_le_sub_one_of_pos (show 0 < 1+x by linarith)
  have he : (1-x)*log (1-x)+(1+x)*log (1+x) ≤ 2*x^2 := by
    nlinarith only [mul_le_mul_of_nonneg_left hL (by linarith : 0 ≤ 1-x),
      mul_le_mul_of_nonneg_left hR (by linarith : 0 ≤ 1+x)]
  nlinarith only [mul_le_mul_of_nonneg_left he (sub_nonneg.mpr h1.le),mul_nonneg hp.le (sq_nonneg x),
    mul_le_mul_of_nonneg_left hlog' hpos.le, hG,hg.1,sq_nonneg x]

private lemma right {x : ℝ} (h1 : x ≤ 1) (hx : 1-1/4096 ≤ x) :
    2*x*binEntropy x-binEntropy (x^2) ≤ (2*0.61727-1)*binEntropy (g x) := by
  rcases h1.eq_or_lt with he|hp
  · simp [he,g]
  have h0 : 0 ≤ x := by linarith
  have hg := g_bounds h0 hp.le
  have hG := hlog (show 0 ≤ 1-g x by linarith [hg.2.1]) (show 1-g x ≤ 1 by linarith [hg.1,sq_nonneg x])
  rw [binEntropy_one_sub] at hG
  have hL := bigLog (n := 11) (show 0 < 1-g x by linarith [hg.2.1]) (by norm_num; nlinarith [hg.1,sq_nonneg (1-x)])
  norm_num1 at hL
  rw [D_mid h0 hp]
  have hH := binEntropy_nonneg (show 0 ≤ (1+x)/2 by linarith) (show (1+x)/2 ≤ 1 by linarith)
  nlinarith only [mul_nonneg (sub_nonneg.mpr hp.le) hH,
    mul_le_mul_of_nonneg_left (le_of_lt log_two_lt_d9) (sub_nonneg.mpr hp.le),
    mul_le_mul_of_nonneg_left hL (show 0 ≤ 1-g x by linarith [hg.2.1]), hG,hg.2.1,hp.le]

private def gq (q : ℚ) := q^2*(1+(49/100)*(1-q)^2)
private lemma cg (q : ℚ) : (gq q:ℝ) = g q := by simp [gq,g]

private def verify (a b : ℚ) : Bool :=
  decide (0 ≤ a ∧ a ≤ b ∧ b < 1 ∧
    2*(1-a)*(0.6931471808-(entropyBounds 7 32 ((1+b)/2)).1) ≤
    (2*0.61727-1)*(entropyInterval 7 32 (gq a) (gq b)).1)

private theorem verified {a b : ℚ} (h : verify a b = true) {x : ℝ}
    (hx : x ∈ Icc (a:ℝ) b) :
    2*x*binEntropy x-binEntropy (x^2) ≤ (2*0.61727-1)*binEntropy (g x) := by
  simp only [verify,decide_eq_true_eq] at h
  obtain ⟨ha,hab,hb,hn⟩ := h
  have har : (0:ℝ) ≤ a := by exact_mod_cast ha
  have hbr : (b:ℝ) < 1 := by exact_mod_cast hb
  have hx0 := har.trans hx.1
  have hx1 := hx.2.trans_lt hbr
  have hga : 0 ≤ gq a := by unfold gq; positivity
  have hgb : gq b ≤ 1 := by
    have hh := ((g_bounds (hx0.trans hx.2) hbr.le).2.1.trans hbr.le)
    rw [←cg] at hh; exact_mod_cast hh
  have he := (entropyInterval_spec 7 32 (x := g x) hga hgb
    (by rw [cg]; exact mono har hx.1 hx1.le)
    (by rw [cg]; exact mono hx0 hx.2 hbr.le)).1
  have hm := (entropyBounds_spec 7 32 (q := (1+b)/2) (by linarith) (by linarith)).1
  push_cast at hm
  have ha' := binEntropy_strictAntiOn.antitoneOn
     (show (1+x)/2 ∈ Icc (2:ℝ)⁻¹ 1 by constructor <;> linarith)
     (show (1+(b:ℝ))/2 ∈ Icc (2:ℝ)⁻¹ 1 by constructor <;> linarith [hx.2])
     (show (1+x)/2 ≤ (1+b)/2 by linarith [hx.2])
  rw [D_mid hx0 hx1]
  have hi := mul_le_mul (show 1-x ≤ 1-a by linarith [hx.1])
    (show log 2-binEntropy ((1+x)/2) ≤ 0.6931471808 -
       ((entropyBounds 7 32 ((1+b)/2)).1:ℝ) by linarith [log_two_lt_d9])
    (sub_nonneg.mpr binEntropy_le_log_two) (show 0 ≤ 1-(a:ℝ) by linarith [hx.1])
  have hc := (Rat.cast_le (K := ℝ)).mpr hn
  push_cast at hc
  linarith only [hi,he,hc]

private def checkGrid (a : ℚ) : List ℚ → Bool
  | [] => decide (a = 4095/4096)
  | b::bs => verify a b && checkGrid b bs

private theorem from_grid (a : ℚ) (bs : List ℚ) (h : checkGrid a bs = true)
    {x : ℝ} (hx : (a:ℝ) < x) (h1 : x ≤ 4095/4096) :
    2*x*binEntropy x-binEntropy (x^2) ≤ (2*0.61727-1)*binEntropy (g x) := by
  induction bs generalizing a with
  | nil =>
    have hh : a = 4095/4096 := by simpa [checkGrid] using h
    subst a; norm_num at hx; linarith
  | cons b bs ih =>
    simp only [checkGrid,Bool.and_eq_true] at h
    rcases le_or_gt x (b:ℝ) with hb|hb
    · exact verified h.1 ⟨hx.le,hb⟩
    · exact ih b h.2 hb

private def segment (z : ℚ) (a : ℚ) : List ℚ → Bool
  | [] => decide (a=z)
  | b::bs => verify a b && segment z b bs

private theorem joined {a z : ℚ} (v w : List ℚ) (h : segment z a v = true)
    (h' : checkGrid z w = true) : checkGrid a (v++w) = true := by
  induction v generalizing a with
  | nil =>
    have e : a=z := by simpa [segment] using h
    simpa [e] using h'
  | cons b v ih =>
    simp only [segment,Bool.and_eq_true] at h
    simpa only [List.cons_append,checkGrid,Bool.and_eq_true] using And.intro h.1 (ih h.2)

private def pts0 : List ℚ := [(3/256),(1/64),(3/128),(1/32),(3/64),(1/16),(5/64),(3/32),(1/8),(5/32),(3/16),(7/32)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem run0 : segment (7/32) (1/128) pts0 = true := by decide +kernel
private def pts1 : List ℚ := [(1/4),(9/32),(5/16),(11/32),(3/8),(25/64),(13/32),(27/64),(7/16),(29/64),(15/32),(31/64)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem run1 : segment (31/64) (7/32) pts1 = true := by decide +kernel
private def pts2 : List ℚ := [(1/2),(65/128),(33/64),(67/128),(17/32),(69/128),(35/64),(71/128),(9/16),(73/128),(147/256),(37/64)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem run2 : segment (37/64) (31/64) pts2 = true := by decide +kernel
private def pts3 : List ℚ := [(149/256),(75/128),(151/256),(19/32),(153/256),(77/128),(155/256),(39/64),(313/512),(157/256),(315/512),(79/128)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem run3 : segment (79/128) (37/64) pts3 = true := by decide +kernel
private def pts4 : List ℚ := [(317/512),(159/256),(319/512),(5/8),(321/512),(161/256),(323/512),(81/128),(325/512),(163/256),(653/1024),(327/512)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem run4 : segment (327/512) (79/128) pts4 = true := by decide +kernel
private def pts5 : List ℚ := [(655/1024),(41/64),(657/1024),(329/512),(659/1024),(165/256),(661/1024),(331/512),(663/1024),(83/128),(665/1024),(333/512)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem run5 : segment (333/512) (327/512) pts5 = true := by decide +kernel
private def pts6 : List ℚ := [(667/1024),(167/256),(669/1024),(335/512),(671/1024),(21/32),(673/1024),(337/512),(1349/2048),(675/1024),(1351/2048),(169/256)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem run6 : segment (169/256) (333/512) pts6 = true := by decide +kernel
private def pts7 : List ℚ := [(1353/2048),(677/1024),(1355/2048),(339/512),(1357/2048),(679/1024),(1359/2048),(85/128),(1361/2048),(681/1024),(1363/2048),(341/512)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem run7 : segment (341/512) (169/256) pts7 = true := by decide +kernel
private def pts8 : List ℚ := [(1365/2048),(683/1024),(1367/2048),(171/256),(1369/2048),(685/1024),(1371/2048),(343/512),(1373/2048),(687/1024),(1375/2048),(43/64)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem run8 : segment (43/64) (341/512) pts8 = true := by decide +kernel
private def pts9 : List ℚ := [(1377/2048),(689/1024),(1379/2048),(345/512),(1381/2048),(691/1024),(1383/2048),(173/256),(1385/2048),(693/1024),(1387/2048),(347/512)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem run9 : segment (347/512) (43/64) pts9 = true := by decide +kernel
private def pts10 : List ℚ := [(1389/2048),(695/1024),(2781/4096),(1391/2048),(2783/4096),(87/128),(2785/4096),(1393/2048),(2787/4096),(697/1024),(2789/4096),(1395/2048)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem run10 : segment (1395/2048) (347/512) pts10 = true := by decide +kernel
private def pts11 : List ℚ := [(2791/4096),(349/512),(2793/4096),(1397/2048),(2795/4096),(699/1024),(2797/4096),(1399/2048),(2799/4096),(175/256),(2801/4096),(1401/2048)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem run11 : segment (1401/2048) (1395/2048) pts11 = true := by decide +kernel
private def pts12 : List ℚ := [(2803/4096),(701/1024),(2805/4096),(1403/2048),(2807/4096),(351/512),(2809/4096),(1405/2048),(2811/4096),(703/1024),(2813/4096),(1407/2048)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem run12 : segment (1407/2048) (1401/2048) pts12 = true := by decide +kernel
private def pts13 : List ℚ := [(2815/4096),(11/16),(2817/4096),(1409/2048),(2819/4096),(705/1024),(2821/4096),(1411/2048),(2823/4096),(353/512),(2825/4096),(1413/2048)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem run13 : segment (1413/2048) (1407/2048) pts13 = true := by decide +kernel
private def pts14 : List ℚ := [(2827/4096),(707/1024),(2829/4096),(1415/2048),(2831/4096),(177/256),(2833/4096),(1417/2048),(2835/4096),(709/1024),(2837/4096),(1419/2048)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem run14 : segment (1419/2048) (1413/2048) pts14 = true := by decide +kernel
private def pts15 : List ℚ := [(2839/4096),(355/512),(2841/4096),(1421/2048),(2843/4096),(711/1024),(2845/4096),(1423/2048),(2847/4096),(89/128),(2849/4096),(1425/2048)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem run15 : segment (1425/2048) (1419/2048) pts15 = true := by decide +kernel
private def pts16 : List ℚ := [(2851/4096),(713/1024),(2853/4096),(1427/2048),(2855/4096),(357/512),(2857/4096),(1429/2048),(2859/4096),(715/1024),(2861/4096),(1431/2048)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem run16 : segment (1431/2048) (1425/2048) pts16 = true := by decide +kernel
private def pts17 : List ℚ := [(2863/4096),(179/256),(2865/4096),(1433/2048),(2867/4096),(717/1024),(2869/4096),(1435/2048),(2871/4096),(359/512),(2873/4096),(1437/2048)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem run17 : segment (1437/2048) (1431/2048) pts17 = true := by decide +kernel
private def pts18 : List ℚ := [(2875/4096),(719/1024),(2877/4096),(1439/2048),(2879/4096),(45/64),(1441/2048),(721/1024),(1443/2048),(361/512),(1445/2048),(723/1024)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem run18 : segment (723/1024) (1437/2048) pts18 = true := by decide +kernel
private def pts19 : List ℚ := [(1447/2048),(181/256),(1449/2048),(725/1024),(1451/2048),(363/512),(1453/2048),(727/1024),(1455/2048),(91/128),(1457/2048),(729/1024)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem run19 : segment (729/1024) (723/1024) pts19 = true := by decide +kernel
private def pts20 : List ℚ := [(1459/2048),(365/512),(1461/2048),(731/1024),(1463/2048),(183/256),(1465/2048),(733/1024),(1467/2048),(367/512),(1469/2048),(735/1024)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem run20 : segment (735/1024) (729/1024) pts20 = true := by decide +kernel
private def pts21 : List ℚ := [(1471/2048),(23/32),(1473/2048),(737/1024),(1475/2048),(369/512),(1477/2048),(739/1024),(1479/2048),(185/256),(741/1024),(371/512)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem run21 : segment (371/512) (735/1024) pts21 = true := by decide +kernel
private def pts22 : List ℚ := [(743/1024),(93/128),(745/1024),(373/512),(747/1024),(187/256),(749/1024),(375/512),(751/1024),(47/64),(753/1024),(377/512)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem run22 : segment (377/512) (371/512) pts22 = true := by decide +kernel
private def pts23 : List ℚ := [(755/1024),(189/256),(757/1024),(379/512),(759/1024),(95/128),(761/1024),(381/512),(191/256),(383/512),(3/4),(385/512)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem run23 : segment (385/512) (377/512) pts23 = true := by decide +kernel
private def pts24 : List ℚ := [(193/256),(387/512),(97/128),(389/512),(195/256),(391/512),(49/64),(393/512),(197/256),(395/512),(99/128),(199/256)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem run24 : segment (199/256) (385/512) pts24 = true := by decide +kernel
private def pts25 : List ℚ := [(25/32),(201/256),(101/128),(203/256),(51/64),(205/256),(103/128),(207/256),(13/16),(209/256),(105/128),(53/64)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem run25 : segment (53/64) (199/256) pts25 = true := by decide +kernel
private def pts26 : List ℚ := [(107/128),(27/32),(109/128),(55/64),(111/128),(7/8),(113/128),(57/64),(115/128),(29/32),(117/128),(59/64)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem run26 : segment (59/64) (53/64) pts26 = true := by decide +kernel
private def pts27 : List ℚ := [(119/128),(15/16),(121/128),(61/64),(123/128),(31/32),(125/128),(63/64),(253/256),(127/128),(255/256),(511/512)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem run27 : segment (511/512) (59/64) pts27 = true := by decide +kernel
private def pts28 : List ℚ := [(1023/1024),(2047/2048),(4095/4096)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 9000000 in
private theorem run28 : segment (4095/4096) (511/512) pts28 = true := by decide +kernel

theorem bound (x : ℝ) (hx : x ∈ Icc 0 1) :
    2*x*binEntropy x-binEntropy (x^2) ≤ (2*(0.61727:ℝ)-1)*binEntropy (x^2*(1+(49/100)*(1-x)^2)) := by
  rcases le_or_gt x (1/128) with h|h
  · exact left hx.1 h
  rcases le_or_gt (1-1/4096) x with hR|hR
  · exact right hx.2 hR
  apply from_grid (1/128) (pts0 ++ pts1 ++ pts2 ++ pts3 ++ pts4 ++ pts5 ++ pts6 ++ pts7 ++ pts8 ++ pts9 ++ pts10 ++ pts11 ++ pts12 ++ pts13 ++ pts14 ++ pts15 ++ pts16 ++ pts17 ++ pts18 ++ pts19 ++ pts20 ++ pts21 ++ pts22 ++ pts23 ++ pts24 ++ pts25 ++ pts26 ++ pts27 ++ pts28 ++ []) _ (by simpa using h) (by linarith)
  apply joined pts0 _ run0
  apply joined pts1 _ run1
  apply joined pts2 _ run2
  apply joined pts3 _ run3
  apply joined pts4 _ run4
  apply joined pts5 _ run5
  apply joined pts6 _ run6
  apply joined pts7 _ run7
  apply joined pts8 _ run8
  apply joined pts9 _ run9
  apply joined pts10 _ run10
  apply joined pts11 _ run11
  apply joined pts12 _ run12
  apply joined pts13 _ run13
  apply joined pts14 _ run14
  apply joined pts15 _ run15
  apply joined pts16 _ run16
  apply joined pts17 _ run17
  apply joined pts18 _ run18
  apply joined pts19 _ run19
  apply joined pts20 _ run20
  apply joined pts21 _ run21
  apply joined pts22 _ run22
  apply joined pts23 _ run23
  apply joined pts24 _ run24
  apply joined pts25 _ run25
  apply joined pts26 _ run26
  apply joined pts27 _ run27
  apply joined pts28 _ run28
  simp [checkGrid]

end
end C6BDiag
end

theorem OMA.solution : type_of% @Constant6a.c6a_lower_bound_improved := by
  apply lt_of_lt_of_le (show (0.38272 : ℝ) < 0.382725 by norm_num)
  apply C6Intermediate.lowerBound_of_scalar (f := C6B.amplitude)
    (α := 1-1/(2*0.61727)) (k := (1-0.382725)/0.61727) C6B.admissible
    (by norm_num) (by constructor <;> norm_num) (by norm_num)
  apply C6B.scalar
  · intro x hx y hy
    have he (a b : ℝ) : C6Kernel.joint (49/100) a b = a*b+C6B.amplitude a*C6B.amplitude b := by
      unfold C6Kernel.joint C6B.amplitude; ring
    have diag (a : ℝ) : C6Kernel.diag (49/100) a = C6B.diagonal a := by
      unfold C6Kernel.diag C6Kernel.joint C6B.diagonal; ring
    simpa only [diag,he,C6B.profile] using C6Kernel.product_lower
      (τ := 49/100) (by constructor <;> norm_num) hx hy
  · exact C6BDiag.bound
