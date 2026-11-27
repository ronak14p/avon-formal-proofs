import FormalConjectures.ErdosProblems.«267»
import Mathlib

-- Problem: Erdős Problem 267 — fibonacci inverse sum
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/267.lean:74 (declaration Erdos267.erdos_267.variants.fibonacci_inverse_sum)
-- Credit: @ronak14p (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
# Erdős Problem 267 — Irrationality of the Reciprocal Fibonacci Constant (André-Jeannin, 1989)

We formalize a completely rational, self-contained proof that the reciprocal Fibonacci sum
`∑' k : ℕ, 1 / (Nat.fib k : ℝ)` is irrational:
1. Define signed Fibonacci numbers `zfib : ℤ → ℤ` and integer Fibonomial coefficients
   `fibBinom : ℕ → ℕ → ℕ` via their Pascal-type recurrence, avoiding divisibility boilerplate.
2. Construct explicit integer Padé weights `coeffA n k` and prove the exact Fibonomial
   Lagrange partial-fraction identity via univariate polynomial vanishing over `ℚ` at the
   `n + 1` distinct consecutive Fibonacci ratios `F_{r+2} / F_{r+1}` (`0 ≤ r ≤ n`).
3. Scale the resulting rational approximations by the naive product `prodFib n = ∏_{i=1}^n F_i`
   to obtain integer linear forms `intP n * psi - intQ n` whose infinite tail has uniform sign
   `(-1)^n` and satisfies `0 < |intP n * psi - intQ n| ≤ psi / F_{n+2}`, ruling out rationality.
-/

namespace OMA.Erdos267Fib

def zfib : ℤ → ℤ
  | Int.ofNat n => (Nat.fib n : ℤ)
  | Int.negSucc n => (-1) ^ n * (Nat.fib (n + 1) : ℤ)

def fibBinom : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | m + 1, k + 1 => Nat.fib k * fibBinom m (k + 1) + Nat.fib (m + 1 - k) * fibBinom m k

def coeffA (n k : ℕ) : ℤ :=
  (-1) ^ (k * (k + 1) / 2) * (fibBinom n k : ℤ) * (fibBinom (2 * n - k) n : ℤ)

def prodFib (n : ℕ) : ℕ :=
  ∏ i ∈ Finset.range n, Nat.fib (i + 1)

def seqA (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), coeffA n k

def intP (n : ℕ) : ℤ :=
  (prodFib n : ℤ) * seqA n

def intQ (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1),
    coeffA n k * ∑ j ∈ Finset.range (n - k), ∏ i ∈ (Finset.range n).erase j, (Nat.fib (i + 1) : ℤ)

noncomputable def psi : ℝ :=
  ∑' k : ℕ, (1 : ℝ) / (Nat.fib k : ℝ)

noncomputable def tailTerm (n s : ℕ) : ℝ :=
  (∏ j ∈ Finset.range n, (Nat.fib (s + j + 1) : ℝ)) /
    (∏ j ∈ Finset.range (n + 1), (Nat.fib (n + 1 + s + j) : ℝ))

-- === Part 1: Signed Fibonacci numbers, d'Ocagne injectivity, and Fibonomial product formula ===

lemma zfib_ofNat (n : ℕ) : zfib (n : ℤ) = (Nat.fib n : ℤ) := rfl

private lemma fib_succ_pos (k : ℕ) : 0 < Nat.fib (k + 1) := by
  have h1 : Nat.fib 1 ≤ Nat.fib (k + 1) := Nat.fib_mono (by omega)
  rw [Nat.fib_one] at h1
  omega

lemma zfib_add_two (m : ℤ) : zfib (m + 2) = zfib (m + 1) + zfib m := by
  cases m with
  | ofNat n =>
    have h0 : Int.ofNat n = ((n : ℕ) : ℤ) := rfl
    have h1 : Int.ofNat n + 1 = ((n + 1 : ℕ) : ℤ) := by omega
    have h2 : Int.ofNat n + 2 = ((n + 2 : ℕ) : ℤ) := by omega
    rw [h2, h1, h0, zfib_ofNat, zfib_ofNat, zfib_ofNat, Nat.fib_add_two]
    push_cast
    ring
  | negSucc k =>
    rcases k with _ | _ | k
    · rfl
    · rfl
    · have h2 : Int.negSucc (k + 2) + 2 = Int.negSucc k := by omega
      have h1 : Int.negSucc (k + 2) + 1 = Int.negSucc (k + 1) := by omega
      rw [h2, h1]
      dsimp [zfib]
      have hf : Nat.fib (k + 2 + 1) = Nat.fib (k + 1) + Nat.fib (k + 1 + 1) := Nat.fib_add_two
      rw [hf, pow_succ (-1 : ℤ) (k + 1), pow_succ (-1 : ℤ) k]
      push_cast
      ring

lemma zfib_shift_linear (m c : ℤ) :
    zfib (m + c) = zfib (c - 1) * zfib (m + 2) + zfib (c - 2) * zfib (m + 1) := by
  let P : ℤ → Prop := fun x =>
    zfib (m + x) = zfib (x - 1) * zfib (m + 2) + zfib (x - 2) * zfib (m + 1)
  have h0 : P 0 := by
    dsimp [P]
    have hm := zfib_add_two m
    have hf1 : zfib (-1) = 1 := rfl
    have hf2 : zfib (-2) = -1 := rfl
    rw [add_zero, hf1, hf2]
    linarith
  have h1 : P 1 := by
    dsimp [P]
    have hf1 : zfib 0 = 0 := rfl
    have hf2 : zfib (-1) = 1 := rfl
    rw [hf1, hf2]
    ring
  have hstep_up : ∀ x : ℤ, P x → P (x + 1) → P (x + 2) := by
    intro x hx hx1
    dsimp [P] at hx hx1 ⊢
    have ha : zfib (m + (x + 2)) = zfib (m + (x + 1)) + zfib (m + x) := by
      have h := zfib_add_two (m + x)
      have e1 : m + x + 2 = m + (x + 2) := by omega
      have e2 : m + x + 1 = m + (x + 1) := by omega
      rw [e1, e2] at h
      exact h
    have hb : zfib (x + 2 - 1) = zfib (x + 1 - 1) + zfib (x - 1) := by
      have h := zfib_add_two (x - 1)
      have e1 : x - 1 + 2 = x + 2 - 1 := by omega
      have e2 : x - 1 + 1 = x + 1 - 1 := by omega
      rw [e1, e2] at h
      exact h
    have hc : zfib (x + 2 - 2) = zfib (x + 1 - 2) + zfib (x - 2) := by
      have h := zfib_add_two (x - 2)
      have e1 : x - 2 + 2 = x + 2 - 2 := by omega
      have e2 : x - 2 + 1 = x + 1 - 2 := by omega
      rw [e1, e2] at h
      exact h
    rw [ha, hx, hx1, hb, hc]
    ring
  have hstep_down : ∀ x : ℤ, P (x + 1) → P (x + 2) → P x := by
    intro x hx1 hx2
    dsimp [P] at hx1 hx2 ⊢
    have ha : zfib (m + x) = zfib (m + (x + 2)) - zfib (m + (x + 1)) := by
      have h := zfib_add_two (m + x)
      have e1 : m + x + 2 = m + (x + 2) := by omega
      have e2 : m + x + 1 = m + (x + 1) := by omega
      rw [e1, e2] at h
      linarith
    have hb : zfib (x - 1) = zfib (x + 2 - 1) - zfib (x + 1 - 1) := by
      have h := zfib_add_two (x - 1)
      have e1 : x - 1 + 2 = x + 2 - 1 := by omega
      have e2 : x - 1 + 1 = x + 1 - 1 := by omega
      rw [e1, e2] at h
      linarith
    have hc : zfib (x - 2) = zfib (x + 2 - 2) - zfib (x + 1 - 2) := by
      have h := zfib_add_two (x - 2)
      have e1 : x - 2 + 2 = x + 2 - 2 := by omega
      have e2 : x - 2 + 1 = x + 1 - 2 := by omega
      rw [e1, e2] at h
      linarith
    rw [ha, hx1, hx2, hb, hc]
    ring
  have hnat : ∀ n : ℕ, P (n : ℤ) ∧ P ((n : ℤ) + 1) := by
    intro n
    induction n with
    | zero =>
      simpa using And.intro h0 h1
    | succ n ih =>
      have e1 : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by omega
      have e2 : (n : ℤ) + 1 + 1 = (n : ℤ) + 2 := by omega
      rw [e1, e2]
      exact ⟨ih.2, hstep_up (n : ℤ) ih.1 ih.2⟩
  have hneg : ∀ n : ℕ, P (-(n : ℤ)) ∧ P (-(n : ℤ) + 1) := by
    intro n
    induction n with
    | zero =>
      simpa using And.intro h0 h1
    | succ n ih =>
      have e1 : (-((n + 1 : ℕ) : ℤ)) + 1 = -(n : ℤ) := by omega
      have e2 : (-((n + 1 : ℕ) : ℤ)) + 2 = -(n : ℤ) + 1 := by omega
      have hprev : P (-((n + 1 : ℕ) : ℤ)) := by
        apply hstep_down (-((n + 1 : ℕ) : ℤ))
        · rw [e1]; exact ih.1
        · rw [e2]; exact ih.2
      exact ⟨hprev, by rw [e1]; exact ih.1⟩
  cases c with
  | ofNat n =>
    exact (hnat n).1
  | negSucc n =>
    have e : Int.negSucc n = -((n + 1 : ℕ) : ℤ) := by omega
    rw [e]
    exact (hneg (n + 1)).1

private lemma fib_det_ne_zero :
    ∀ r s : ℕ, r < s →
      (Nat.fib (r + 2) : ℤ) * (Nat.fib (s + 1) : ℤ) -
        (Nat.fib (r + 1) : ℤ) * (Nat.fib (s + 2) : ℤ) ≠ 0 := by
  intro r
  induction r with
  | zero =>
    intro s hs
    rcases s with _ | t
    · omega
    · have hpos : 0 < Nat.fib (t + 1) := Nat.fib_pos.mpr (Nat.succ_pos t)
      have hfib : Nat.fib (t + 1 + 2) = Nat.fib (t + 1) + Nat.fib (t + 1 + 1) := Nat.fib_add_two
      have hf1 : Nat.fib 1 = 1 := rfl
      have hf2 : Nat.fib 2 = 1 := rfl
      simp only [Nat.zero_add, hf1, hf2, hfib]
      push_cast
      omega
  | succ r ih =>
    intro s hs
    rcases s with _ | s'
    · omega
    · have hrs : r < s' := by omega
      have h1 := ih s' hrs
      have hfr : Nat.fib (r + 1 + 2) = Nat.fib (r + 1) + Nat.fib (r + 1 + 1) := Nat.fib_add_two
      have hfs : Nat.fib (s' + 1 + 2) = Nat.fib (s' + 1) + Nat.fib (s' + 1 + 1) := Nat.fib_add_two
      rw [hfr, hfs]
      push_cast
      have er : r + 1 + 1 = r + 2 := rfl
      have es : s' + 1 + 1 = s' + 2 := rfl
      rw [er, es]
      intro heq
      apply h1
      linarith

lemma fib_ratio_inj {r s : ℕ} (h : r < s) :
    (Nat.fib (r + 2) : ℚ) / (Nat.fib (r + 1) : ℚ) ≠
      (Nat.fib (s + 2) : ℚ) / (Nat.fib (s + 1) : ℚ) := by
  have hr_pos : (0 : ℚ) < (Nat.fib (r + 1) : ℚ) := by
    exact_mod_cast Nat.fib_pos.mpr (Nat.succ_pos r)
  have hs_pos : (0 : ℚ) < (Nat.fib (s + 1) : ℚ) := by
    exact_mod_cast Nat.fib_pos.mpr (Nat.succ_pos s)
  rw [ne_eq, div_eq_div_iff (ne_of_gt hr_pos) (ne_of_gt hs_pos)]
  intro heq
  have hdet : (((Nat.fib (r + 2) : ℤ) * (Nat.fib (s + 1) : ℤ) -
      (Nat.fib (r + 1) : ℤ) * (Nat.fib (s + 2) : ℤ) : ℤ) : ℚ) = 0 := by
    push_cast
    linarith
  exact fib_det_ne_zero r s h (by exact_mod_cast hdet)

lemma fibBinom_mul_prod (m k : ℕ) :
    (fibBinom m k : ℤ) * ∏ i ∈ Finset.range k, (Nat.fib (i + 1) : ℤ) =
      ∏ i ∈ Finset.range k, zfib ((m : ℤ) - (i : ℤ)) := by
  induction m generalizing k with
  | zero =>
    rcases k with _ | k
    · simp [fibBinom]
    · simp only [fibBinom, Nat.cast_zero, zero_mul]
      symm
      exact Finset.prod_eq_zero (Finset.mem_range.mpr (Nat.succ_pos k)) rfl
  | succ m ih =>
    rcases k with _ | k
    · simp [fibBinom]
    · have hlhs :
          (fibBinom (m + 1) (k + 1) : ℤ) * ∏ i ∈ Finset.range (k + 1), (Nat.fib (i + 1) : ℤ) =
            (∏ i ∈ Finset.range k, zfib ((m : ℤ) - (i : ℤ))) *
              ((Nat.fib k : ℤ) * zfib ((m : ℤ) - (k : ℤ)) +
                (Nat.fib (m + 1 - k) : ℤ) * (Nat.fib (k + 1) : ℤ)) := by
        calc (fibBinom (m + 1) (k + 1) : ℤ) * ∏ i ∈ Finset.range (k + 1), (Nat.fib (i + 1) : ℤ)
          _ = (Nat.fib k : ℤ) *
                ((fibBinom m (k + 1) : ℤ) * ∏ i ∈ Finset.range (k + 1), (Nat.fib (i + 1) : ℤ)) +
              (Nat.fib (m + 1 - k) : ℤ) * (Nat.fib (k + 1) : ℤ) *
                ((fibBinom m k : ℤ) * ∏ i ∈ Finset.range k, (Nat.fib (i + 1) : ℤ)) := by
            rw [fibBinom]
            push_cast
            rw [Finset.prod_range_succ]
            ring
          _ = (Nat.fib k : ℤ) * (∏ i ∈ Finset.range (k + 1), zfib ((m : ℤ) - (i : ℤ))) +
              (Nat.fib (m + 1 - k) : ℤ) * (Nat.fib (k + 1) : ℤ) *
                (∏ i ∈ Finset.range k, zfib ((m : ℤ) - (i : ℤ))) := by
            rw [ih (k + 1), ih k]
          _ = (∏ i ∈ Finset.range k, zfib ((m : ℤ) - (i : ℤ))) *
                ((Nat.fib k : ℤ) * zfib ((m : ℤ) - (k : ℤ)) +
                  (Nat.fib (m + 1 - k) : ℤ) * (Nat.fib (k + 1) : ℤ)) := by
            rw [Finset.prod_range_succ]
            ring
      have hrhs :
          ∏ i ∈ Finset.range (k + 1), zfib (((m + 1 : ℕ) : ℤ) - (i : ℤ)) =
            (∏ i ∈ Finset.range k, zfib ((m : ℤ) - (i : ℤ))) * zfib ((m : ℤ) + 1) := by
        rw [Finset.prod_range_succ']
        congr 1
        refine Finset.prod_congr rfl fun i _ => ?_
        congr 1
        omega
      rw [hlhs, hrhs]
      by_cases hmk : m < k
      · have hprod0 : ∏ i ∈ Finset.range k, zfib ((m : ℤ) - (i : ℤ)) = 0 :=
          Finset.prod_eq_zero (Finset.mem_range.mpr hmk) (by simp [zfib])
        rw [hprod0, zero_mul, zero_mul]
      · congr 1
        have hfk : (Nat.fib k : ℤ) = zfib (k : ℤ) := (zfib_ofNat k).symm
        have hfk1 : (Nat.fib (k + 1) : ℤ) = zfib ((k : ℤ) + 1) := by
          simpa using (zfib_ofNat (k + 1)).symm
        have hfmk : (Nat.fib (m + 1 - k) : ℤ) = zfib ((m : ℤ) + 1 - (k : ℤ)) := by
          rw [← zfib_ofNat (m + 1 - k)]
          congr 1
          omega
        rw [hfk, hfk1, hfmk]
        have hshift := zfib_shift_linear ((k : ℤ) - 1) ((m : ℤ) - (k : ℤ) + 2)
        have e1 : (k : ℤ) - 1 + ((m : ℤ) - (k : ℤ) + 2) = (m : ℤ) + 1 := by omega
        have e2 : (m : ℤ) - (k : ℤ) + 2 - 1 = (m : ℤ) + 1 - (k : ℤ) := by omega
        have e3 : (k : ℤ) - 1 + 2 = (k : ℤ) + 1 := by omega
        have e4 : (m : ℤ) - (k : ℤ) + 2 - 2 = (m : ℤ) - (k : ℤ) := by omega
        have e5 : (k : ℤ) - 1 + 1 = (k : ℤ) := by omega
        rw [e1, e2, e3, e4, e5] at hshift
        linarith

-- === Part 2: Lagrange partial-fraction identity via univariate polynomial over ℚ ===

private lemma zfib_sub_nat {m i : ℕ} (h : i ≤ m) :
    zfib ((m : ℤ) - (i : ℤ)) = (Nat.fib (m - i) : ℤ) := by
  have hcast : (m : ℤ) - (i : ℤ) = ((m - i : ℕ) : ℤ) := by omega
  rw [hcast, zfib_ofNat]

private lemma zfib_sub_shift (r t : ℕ) :
    zfib ((r : ℤ) - ((r + 1 + t : ℕ) : ℤ)) = (-1 : ℤ) ^ t * (Nat.fib (t + 1) : ℤ) := by
  have hcast : (r : ℤ) - ((r + 1 + t : ℕ) : ℤ) = Int.negSucc t := by
    rw [Int.negSucc_eq]
    omega
  rw [hcast]
  rfl

private lemma zfib_neg_sub {n r : ℕ} (hr : r ≤ n) (i : ℕ) :
    zfib ((r : ℤ) - (n : ℤ) - ((i + 1 : ℕ) : ℤ)) =
      (-1 : ℤ) ^ (n - r + i) * (Nat.fib (n - r + i + 1) : ℤ) := by
  have hcast : (r : ℤ) - (n : ℤ) - ((i + 1 : ℕ) : ℤ) = Int.negSucc (n - r + i) := by
    rw [Int.negSucc_eq]
    omega
  rw [hcast]
  rfl

private lemma erase_range_eq (n r : ℕ) (hr : r ≤ n) :
    (Finset.range (n + 1)).erase r =
      Finset.range r ∪ (Finset.range (n - r)).image (fun t => r + 1 + t) := by
  ext j
  simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨hne, hlt⟩
    by_cases hj : j < r
    · exact Or.inl hj
    · right
      exact ⟨j - (r + 1), by omega, by omega⟩
  · rintro (hj | ⟨t, ht, rfl⟩) <;> omega

private lemma disjoint_range_image_shift (n r : ℕ) :
    Disjoint (Finset.range r) ((Finset.range (n - r)).image (fun t => r + 1 + t)) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [Finset.mem_range, Finset.mem_image] at hx hx'
  rcases hx' with ⟨t, _, rfl⟩
  omega

private lemma two_mul_sum_range_add (m : ℕ) :
    2 * (∑ i ∈ Finset.range m, i) + m = m * m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    linarith

private lemma even_mul_succ (r : ℕ) : Even (r * (r + 1)) := by
  rcases Nat.even_or_odd r with ⟨k, hk⟩ | ⟨k, hk⟩
  · refine ⟨k * (r + 1), ?_⟩
    nlinarith
  · refine ⟨r * (k + 1), ?_⟩
    nlinarith

private lemma neg_one_pow_eq_of_even_add {a b : ℕ} (h : Even (a + b)) :
    (-1 : ℤ) ^ a = (-1 : ℤ) ^ b := by
  have h1 : (-1 : ℤ) ^ a * (-1 : ℤ) ^ b = 1 := by
    rw [← pow_add]
    exact h.neg_one_pow
  have h2 : (-1 : ℤ) ^ b * (-1 : ℤ) ^ b = 1 := by
    rw [← pow_add, ← two_mul]
    exact (even_two_mul b).neg_one_pow
  calc
    (-1 : ℤ) ^ a = (-1 : ℤ) ^ a * ((-1 : ℤ) ^ b * (-1 : ℤ) ^ b) := by rw [h2, mul_one]
    _ = ((-1 : ℤ) ^ a * (-1 : ℤ) ^ b) * (-1 : ℤ) ^ b := by ring
    _ = (-1 : ℤ) ^ b := by rw [h1, one_mul]

lemma lagrange_eval_eq (n r : ℕ) (hr : r ≤ n) :
    coeffA n r * ∏ j ∈ (Finset.range (n + 1)).erase r, zfib ((r : ℤ) - (j : ℤ)) =
      (-1 : ℤ) ^ n * ∏ i ∈ Finset.range n, zfib ((r : ℤ) - (n : ℤ) - ((i + 1 : ℕ) : ℤ)) := by
  set P : ℤ := ∏ i ∈ Finset.range n, (Nat.fib (i + 1) : ℤ)
  have hP : P ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i _
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt (fib_succ_pos i))
  apply mul_right_cancel₀ hP
  have hLeftPart :
      ∏ j ∈ Finset.range r, zfib ((r : ℤ) - (j : ℤ)) =
        ∏ i ∈ Finset.range r, (Nat.fib (i + 1) : ℤ) := by
    rw [← Finset.prod_range_reflect (fun i => (Nat.fib (i + 1) : ℤ)) r]
    refine Finset.prod_congr rfl fun j hj => ?_
    have hjlt : j < r := Finset.mem_range.mp hj
    rw [zfib_sub_nat (Nat.le_of_lt hjlt)]
    congr 2
    omega
  have hRightPart :
      ∏ t ∈ Finset.range (n - r), zfib ((r : ℤ) - ((r + 1 + t : ℕ) : ℤ)) =
        (-1 : ℤ) ^ (∑ t ∈ Finset.range (n - r), t) *
          ∏ t ∈ Finset.range (n - r), (Nat.fib (t + 1) : ℤ) := by
    calc
      ∏ t ∈ Finset.range (n - r), zfib ((r : ℤ) - ((r + 1 + t : ℕ) : ℤ))
          = ∏ t ∈ Finset.range (n - r), ((-1 : ℤ) ^ t * (Nat.fib (t + 1) : ℤ)) :=
            Finset.prod_congr rfl fun t _ => zfib_sub_shift r t
      _ = (∏ t ∈ Finset.range (n - r), (-1 : ℤ) ^ t) *
            ∏ t ∈ Finset.range (n - r), (Nat.fib (t + 1) : ℤ) :=
            Finset.prod_mul_distrib
      _ = (-1 : ℤ) ^ (∑ t ∈ Finset.range (n - r), t) *
            ∏ t ∈ Finset.range (n - r), (Nat.fib (t + 1) : ℤ) := by
            rw [Finset.prod_pow_eq_pow_sum]
  have hErase :
      ∏ j ∈ (Finset.range (n + 1)).erase r, zfib ((r : ℤ) - (j : ℤ)) =
        (∏ i ∈ Finset.range r, (Nat.fib (i + 1) : ℤ)) *
          ((-1 : ℤ) ^ (∑ t ∈ Finset.range (n - r), t) *
            ∏ t ∈ Finset.range (n - r), (Nat.fib (t + 1) : ℤ)) := by
    rw [erase_range_eq n r hr, Finset.prod_union (disjoint_range_image_shift n r),
      Finset.prod_image (by intro _ _ _ _ h; dsimp only at h; omega), hLeftPart, hRightPart]
  have hB1 :
      (fibBinom n r : ℤ) * ∏ i ∈ Finset.range r, (Nat.fib (i + 1) : ℤ) =
        ∏ i ∈ Finset.range r, (Nat.fib (n - i) : ℤ) := by
    rw [fibBinom_mul_prod]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hilt : i < r := Finset.mem_range.mp hi
    exact zfib_sub_nat (by omega)
  have hB2 :
      (fibBinom (2 * n - r) n : ℤ) * P =
        ∏ i ∈ Finset.range n, (Nat.fib (2 * n - r - i) : ℤ) := by
    rw [fibBinom_mul_prod]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hilt : i < n := Finset.mem_range.mp hi
    exact zfib_sub_nat (by omega)
  have hRHSprod :
      ∏ i ∈ Finset.range n, zfib ((r : ℤ) - (n : ℤ) - ((i + 1 : ℕ) : ℤ)) =
        (-1 : ℤ) ^ (∑ i ∈ Finset.range n, (n - r + i)) *
          ∏ i ∈ Finset.range n, (Nat.fib (2 * n - r - i) : ℤ) := by
    calc
      ∏ i ∈ Finset.range n, zfib ((r : ℤ) - (n : ℤ) - ((i + 1 : ℕ) : ℤ))
          = ∏ i ∈ Finset.range n,
              ((-1 : ℤ) ^ (n - r + i) * (Nat.fib (n - r + i + 1) : ℤ)) :=
            Finset.prod_congr rfl fun i _ => zfib_neg_sub hr i
      _ = (∏ i ∈ Finset.range n, (-1 : ℤ) ^ (n - r + i)) *
            ∏ i ∈ Finset.range n, (Nat.fib (n - r + i + 1) : ℤ) :=
            Finset.prod_mul_distrib
      _ = (-1 : ℤ) ^ (∑ i ∈ Finset.range n, (n - r + i)) *
            ∏ i ∈ Finset.range n, (Nat.fib (2 * n - r - i) : ℤ) := by
            rw [Finset.prod_pow_eq_pow_sum]
            congr 1
            rw [← Finset.prod_range_reflect (fun i => (Nat.fib (n - r + i + 1) : ℤ)) n]
            refine Finset.prod_congr rfl fun i hi => ?_
            have hilt : i < n := Finset.mem_range.mp hi
            congr 2
            omega
  have hPsplit :
      P = (∏ t ∈ Finset.range (n - r), (Nat.fib (t + 1) : ℤ)) *
            ∏ i ∈ Finset.range r, (Nat.fib (n - i) : ℤ) := by
    have hn : n = (n - r) + r := by omega
    calc
      P = ∏ i ∈ Finset.range ((n - r) + r), (Nat.fib (i + 1) : ℤ) := by
          simp only [P, ← hn]
      _ = (∏ t ∈ Finset.range (n - r), (Nat.fib (t + 1) : ℤ)) *
            ∏ u ∈ Finset.range r, (Nat.fib (n - r + u + 1) : ℤ) := by
          rw [Finset.prod_range_add]
      _ = (∏ t ∈ Finset.range (n - r), (Nat.fib (t + 1) : ℤ)) *
            ∏ i ∈ Finset.range r, (Nat.fib (n - i) : ℤ) := by
          congr 1
          rw [← Finset.prod_range_reflect (fun u => (Nat.fib (n - r + u + 1) : ℤ)) r]
          refine Finset.prod_congr rfl fun i hi => ?_
          have hilt : i < r := Finset.mem_range.mp hi
          congr 2
          omega
  have hSign :
      (-1 : ℤ) ^ (r * (r + 1) / 2 + ∑ t ∈ Finset.range (n - r), t) =
        (-1 : ℤ) ^ (n + ∑ i ∈ Finset.range n, (n - r + i)) := by
    apply neg_one_pow_eq_of_even_add
    set d : ℕ := n - r
    have hnd : n = r + d := by omega
    have hsumR : ∑ i ∈ Finset.range n, (d + i) = n * d + ∑ i ∈ Finset.range n, i := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
    have hSd := two_mul_sum_range_add d
    have hSn := two_mul_sum_range_add n
    rcases even_mul_succ r with ⟨k, hk⟩
    have hhalf : 2 * (r * (r + 1) / 2) = r * (r + 1) := by omega
    refine ⟨k + d * (r + d), ?_⟩
    rw [hsumR]
    nlinarith
  calc
    coeffA n r * (∏ j ∈ (Finset.range (n + 1)).erase r, zfib ((r : ℤ) - (j : ℤ))) * P
        = (-1 : ℤ) ^ (r * (r + 1) / 2 + ∑ t ∈ Finset.range (n - r), t) *
            ((fibBinom n r : ℤ) * ∏ i ∈ Finset.range r, (Nat.fib (i + 1) : ℤ)) *
            ((fibBinom (2 * n - r) n : ℤ) * P) *
            ∏ t ∈ Finset.range (n - r), (Nat.fib (t + 1) : ℤ) := by
          rw [coeffA, hErase, pow_add]
          ring
    _ = (-1 : ℤ) ^ (n + ∑ i ∈ Finset.range n, (n - r + i)) *
          (∏ i ∈ Finset.range r, (Nat.fib (n - i) : ℤ)) *
          (∏ i ∈ Finset.range n, (Nat.fib (2 * n - r - i) : ℤ)) *
          ∏ t ∈ Finset.range (n - r), (Nat.fib (t + 1) : ℤ) := by
          rw [hSign, hB1, hB2]
    _ = (-1 : ℤ) ^ n *
          (∏ i ∈ Finset.range n, zfib ((r : ℤ) - (n : ℤ) - ((i + 1 : ℕ) : ℤ))) * P := by
          rw [hRHSprod, hPsplit, pow_add]
          ring

private noncomputable def linForm (c : ℤ) : Polynomial ℚ :=
  Polynomial.C (zfib (c - 1) : ℚ) * Polynomial.X + Polynomial.C (zfib (c - 2) : ℚ)

private noncomputable def polyDiff (n : ℕ) : Polynomial ℚ :=
  (∑ k ∈ Finset.range (n + 1),
    Polynomial.C (coeffA n k : ℚ) *
      ∏ j ∈ (Finset.range (n + 1)).erase k, linForm (-(j : ℤ))) -
  Polynomial.C ((-1 : ℚ) ^ n) *
    ∏ i ∈ Finset.range n, linForm (-(n : ℤ) - ((i + 1 : ℕ) : ℤ))

private noncomputable def fibRatio (y : ℕ) : ℚ :=
  (Nat.fib (y + 2) : ℚ) / (Nat.fib (y + 1) : ℚ)

private lemma natDegree_linForm_le (c : ℤ) : (linForm c).natDegree ≤ 1 := by
  unfold linForm
  refine le_trans (Polynomial.natDegree_add_le _ _) ?_
  refine max_le ?_ ?_
  · exact le_trans (Polynomial.natDegree_C_mul_le _ _) (by simp)
  · simp

private lemma natDegree_prod_linForm_le {α : Type*} (S : Finset α) (f : α → ℤ) :
    (∏ a ∈ S, linForm (f a)).natDegree ≤ S.card := by
  refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
  calc
    ∑ a ∈ S, (linForm (f a)).natDegree ≤ ∑ _a ∈ S, 1 :=
      Finset.sum_le_sum fun a _ => natDegree_linForm_le (f a)
    _ = S.card := by simp

private lemma natDegree_polyDiff_le (n : ℕ) : (polyDiff n).natDegree ≤ n := by
  unfold polyDiff
  refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
  refine max_le ?_ ?_
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
    refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    refine le_trans (natDegree_prod_linForm_le _ _) ?_
    rw [Finset.card_erase_of_mem hk, Finset.card_range]
    omega
  · refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    refine le_trans (natDegree_prod_linForm_le _ _) ?_
    rw [Finset.card_range]

private lemma fib_mul_eval_linForm (y : ℕ) (c : ℤ) :
    (Nat.fib (y + 1) : ℚ) * (linForm c).eval (fibRatio y) = (zfib ((y : ℤ) + c) : ℚ) := by
  have hY : (Nat.fib (y + 1) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (fib_succ_pos y))
  have hshift := congrArg (Int.cast (R := ℚ)) (zfib_shift_linear (y : ℤ) c)
  have h1 : zfib ((y : ℤ) + 1) = (Nat.fib (y + 1) : ℤ) := by
    have : (y : ℤ) + 1 = ((y + 1 : ℕ) : ℤ) := by omega
    rw [this, zfib_ofNat]
  have h2 : zfib ((y : ℤ) + 2) = (Nat.fib (y + 2) : ℤ) := by
    have : (y : ℤ) + 2 = ((y + 2 : ℕ) : ℤ) := by omega
    rw [this, zfib_ofNat]
  rw [h1, h2] at hshift
  push_cast at hshift
  rw [hshift]
  unfold linForm fibRatio
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  field_simp [hY]

private lemma fib_pow_mul_eval_prod_linForm {α : Type*} (y n : ℕ) (S : Finset α)
    (hcard : S.card = n) (f : α → ℤ) :
    (Nat.fib (y + 1) : ℚ) ^ n * (∏ a ∈ S, linForm (f a)).eval (fibRatio y) =
      ∏ a ∈ S, (zfib ((y : ℤ) + f a) : ℚ) := by
  rw [Polynomial.eval_prod]
  have hpow : (Nat.fib (y + 1) : ℚ) ^ n = ∏ _a ∈ S, (Nat.fib (y + 1) : ℚ) := by
    rw [Finset.prod_const, hcard]
  rw [hpow, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun a _ => fib_mul_eval_linForm y (f a)

private lemma fib_pow_mul_eval_polyDiff (n y : ℕ) :
    (Nat.fib (y + 1) : ℚ) ^ n * (polyDiff n).eval (fibRatio y) =
      (∑ k ∈ Finset.range (n + 1),
        (coeffA n k : ℚ) *
          ∏ j ∈ (Finset.range (n + 1)).erase k, (zfib ((y : ℤ) - (j : ℤ)) : ℚ)) -
      (-1 : ℚ) ^ n *
        ∏ i ∈ Finset.range n, (zfib ((y : ℤ) - (n : ℤ) - ((i + 1 : ℕ) : ℤ)) : ℚ) := by
  unfold polyDiff
  rw [Polynomial.eval_sub, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    mul_sub, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C]
    have hcard : ((Finset.range (n + 1)).erase k).card = n := by
      rw [Finset.card_erase_of_mem hk, Finset.card_range]
      omega
    calc
      (Nat.fib (y + 1) : ℚ) ^ n *
          ((coeffA n k : ℚ) *
            (∏ j ∈ (Finset.range (n + 1)).erase k, linForm (-(j : ℤ))).eval (fibRatio y))
          = (coeffA n k : ℚ) *
              ((Nat.fib (y + 1) : ℚ) ^ n *
                (∏ j ∈ (Finset.range (n + 1)).erase k, linForm (-(j : ℤ))).eval (fibRatio y)) := by
            ring
      _ = (coeffA n k : ℚ) *
            ∏ j ∈ (Finset.range (n + 1)).erase k, (zfib ((y : ℤ) + -(j : ℤ)) : ℚ) := by
            rw [fib_pow_mul_eval_prod_linForm y n _ hcard]
      _ = (coeffA n k : ℚ) *
            ∏ j ∈ (Finset.range (n + 1)).erase k, (zfib ((y : ℤ) - (j : ℤ)) : ℚ) := by
            congr 1
  · calc
      (Nat.fib (y + 1) : ℚ) ^ n *
          ((-1 : ℚ) ^ n *
            (∏ i ∈ Finset.range n, linForm (-(n : ℤ) - ((i + 1 : ℕ) : ℤ))).eval (fibRatio y))
          = (-1 : ℚ) ^ n *
              ((Nat.fib (y + 1) : ℚ) ^ n *
                (∏ i ∈ Finset.range n, linForm (-(n : ℤ) - ((i + 1 : ℕ) : ℤ))).eval (fibRatio y)) := by
            ring
      _ = (-1 : ℚ) ^ n *
            ∏ i ∈ Finset.range n, (zfib ((y : ℤ) + (-(n : ℤ) - ((i + 1 : ℕ) : ℤ))) : ℚ) := by
            rw [fib_pow_mul_eval_prod_linForm y n _ (Finset.card_range n)]
      _ = (-1 : ℚ) ^ n *
            ∏ i ∈ Finset.range n, (zfib ((y : ℤ) - (n : ℤ) - ((i + 1 : ℕ) : ℤ)) : ℚ) := by
            congr 1
            refine Finset.prod_congr rfl fun i _ => ?_
            have : (y : ℤ) + (-(n : ℤ) - ((i + 1 : ℕ) : ℤ)) = (y : ℤ) - (n : ℤ) - ((i + 1 : ℕ) : ℤ) := by
              ring
            rw [this]

private lemma fibRatio_injective : Function.Injective fibRatio := by
  intro r s h
  rcases lt_trichotomy r s with hlt | heq | hgt
  · exact absurd h (fib_ratio_inj hlt)
  · exact heq
  · exact absurd h.symm (fib_ratio_inj hgt)

private lemma polyDiff_eq_zero (n : ℕ) : polyDiff n = 0 := by
  have hroots : ∀ x ∈ (Finset.range (n + 1)).image fibRatio, (polyDiff n).eval x = 0 := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨r, hr, rfl⟩
    have hrle : r ≤ n := by
      have := Finset.mem_range.mp hr
      omega
    have hYpow : (Nat.fib (r + 1) : ℚ) ^ n ≠ 0 :=
      pow_ne_zero n (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (fib_succ_pos r)))
    apply mul_left_cancel₀ hYpow
    rw [mul_zero, fib_pow_mul_eval_polyDiff]
    have hsum :
        ∑ k ∈ Finset.range (n + 1),
          (coeffA n k : ℚ) *
            ∏ j ∈ (Finset.range (n + 1)).erase k, (zfib ((r : ℤ) - (j : ℤ)) : ℚ) =
        (coeffA n r : ℚ) *
          ∏ j ∈ (Finset.range (n + 1)).erase r, (zfib ((r : ℤ) - (j : ℤ)) : ℚ) := by
      refine Finset.sum_eq_single r ?_ ?_
      · intro k _ hkr
        have hrMem : r ∈ (Finset.range (n + 1)).erase k :=
          Finset.mem_erase.mpr ⟨Ne.symm hkr, hr⟩
        have hprod0 :
            ∏ j ∈ (Finset.range (n + 1)).erase k, (zfib ((r : ℤ) - (j : ℤ)) : ℚ) = 0 := by
          refine Finset.prod_eq_zero hrMem ?_
          have h0 : zfib ((r : ℤ) - (r : ℤ)) = 0 := by
            rw [sub_self]
            rfl
          rw [h0]
          simp
        rw [hprod0, mul_zero]
      · intro hr'
        exact absurd hr hr'
    rw [hsum]
    have heval := congrArg (Int.cast (R := ℚ)) (lagrange_eval_eq n r hrle)
    push_cast at heval ⊢
    rw [heval, sub_self]
  have hdeg : (polyDiff n).natDegree < ((Finset.range (n + 1)).image fibRatio).card := by
    rw [Finset.card_image_of_injective _ fibRatio_injective, Finset.card_range]
    exact Nat.lt_succ_of_le (natDegree_polyDiff_le n)
  exact Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (polyDiff n) _ hroots hdeg

lemma lagrange_nat_identity (n m : ℕ) (hm : n + 1 ≤ m) :
    ∑ k ∈ Finset.range (n + 1),
      coeffA n k * ∏ j ∈ (Finset.range (n + 1)).erase k, (Nat.fib (m - j) : ℤ) =
      (-1 : ℤ) ^ n * ∏ i ∈ Finset.range n, (Nat.fib (m - n - (i + 1)) : ℤ) := by
  have hq := fib_pow_mul_eval_polyDiff n m
  rw [polyDiff_eq_zero, Polynomial.eval_zero, mul_zero] at hq
  have hq' :
      ∑ k ∈ Finset.range (n + 1),
        (coeffA n k : ℚ) *
          ∏ j ∈ (Finset.range (n + 1)).erase k, (zfib ((m : ℤ) - (j : ℤ)) : ℚ) =
      (-1 : ℚ) ^ n *
        ∏ i ∈ Finset.range n, (zfib ((m : ℤ) - (n : ℤ) - ((i + 1 : ℕ) : ℤ)) : ℚ) :=
    sub_eq_zero.mp hq.symm
  have hz :
      ∑ k ∈ Finset.range (n + 1),
        coeffA n k *
          ∏ j ∈ (Finset.range (n + 1)).erase k, zfib ((m : ℤ) - (j : ℤ)) =
      (-1 : ℤ) ^ n *
        ∏ i ∈ Finset.range n, zfib ((m : ℤ) - (n : ℤ) - ((i + 1 : ℕ) : ℤ)) := by
    exact_mod_cast hq'
  have hLHS :
      ∑ k ∈ Finset.range (n + 1),
        coeffA n k * ∏ j ∈ (Finset.range (n + 1)).erase k, zfib ((m : ℤ) - (j : ℤ)) =
      ∑ k ∈ Finset.range (n + 1),
        coeffA n k * ∏ j ∈ (Finset.range (n + 1)).erase k, (Nat.fib (m - j) : ℤ) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    have hjlt : j < n + 1 := Finset.mem_range.mp (Finset.mem_of_mem_erase hj)
    exact zfib_sub_nat (by omega)
  have hRHS :
      ∏ i ∈ Finset.range n, zfib ((m : ℤ) - (n : ℤ) - ((i + 1 : ℕ) : ℤ)) =
        ∏ i ∈ Finset.range n, (Nat.fib (m - n - (i + 1)) : ℤ) := by
    by_cases h2 : 2 * n + 1 ≤ m
    · refine Finset.prod_congr rfl fun i hi => ?_
      have hilt : i < n := Finset.mem_range.mp hi
      have hcast : (m : ℤ) - (n : ℤ) - ((i + 1 : ℕ) : ℤ) = ((m - n - (i + 1) : ℕ) : ℤ) := by
        omega
      rw [hcast, zfib_ofNat]
    · have hi0 : m - n - 1 ∈ Finset.range n := Finset.mem_range.mpr (by omega)
      have hz0 : ∏ i ∈ Finset.range n, zfib ((m : ℤ) - (n : ℤ) - ((i + 1 : ℕ) : ℤ)) = 0 := by
        refine Finset.prod_eq_zero hi0 ?_
        have hzero : (m : ℤ) - (n : ℤ) - ((m - n - 1 + 1 : ℕ) : ℤ) = 0 := by omega
        rw [hzero]
        rfl
      have hn0 : ∏ i ∈ Finset.range n, (Nat.fib (m - n - (i + 1)) : ℤ) = 0 := by
        refine Finset.prod_eq_zero hi0 ?_
        have hzero : m - n - (m - n - 1 + 1) = 0 := by omega
        rw [hzero]
        simp
      rw [hz0, hn0]
  rw [← hLHS, hz, hRHS]

private lemma lagrange_real_div (n m : ℕ) (hm : n + 1 ≤ m) :
    ∑ k ∈ Finset.range (n + 1), (coeffA n k : ℝ) / (Nat.fib (m - k) : ℝ) =
      ((-1 : ℝ) ^ n * ∏ i ∈ Finset.range n, (Nat.fib (m - n - (i + 1)) : ℝ)) /
        ∏ j ∈ Finset.range (n + 1), (Nat.fib (m - j) : ℝ) := by
  set D : ℝ := ∏ j ∈ Finset.range (n + 1), (Nat.fib (m - j) : ℝ)
  have hfib_ne : ∀ j ∈ Finset.range (n + 1), (Nat.fib (m - j) : ℝ) ≠ 0 := by
    intro j hj
    have hjlt : j < n + 1 := Finset.mem_range.mp hj
    have hpos : 0 < Nat.fib (m - j) := by
      have hsub : m - j = (m - j - 1) + 1 := by omega
      rw [hsub]
      exact fib_succ_pos (m - j - 1)
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt hpos)
  have hD : D ≠ 0 := Finset.prod_ne_zero_iff.mpr hfib_ne
  have hterm :
      ∀ k ∈ Finset.range (n + 1),
        (coeffA n k : ℝ) / (Nat.fib (m - k) : ℝ) =
          ((coeffA n k : ℝ) *
            ∏ j ∈ (Finset.range (n + 1)).erase k, (Nat.fib (m - j) : ℝ)) / D := by
    intro k hk
    have hmul :
        (Nat.fib (m - k) : ℝ) *
          ∏ j ∈ (Finset.range (n + 1)).erase k, (Nat.fib (m - j) : ℝ) = D :=
      Finset.mul_prod_erase (Finset.range (n + 1)) (fun j => (Nat.fib (m - j) : ℝ)) hk
    rw [div_eq_div_iff (hfib_ne k hk) hD]
    calc
      (coeffA n k : ℝ) * D
          = (coeffA n k : ℝ) *
              ((Nat.fib (m - k) : ℝ) *
                ∏ j ∈ (Finset.range (n + 1)).erase k, (Nat.fib (m - j) : ℝ)) := by
            rw [hmul]
      _ = (coeffA n k : ℝ) *
            (∏ j ∈ (Finset.range (n + 1)).erase k, (Nat.fib (m - j) : ℝ)) *
            (Nat.fib (m - k) : ℝ) := by
            ring
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div]
  have hr := congrArg (Int.cast (R := ℝ)) (lagrange_nat_identity n m hm)
  push_cast at hr
  rw [hr]

lemma pade_ortho_zero (n d : ℕ) (hd1 : 1 ≤ d) (hd2 : d ≤ n) :
    ∑ k ∈ Finset.range (n + 1), (coeffA n k : ℝ) / (Nat.fib (n + d - k) : ℝ) = 0 := by
  rw [lagrange_real_div n (n + d) (by omega)]
  have hprod0 : ∏ i ∈ Finset.range n, (Nat.fib (n + d - n - (i + 1)) : ℝ) = 0 := by
    refine Finset.prod_eq_zero (Finset.mem_range.mpr (by omega : d - 1 < n)) ?_
    have hzero : n + d - n - (d - 1 + 1) = 0 := by omega
    rw [hzero]
    simp
  rw [hprod0, mul_zero, zero_div]

lemma pade_tail_eq (n s : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (coeffA n k : ℝ) / (Nat.fib (2 * n + 1 + s - k) : ℝ) =
      (-1 : ℝ) ^ n * tailTerm n s := by
  rw [lagrange_real_div n (2 * n + 1 + s) (by omega), tailTerm, mul_div_assoc]
  congr 2
  · rw [← Finset.prod_range_reflect (fun j => (Nat.fib (s + j + 1) : ℝ)) n]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hilt : i < n := Finset.mem_range.mp hi
    congr 2
    omega
  · rw [← Finset.prod_range_reflect (fun j => (Nat.fib (n + 1 + s + j) : ℝ)) (n + 1)]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hilt : i < n + 1 := Finset.mem_range.mp hi
    congr 2
    omega

-- === Part 3: Series convergence, prefix splitting, positivity, and upper bound ===

private lemma fib_ge_three_halves_pow :
    ∀ k : ℕ, (3 / 2 : ℝ) ^ k ≤ (Nat.fib (k + 2) : ℝ) ∧
      (3 / 2 : ℝ) ^ (k + 1) ≤ (Nat.fib (k + 3) : ℝ) := by
  intro k
  induction k with
  | zero =>
    have h2 : Nat.fib 2 = 1 := Nat.fib_two
    have h3 : Nat.fib 3 = 2 := by
      rw [show (3 : ℕ) = 1 + 2 from rfl, Nat.fib_add_two, Nat.fib_one, Nat.fib_two]
    simp only [Nat.zero_add]
    rw [h2, h3]
    push_cast
    constructor <;> norm_num
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    have hfib : Nat.fib (k + 1 + 3) = Nat.fib (k + 2) + Nat.fib (k + 3) := by
      rw [show k + 1 + 3 = (k + 2) + 2 by omega, Nat.fib_add_two]
    rw [hfib]
    push_cast
    have hp0 : (0 : ℝ) ≤ (3 / 2 : ℝ) ^ k := by positivity
    have hpow2 : (3 / 2 : ℝ) ^ (k + 1 + 1) = (9 / 4 : ℝ) * (3 / 2 : ℝ) ^ k := by ring
    have hpow1 : (3 / 2 : ℝ) ^ (k + 1) = (3 / 2 : ℝ) * (3 / 2 : ℝ) ^ k := by ring
    linarith [ih.1, ih.2]

lemma summable_inv_fib : Summable (fun k : ℕ => (1 : ℝ) / (Nat.fib k : ℝ)) := by
  have hgeom : Summable (fun k : ℕ => (2 / 3 : ℝ) ^ k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hshift : Summable (fun k : ℕ => (1 : ℝ) / (Nat.fib (k + 2) : ℝ)) := by
    refine hgeom.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    have hfg : (3 / 2 : ℝ) ^ k ≤ (Nat.fib (k + 2) : ℝ) := (fib_ge_three_halves_pow k).1
    have hp : (0 : ℝ) < (3 / 2 : ℝ) ^ k := by positivity
    calc
      (1 : ℝ) / (Nat.fib (k + 2) : ℝ) ≤ 1 / (3 / 2 : ℝ) ^ k :=
        one_div_le_one_div_of_le hp hfg
      _ = (2 / 3 : ℝ) ^ k := by
        rw [one_div, ← inv_pow]
        congr 1
        norm_num
  exact (summable_nat_add_iff (f := fun k : ℕ => (1 : ℝ) / (Nat.fib k : ℝ)) 2).mp hshift

private lemma summable_inv_fib_succ : Summable (fun j : ℕ => (1 : ℝ) / (Nat.fib (j + 1) : ℝ)) :=
  (summable_nat_add_iff (f := fun k : ℕ => (1 : ℝ) / (Nat.fib k : ℝ)) 1).mpr summable_inv_fib

private lemma psi_eq_tsum_succ : psi = ∑' j : ℕ, (1 : ℝ) / (Nat.fib (j + 1) : ℝ) := by
  unfold psi
  rw [← summable_inv_fib.sum_add_tsum_nat_add 1, Finset.sum_range_one, Nat.fib_zero,
    Nat.cast_zero, div_zero, zero_add]

private lemma prodFib_mul_inv_fib_eq_erase (n j : ℕ) (hj : j ∈ Finset.range n) :
    (prodFib n : ℝ) * ((1 : ℝ) / (Nat.fib (j + 1) : ℝ)) =
      ∏ i ∈ (Finset.range n).erase j, (Nat.fib (i + 1) : ℝ) := by
  have hmul :
      (Nat.fib (j + 1) : ℝ) * ∏ i ∈ (Finset.range n).erase j, (Nat.fib (i + 1) : ℝ) =
        (prodFib n : ℝ) := by
    unfold prodFib
    push_cast
    exact Finset.mul_prod_erase (Finset.range n) (fun i => (Nat.fib (i + 1) : ℝ)) hj
  have hne : (Nat.fib (j + 1) : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (fib_succ_pos j))
  rw [← hmul]
  field_simp

lemma linear_form_eq_tail (n : ℕ) :
    (intP n : ℝ) * psi - (intQ n : ℝ) =
      (-1 : ℝ) ^ n * (prodFib n : ℝ) * ∑' s : ℕ, tailTerm n s := by
  have hsum1 : Summable (fun j : ℕ => (1 : ℝ) / (Nat.fib (j + 1) : ℝ)) :=
    summable_inv_fib_succ
  have hP :
      (intP n : ℝ) * psi =
        ∑ k ∈ Finset.range (n + 1), (coeffA n k : ℝ) * ((prodFib n : ℝ) * psi) := by
    unfold intP seqA
    push_cast
    rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  have hQ :
      (intQ n : ℝ) =
        ∑ k ∈ Finset.range (n + 1),
          (coeffA n k : ℝ) *
            ((prodFib n : ℝ) * ∑ j ∈ Finset.range (n - k), (1 : ℝ) / (Nat.fib (j + 1) : ℝ)) := by
    unfold intQ
    push_cast
    refine Finset.sum_congr rfl (fun k _ => ?_)
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hjn : j ∈ Finset.range n := by
      rw [Finset.mem_range] at hj ⊢
      omega
    exact (prodFib_mul_inv_fib_eq_erase n j hjn).symm
  have hdiff :
      (intP n : ℝ) * psi - (intQ n : ℝ) =
        (prodFib n : ℝ) *
          ∑ k ∈ Finset.range (n + 1),
            ∑' d : ℕ, (coeffA n k : ℝ) / (Nat.fib (n + (d + 1) - k) : ℝ) := by
    rw [hP, hQ, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hkn : k ≤ n := by
      rw [Finset.mem_range] at hk
      omega
    have hsplit :
        psi - ∑ j ∈ Finset.range (n - k), (1 : ℝ) / (Nat.fib (j + 1) : ℝ) =
          ∑' d : ℕ, (1 : ℝ) / (Nat.fib (n + (d + 1) - k) : ℝ) := by
      have h1 :
          psi =
            (∑ j ∈ Finset.range (n - k), (1 : ℝ) / (Nat.fib (j + 1) : ℝ)) +
              ∑' d : ℕ, (1 : ℝ) / (Nat.fib (d + (n - k) + 1) : ℝ) := by
        rw [psi_eq_tsum_succ, ← hsum1.sum_add_tsum_nat_add (n - k)]
      have h2 :
          (∑' d : ℕ, (1 : ℝ) / (Nat.fib (d + (n - k) + 1) : ℝ)) =
            ∑' d : ℕ, (1 : ℝ) / (Nat.fib (n + (d + 1) - k) : ℝ) := by
        refine tsum_congr (fun d => ?_)
        rw [show d + (n - k) + 1 = n + (d + 1) - k by omega]
      linarith
    have hterm :
        (coeffA n k : ℝ) * ((prodFib n : ℝ) * psi) -
            (coeffA n k : ℝ) *
              ((prodFib n : ℝ) * ∑ j ∈ Finset.range (n - k), (1 : ℝ) / (Nat.fib (j + 1) : ℝ)) =
          (prodFib n : ℝ) *
            ((coeffA n k : ℝ) *
              (psi - ∑ j ∈ Finset.range (n - k), (1 : ℝ) / (Nat.fib (j + 1) : ℝ))) := by
      ring
    rw [hterm, hsplit, ← tsum_mul_left]
    congr 1
    refine tsum_congr (fun d => ?_)
    ring
  have hF_sum :
      ∀ k ∈ Finset.range (n + 1),
        Summable (fun d : ℕ => (coeffA n k : ℝ) / (Nat.fib (n + (d + 1) - k) : ℝ)) := by
    intro k hk
    have hkn : k ≤ n := by
      rw [Finset.mem_range] at hk
      omega
    have hs0 : Summable (fun d : ℕ => (1 : ℝ) / (Nat.fib (d + (n + 1 - k)) : ℝ)) :=
      (summable_nat_add_iff (f := fun j : ℕ => (1 : ℝ) / (Nat.fib j : ℝ)) (n + 1 - k)).mpr
        summable_inv_fib
    have hs1 : Summable (fun d : ℕ => (coeffA n k : ℝ) * ((1 : ℝ) / (Nat.fib (d + (n + 1 - k)) : ℝ))) :=
      hs0.mul_left (coeffA n k : ℝ)
    refine hs1.congr (fun d => ?_)
    have hidx : d + (n + 1 - k) = n + (d + 1) - k := by omega
    rw [hidx]
    ring
  rw [hdiff, ← Summable.tsum_finsetSum hF_sum]
  let g : ℕ → ℝ := fun d =>
    ∑ k ∈ Finset.range (n + 1), (coeffA n k : ℝ) / (Nat.fib (n + (d + 1) - k) : ℝ)
  have hg : Summable g := by
    have haux :
        ∀ m : ℕ, m ≤ n + 1 →
          Summable (fun d : ℕ =>
            ∑ k ∈ Finset.range m, (coeffA n k : ℝ) / (Nat.fib (n + (d + 1) - k) : ℝ)) := by
      intro m hm
      induction m with
      | zero =>
        simp only [Finset.sum_range_zero]
        exact summable_zero
      | succ m ihm =>
        simp only [Finset.sum_range_succ]
        exact (ihm (by omega)).add (hF_sum m (Finset.mem_range.mpr (by omega)))
    exact haux (n + 1) (le_refl _)
  change (prodFib n : ℝ) * ∑' d : ℕ, g d = _
  rw [← hg.sum_add_tsum_nat_add n]
  have hpref : ∑ d ∈ Finset.range n, g d = 0 := by
    refine Finset.sum_eq_zero (fun d hd => ?_)
    rw [Finset.mem_range] at hd
    exact pade_ortho_zero n (d + 1) (by omega) (by omega)
  have htail :
      (∑' s : ℕ, g (s + n)) = (-1 : ℝ) ^ n * ∑' s : ℕ, tailTerm n s := by
    have hgs : ∀ s : ℕ, g (s + n) = (-1 : ℝ) ^ n * tailTerm n s := by
      intro s
      have heq :
          g (s + n) =
            ∑ k ∈ Finset.range (n + 1), (coeffA n k : ℝ) / (Nat.fib (2 * n + 1 + s - k) : ℝ) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [show n + (s + n + 1) - k = 2 * n + 1 + s - k by omega]
      rw [heq, pade_tail_eq n s]
    rw [tsum_congr hgs, tsum_mul_left]
  rw [hpref, zero_add, htail]
  ring

private lemma fib_mul_le_pair (a : ℕ) :
    ∀ m : ℕ, Nat.fib (m + 1) * Nat.fib a ≤ Nat.fib (m + a) ∧
      Nat.fib (m + 2) * Nat.fib a ≤ Nat.fib (m + 1 + a) := by
  intro m
  induction m with
  | zero =>
    constructor
    · simp [Nat.fib_one]
    · rw [Nat.fib_two, one_mul]
      exact Nat.fib_mono (by omega)
  | succ m ih =>
    refine ⟨ih.2, ?_⟩
    have h1 : Nat.fib (m + 1 + 2) = Nat.fib (m + 1) + Nat.fib (m + 2) := Nat.fib_add_two
    have h2 : Nat.fib (m + 1 + 1 + a) = Nat.fib (m + a) + Nat.fib (m + 1 + a) := by
      rw [show m + 1 + 1 + a = (m + a) + 2 by omega, Nat.fib_add_two,
        show m + a + 1 = m + 1 + a by omega]
    rw [h1, h2, Nat.add_mul]
    exact Nat.add_le_add ih.1 ih.2

private lemma prodFib_pos (n : ℕ) : (0 : ℝ) < (prodFib n : ℝ) := by
  unfold prodFib
  push_cast
  exact Finset.prod_pos (fun i _ => Nat.cast_pos.mpr (fib_succ_pos i))

private lemma tailTerm_pos (n s : ℕ) : 0 < tailTerm n s := by
  unfold tailTerm
  refine div_pos ?_ ?_
  · exact Finset.prod_pos (fun j _ => Nat.cast_pos.mpr (fib_succ_pos (s + j)))
  · refine Finset.prod_pos (fun j _ => ?_)
    rw [show n + 1 + s + j = (n + s + j) + 1 by omega]
    exact Nat.cast_pos.mpr (fib_succ_pos (n + s + j))

private lemma prodFib_mul_tailTerm_le (n s : ℕ) (hn : 1 ≤ n) :
    (prodFib n : ℝ) * tailTerm n s ≤
      (1 / (Nat.fib (n + 2) : ℝ)) * (1 / (Nat.fib (n + 1 + s) : ℝ)) := by
  let term : ℕ → ℝ := fun j =>
    (Nat.fib (j + 1) : ℝ) * (Nat.fib (s + j + 1) : ℝ) / (Nat.fib (n + 1 + s + (j + 1)) : ℝ)
  have h_rewrite :
      (prodFib n : ℝ) * tailTerm n s =
        (∏ j ∈ Finset.range n, term j) * (1 / (Nat.fib (n + 1 + s) : ℝ)) := by
    unfold prodFib tailTerm
    push_cast
    rw [Finset.prod_range_succ' (fun j => (Nat.fib (n + 1 + s + j) : ℝ)) n]
    simp only [Nat.add_zero]
    rw [← mul_div_assoc, div_mul_eq_div_div, div_eq_mul_one_div, ← Finset.prod_mul_distrib,
      ← Finset.prod_div_distrib]
  have hterm_nonneg : ∀ j : ℕ, 0 ≤ term j := by
    intro j
    exact div_nonneg (by positivity) (by positivity)
  have hterm_bound : ∀ j : ℕ, term j ≤ (Nat.fib (j + 1) : ℝ) / (Nat.fib (n + 2) : ℝ) := by
    intro j
    have hfm : Nat.fib (n + 2) * Nat.fib (s + j + 1) ≤ Nat.fib (n + 1 + s + (j + 1)) := by
      have h0 := (fib_mul_le_pair (s + j + 1) (n + 1)).1
      rwa [show n + 1 + 1 = n + 2 by omega,
        show n + 1 + (s + j + 1) = n + 1 + s + (j + 1) by omega] at h0
    have hfmR :
        (Nat.fib (n + 2) : ℝ) * (Nat.fib (s + j + 1) : ℝ) ≤
          (Nat.fib (n + 1 + s + (j + 1)) : ℝ) := by
      exact_mod_cast hfm
    have hd1 : (0 : ℝ) < (Nat.fib (n + 1 + s + (j + 1)) : ℝ) := by
      rw [show n + 1 + s + (j + 1) = (n + 1 + s + j) + 1 by omega]
      exact Nat.cast_pos.mpr (fib_succ_pos (n + 1 + s + j))
    have hd2 : (0 : ℝ) < (Nat.fib (n + 2) : ℝ) :=
      Nat.cast_pos.mpr (fib_succ_pos (n + 1))
    rw [div_le_div_iff₀ hd1 hd2]
    have hj_nn : (0 : ℝ) ≤ (Nat.fib (j + 1) : ℝ) := by positivity
    nlinarith
  have hprod_le : (∏ j ∈ Finset.range n, term j) ≤ 1 / (Nat.fib (n + 2) : ℝ) := by
    have hrange : Finset.range n = Finset.range ((n - 1) + 1) := by
      congr 1
      omega
    rw [hrange, Finset.prod_range_succ' term (n - 1)]
    have hrest : (∏ k ∈ Finset.range (n - 1), term (k + 1)) ≤ 1 := by
      refine Finset.prod_le_one (fun k _ => hterm_nonneg (k + 1)) (fun k hk => ?_)
      rw [Finset.mem_range] at hk
      have hmono : (Nat.fib (k + 1 + 1) : ℝ) ≤ (Nat.fib (n + 2) : ℝ) := by
        exact_mod_cast Nat.fib_mono (by omega)
      have hd2 : (0 : ℝ) < (Nat.fib (n + 2) : ℝ) :=
        Nat.cast_pos.mpr (fib_succ_pos (n + 1))
      calc
        term (k + 1) ≤ (Nat.fib (k + 1 + 1) : ℝ) / (Nat.fib (n + 2) : ℝ) := hterm_bound (k + 1)
        _ ≤ 1 := (div_le_one hd2).mpr hmono
    have ht0 : term 0 ≤ 1 / (Nat.fib (n + 2) : ℝ) := by
      have hb := hterm_bound 0
      simpa [Nat.fib_one] using hb
    have ht0_nn : 0 ≤ term 0 := hterm_nonneg 0
    calc
      (∏ k ∈ Finset.range (n - 1), term (k + 1)) * term 0 ≤ 1 * term 0 :=
        mul_le_mul_of_nonneg_right hrest ht0_nn
      _ = term 0 := one_mul _
      _ ≤ 1 / (Nat.fib (n + 2) : ℝ) := ht0
  rw [h_rewrite]
  exact mul_le_mul_of_nonneg_right hprod_le (by positivity)

lemma linear_form_bounds (n : ℕ) (hn : 1 ≤ n) :
    0 < |(intP n : ℝ) * psi - (intQ n : ℝ)| ∧
      |(intP n : ℝ) * psi - (intQ n : ℝ)| ≤ psi / (Nat.fib (n + 2) : ℝ) := by
  have hshift_sum : Summable (fun s : ℕ => (1 : ℝ) / (Nat.fib (n + 1 + s) : ℝ)) := by
    have hs0 : Summable (fun s : ℕ => (1 : ℝ) / (Nat.fib (s + (n + 1)) : ℝ)) :=
      (summable_nat_add_iff (f := fun j : ℕ => (1 : ℝ) / (Nat.fib j : ℝ)) (n + 1)).mpr
        summable_inv_fib
    refine hs0.congr (fun s => ?_)
    rw [Nat.add_comm s (n + 1)]
  have hupper_sum :
      Summable (fun s : ℕ => (1 / (Nat.fib (n + 2) : ℝ)) * (1 / (Nat.fib (n + 1 + s) : ℝ))) :=
    hshift_sum.mul_left (1 / (Nat.fib (n + 2) : ℝ))
  have hprod_tail_sum : Summable (fun s : ℕ => (prodFib n : ℝ) * tailTerm n s) :=
    hupper_sum.of_nonneg_of_le
      (fun s => mul_nonneg (le_of_lt (prodFib_pos n)) (le_of_lt (tailTerm_pos n s)))
      (fun s => prodFib_mul_tailTerm_le n s hn)
  have hp_pos : (0 : ℝ) < (prodFib n : ℝ) := prodFib_pos n
  have htail_sum : Summable (tailTerm n) := by
    have hs := hprod_tail_sum.mul_left (prodFib n : ℝ)⁻¹
    refine hs.congr (fun s => ?_)
    exact inv_mul_cancel_left₀ (ne_of_gt hp_pos) (tailTerm n s)
  have htsum_pos : 0 < ∑' s : ℕ, tailTerm n s := by
    rw [← htail_sum.sum_add_tsum_nat_add 1, Finset.sum_range_one]
    have ht0 : 0 < tailTerm n 0 := tailTerm_pos n 0
    have hrest : 0 ≤ ∑' s : ℕ, tailTerm n (s + 1) :=
      tsum_nonneg (fun s => le_of_lt (tailTerm_pos n (s + 1)))
    linarith
  have habs :
      |(intP n : ℝ) * psi - (intQ n : ℝ)| = (prodFib n : ℝ) * ∑' s : ℕ, tailTerm n s := by
    rw [linear_form_eq_tail n, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_pos hp_pos, abs_of_pos htsum_pos]
  refine ⟨?_, ?_⟩
  · rw [habs]
    exact mul_pos hp_pos htsum_pos
  · rw [habs, ← tsum_mul_left]
    have hle1 :
        (∑' s : ℕ, (prodFib n : ℝ) * tailTerm n s) ≤
          ∑' s : ℕ, (1 / (Nat.fib (n + 2) : ℝ)) * (1 / (Nat.fib (n + 1 + s) : ℝ)) :=
      Summable.tsum_le_tsum (fun s => prodFib_mul_tailTerm_le n s hn) hprod_tail_sum hupper_sum
    have hsum1 : Summable (fun j : ℕ => (1 : ℝ) / (Nat.fib (j + 1) : ℝ)) :=
      summable_inv_fib_succ
    have htail_le_psi : (∑' s : ℕ, (1 : ℝ) / (Nat.fib (n + 1 + s) : ℝ)) ≤ psi := by
      have hsplit :
          psi =
            (∑ j ∈ Finset.range n, (1 : ℝ) / (Nat.fib (j + 1) : ℝ)) +
              ∑' s : ℕ, (1 : ℝ) / (Nat.fib (s + n + 1) : ℝ) := by
        rw [psi_eq_tsum_succ, ← hsum1.sum_add_tsum_nat_add n]
      have hpref_nn : 0 ≤ ∑ j ∈ Finset.range n, (1 : ℝ) / (Nat.fib (j + 1) : ℝ) :=
        Finset.sum_nonneg (fun j _ => by positivity)
      have htail_eq :
          (∑' s : ℕ, (1 : ℝ) / (Nat.fib (n + 1 + s) : ℝ)) =
            ∑' s : ℕ, (1 : ℝ) / (Nat.fib (s + n + 1) : ℝ) := by
        refine tsum_congr (fun s => ?_)
        rw [show n + 1 + s = s + n + 1 by omega]
      linarith
    calc
      (∑' s : ℕ, (prodFib n : ℝ) * tailTerm n s) ≤
          ∑' s : ℕ, (1 / (Nat.fib (n + 2) : ℝ)) * (1 / (Nat.fib (n + 1 + s) : ℝ)) := hle1
      _ = (1 / (Nat.fib (n + 2) : ℝ)) * ∑' s : ℕ, (1 : ℝ) / (Nat.fib (n + 1 + s) : ℝ) :=
          tsum_mul_left
      _ ≤ (1 / (Nat.fib (n + 2) : ℝ)) * psi :=
          mul_le_mul_of_nonneg_left htail_le_psi (by positivity)
      _ = psi / (Nat.fib (n + 2) : ℝ) := by ring

-- === Final irrationality deduction ===

theorem main_irrational : Irrational psi := by
  rintro ⟨q, hq⟩
  set p : ℤ := q.num
  set d : ℕ := q.den
  have hd_pos_nat : 0 < d := q.den_pos
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd_pos_nat
  have hpsi : psi = (p : ℝ) / (d : ℝ) := by
    rw [← hq, Rat.cast_def]
  obtain ⟨N, hN⟩ := exists_nat_gt ((d : ℝ) * psi)
  set n := N + 1
  have hn : 1 ≤ n := by omega
  obtain ⟨hpos, hub⟩ := linear_form_bounds n hn
  have hfib_ge : n + 1 ≤ Nat.fib (n + 2) := by
    have h1 : ∀ k : ℕ, k ≤ Nat.fib (k + 1) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        cases k with
        | zero => simp
        | succ k' =>
          rw [Nat.fib_add_two]
          have : 1 ≤ Nat.fib (k' + 1) := Nat.fib_pos.mpr (by omega)
          omega
    exact h1 (n + 1)
  have hfib_gt : (d : ℝ) * psi < (Nat.fib (n + 2) : ℝ) := by
    have hcast : (N : ℝ) < ((n + 1 : ℕ) : ℝ) := by
      push_cast [n]
      linarith
    have hcast2 : ((n + 1 : ℕ) : ℝ) ≤ (Nat.fib (n + 2) : ℝ) := by exact_mod_cast hfib_ge
    linarith
  set M : ℤ := intP n * p - intQ n * (d : ℤ)
  have hM_eq : (M : ℝ) = (d : ℝ) * ((intP n : ℝ) * psi - (intQ n : ℝ)) := by
    push_cast [M]
    rw [hpsi]
    have hd_ne : (d : ℝ) ≠ 0 := ne_of_gt hd_pos
    field_simp [hd_ne]
  have hM_pos : (0 : ℝ) < |(M : ℝ)| := by
    rw [hM_eq, abs_mul, abs_of_pos hd_pos]
    exact mul_pos hd_pos hpos
  have hM_lt_one : |(M : ℝ)| < 1 := by
    rw [hM_eq, abs_mul, abs_of_pos hd_pos]
    have h1 : (d : ℝ) * |(intP n : ℝ) * psi - (intQ n : ℝ)| ≤ (d : ℝ) * (psi / (Nat.fib (n + 2) : ℝ)) :=
      mul_le_mul_of_nonneg_left hub hd_pos.le
    have hfib_pos : (0 : ℝ) < (Nat.fib (n + 2) : ℝ) := by
      exact_mod_cast Nat.fib_pos.mpr (by omega)
    have h2 : (d : ℝ) * (psi / (Nat.fib (n + 2) : ℝ)) < 1 := by
      rw [← mul_div_assoc, div_lt_one hfib_pos]
      exact hfib_gt
    linarith
  have hM_int_pos : (0 : ℤ) < |M| := by exact_mod_cast hM_pos
  have hM_int_lt : |M| < (1 : ℤ) := by exact_mod_cast hM_lt_one
  omega

end OMA.Erdos267Fib

theorem OMA.solution : type_of% @Erdos267.erdos_267.variants.fibonacci_inverse_sum :=
  OMA.Erdos267Fib.main_irrational
