import FormalConjectures.Mathoverflow.«508539»

-- Problem: MathOverflow 508539
-- Upstream: formal-conjectures FormalConjectures/Mathoverflow/508539.lean:66 (declaration Mathoverflow508539.mathoverflow_508539)
-- Credit: @ronak14p (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-
Proof outline (elementary induction on the set of coordinate directions).

For a set `S` of directions and a base point `z`, the fibre `F_S(z)` is the subcube of all `x`
agreeing with `z` outside `S`; it has `N = 2 ^ #S` points.  Inside the fibre let
`a = #(A ∩ F)`, `E` the number of pairs `(x, i)` with `x ∈ A ∩ F`, `i ∈ S`, `flip i x ∉ A`, and
`V` the number of `x ∈ A ∩ F` having such an `i`.  We prove by induction on `S` the invariant

  `Q := 3 N² E - 4 (2a - N) a (N - a) ≥ 0`   and   `Q · V ≥ 12 a² (N - a)²`.

Adding a direction `j` glues two fibres with data `(a₀, E₀, V₀)`, `(a₁, E₁, V₁)`, `a₀ ≤ a₁`, and
`E ≥ E₀ + E₁ + (a₁ - a₀)`, `V ≥ V₀ + max V₁ (a₁ - a₀)`.  The invariant is preserved thanks to a
polynomial identity plus Cauchy-Schwarz.  For `S = univ`, `a = N / 2` it reads `E V ≥ N² / 4`.
-/

open Finset SimpleGraph

namespace OMA

/-! ### Real algebra -/

/-- The inductive invariant. -/
def Inv (N a E V : ℝ) : Prop :=
  4 * (2 * a - N) * a * (N - a) ≤ 3 * N ^ 2 * E ∧
    12 * a ^ 2 * (N - a) ^ 2 ≤ (3 * N ^ 2 * E - 4 * (2 * a - N) * a * (N - a)) * V

lemma cs_aux {X0 X1 V0 m k g : ℝ} (hX0 : 0 ≤ X0) (hX1 : 0 ≤ X1) (hV0 : 0 ≤ V0) (hm : 0 ≤ m)
    (h0 : k ^ 2 ≤ X0 * V0) (h1 : g ^ 2 ≤ X1 * m) :
    (k + g) ^ 2 ≤ (X0 + X1) * (V0 + m) := by
  have hc : 2 * k * g ≤ X0 * m + X1 * V0 := by
    by_contra hlt
    rw [not_le] at hlt
    have hpos : 0 ≤ X0 * m + X1 * V0 := by positivity
    have hsq : (X0 * m + X1 * V0) ^ 2 < (2 * k * g) ^ 2 := by nlinarith
    have hprod : k ^ 2 * g ^ 2 ≤ (X0 * V0) * (X1 * m) :=
      mul_le_mul h0 h1 (sq_nonneg g) (le_trans (sq_nonneg k) h0)
    nlinarith [sq_nonneg (X0 * m - X1 * V0)]
  nlinarith

lemma inv_step {N a0 E0 V0 a1 E1 V1 E V : ℝ} (_hN : 0 < N) (h0 : 0 ≤ a0) (h01 : a0 ≤ a1)
    (h1 : a1 ≤ N) (hV0 : 0 ≤ V0) (hV1 : 0 ≤ V1) (I0 : Inv N a0 E0 V0) (I1 : Inv N a1 E1 V1)
    (hE : E0 + E1 + (a1 - a0) ≤ E) (hV : V0 + V1 ≤ V) (hV' : V0 + (a1 - a0) ≤ V) :
    Inv (2 * N) (a0 + a1) E V := by
  obtain ⟨q0, r0⟩ := I0
  obtain ⟨q1, r1⟩ := I1
  set Q0 := 3 * N ^ 2 * E0 - 4 * (2 * a0 - N) * a0 * (N - a0) with hQ0
  set Q1 := 3 * N ^ 2 * E1 - 4 * (2 * a1 - N) * a1 * (N - a1) with hQ1
  have hQ0n : 0 ≤ Q0 := by rw [hQ0]; linarith
  have hQ1n : 0 ≤ Q1 := by rw [hQ1]; linarith
  have hd : 0 ≤ a1 - a0 := by linarith
  have hbr : 0 ≤ N ^ 2 + 2 * (N - a0 - a1) * (a1 - a0) := by
    nlinarith [mul_nonneg (sub_nonneg.2 h1) hd, mul_nonneg h0 (sub_nonneg.2 h1),
      sq_nonneg (N - 2 * a0), mul_nonneg h0 hd]
  set Dh := 3 * (a1 - a0) * (N ^ 2 + 2 * (N - a0 - a1) * (a1 - a0)) with hDh
  have hDhn : 0 ≤ Dh := by rw [hDh]; positivity
  set Qn := 3 * (2 * N) ^ 2 * E - 4 * (2 * (a0 + a1) - 2 * N) * (a0 + a1) * (2 * N - (a0 + a1))
    with hQn
  have hQid : Qn = 4 * Q0 + 4 * Q1 + 4 * Dh + 12 * N ^ 2 * (E - E0 - E1 - (a1 - a0)) := by
    rw [hQn, hQ0, hQ1, hDh]; ring
  have hQge : 4 * (Q0 + (Q1 + Dh)) ≤ Qn := by
    rw [hQid]
    have := mul_nonneg (sq_nonneg N) (show (0:ℝ) ≤ E - E0 - E1 - (a1 - a0) by linarith)
    linarith
  have hQnn : 0 ≤ Qn := by linarith
  refine ⟨by linarith, ?_⟩
  -- the product part
  set m := max V1 (a1 - a0) with hm
  have hmV1 : V1 ≤ m := le_max_left _ _
  have hmd : a1 - a0 ≤ m := le_max_right _ _
  have hmn : 0 ≤ m := le_trans hV1 hmV1
  have hVm : V0 + m ≤ V := by
    rcases max_cases V1 (a1 - a0) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [hm, h] <;> linarith
  set k := 12 * a0 * (N - a0) with hk
  set g := 6 * (a0 + a1) * (2 * N - (a0 + a1)) - k with hg
  have hkn : 0 ≤ k := by
    rw [hk]; exact mul_nonneg (by linarith) (by linarith)
  have hk2 : k ^ 2 ≤ (12 * Q0) * V0 := by
    have : k ^ 2 = 12 * (12 * a0 ^ 2 * (N - a0) ^ 2) := by rw [hk]; ring
    rw [this]
    have h6 : (12 * Q0) * V0 = 12 * (Q0 * V0) := by ring
    rw [h6]
    linarith
  have hg2 : g ^ 2 ≤ (12 * (Q1 + Dh)) * m := by
    have hid : 144 * a1 ^ 2 * (N - a1) ^ 2 + 12 * Dh * (a1 - a0)
        = g ^ 2 + 36 * (a1 - a0) ^ 2 * (N - (a0 + a1)) ^ 2 := by
      rw [hg, hk, hDh]; ring
    have h2 : 12 * (12 * a1 ^ 2 * (N - a1) ^ 2) ≤ 12 * (Q1 * m) := by
      have : Q1 * V1 ≤ Q1 * m := mul_le_mul_of_nonneg_left hmV1 hQ1n
      linarith
    have h3 : 12 * Dh * (a1 - a0) ≤ 12 * (Dh * m) := by
      have : Dh * (a1 - a0) ≤ Dh * m := mul_le_mul_of_nonneg_left hmd hDhn
      linarith
    have h4 : 0 ≤ 36 * (a1 - a0) ^ 2 * (N - (a0 + a1)) ^ 2 := by positivity
    have h5 : (12 * (Q1 + Dh)) * m = 12 * (Q1 * m) + 12 * (Dh * m) := by ring
    rw [h5]
    linarith
  have hcs := cs_aux (X0 := 12 * Q0) (X1 := 12 * (Q1 + Dh)) (V0 := V0) (m := m) (k := k) (g := g)
    (by positivity) (by positivity) hV0 hmn hk2 hg2
  have hkg : k + g = 6 * (a0 + a1) * (2 * N - (a0 + a1)) := by rw [hg]; ring
  rw [hkg] at hcs
  have hfin : (4 * (Q0 + (Q1 + Dh))) * (V0 + m) ≤ Qn * V :=
    mul_le_mul hQge hVm (by positivity) hQnn
  have e1 : (6 * (a0 + a1) * (2 * N - (a0 + a1))) ^ 2
      = 3 * (12 * (a0 + a1) ^ 2 * (2 * N - (a0 + a1)) ^ 2) := by ring
  have e2 : (12 * Q0 + 12 * (Q1 + Dh)) * (V0 + m) = 3 * ((4 * (Q0 + (Q1 + Dh))) * (V0 + m)) := by
    ring
  rw [e1, e2] at hcs
  linarith

/-! ### Combinatorics -/

variable {n : ℕ}

/-- Flip the `i`-th coordinate. -/
def flp (i : Fin n) (x : Fin n → Bool) : Fin n → Bool := Function.update x i (!x i)

lemma flp_same (i : Fin n) (x : Fin n → Bool) : flp i x i = !x i := by simp [flp]

lemma flp_ne {i k : Fin n} (x : Fin n → Bool) (h : k ≠ i) : flp i x k = x k := by
  simp [flp, h]

lemma flp_flp (i : Fin n) (x : Fin n → Bool) : flp i (flp i x) = x := by
  funext k
  by_cases h : k = i
  · subst h; rw [flp_same, flp_same]; simp
  · rw [flp_ne _ h, flp_ne _ h]

lemma flp_dir_inj {i k : Fin n} {x : Fin n → Bool} (h : flp i x = flp k x) : i = k := by
  by_contra hne
  have h2 := congrFun h i
  rw [flp_same, flp_ne x hne] at h2
  cases hx : x i <;> simp [hx] at h2

lemma adj_iff {x y : Fin n → Bool} : (hypercube n).Adj x y ↔ ∃ i, y = flp i x := by
  rw [hypercube_adj, Finset.card_eq_one]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    funext k
    have hk : (x k ≠ y k) ↔ k = i := by
      have := Finset.ext_iff.1 hi k
      simpa using this
    by_cases h : k = i
    · subst h
      rw [flp_same]
      have h3 := hk.2 rfl
      cases hx : x k <;> cases hy : y k <;> simp_all
    · rw [flp_ne x h]
      have h3 : ¬ (x k ≠ y k) := fun h4 => h (hk.1 h4)
      exact (not_not.1 h3).symm
  · rintro ⟨i, rfl⟩
    refine ⟨i, ?_⟩
    ext k
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    by_cases h : k = i
    · subst h; rw [flp_same]; simp
    · rw [flp_ne x h]; simp [h]

/-- number of points of `A` in the fibre -/
def aC (A : Finset (Fin n → Bool)) (S : Finset (Fin n)) (z : Fin n → Bool) : ℕ :=
  ∑ x ∈ A, if (∀ i, i ∉ S → x i = z i) then 1 else 0

/-- number of directions in `S` leaving `A` at `x` -/
def hC (A : Finset (Fin n → Bool)) (S : Finset (Fin n)) (x : Fin n → Bool) : ℕ :=
  ∑ i ∈ S, if flp i x ∈ A then 0 else 1

/-- edge boundary inside the fibre -/
def eC (A : Finset (Fin n → Bool)) (S : Finset (Fin n)) (z : Fin n → Bool) : ℕ :=
  ∑ x ∈ A, if (∀ i, i ∉ S → x i = z i) then hC A S x else 0

/-- inner vertex boundary inside the fibre -/
def vC (A : Finset (Fin n → Bool)) (S : Finset (Fin n)) (z : Fin n → Bool) : ℕ :=
  ∑ x ∈ A, if ((∀ i, i ∉ S → x i = z i) ∧ ∃ i ∈ S, flp i x ∉ A) then 1 else 0

/-- points of the fibre whose `j`-neighbour is outside `A` -/
def wC (A : Finset (Fin n → Bool)) (S : Finset (Fin n)) (j : Fin n) (z : Fin n → Bool) : ℕ :=
  ∑ x ∈ A, if ((∀ i, i ∉ S → x i = z i) ∧ flp j x ∉ A) then 1 else 0

lemma fib_insert {S : Finset (Fin n)} {j : Fin n} (hj : j ∉ S) (x z : Fin n → Bool) :
    (∀ i, i ∉ insert j S → x i = z i) ↔
      ((∀ i, i ∉ S → x i = z i) ∨ (∀ i, i ∉ S → x i = flp j z i)) := by
  constructor
  · intro H
    by_cases h : x j = z j
    · left
      intro i hi
      by_cases hij : i = j
      · subst hij; exact h
      · exact H i (by simp [hij, hi])
    · right
      intro i hi
      by_cases hij : i = j
      · subst hij
        rw [flp_same]
        cases hx : x i <;> cases hz : z i <;> simp_all
      · rw [flp_ne z hij]
        exact H i (by simp [hij, hi])
  · rintro (H | H) i hi
    · exact H i (fun h => hi (Finset.mem_insert_of_mem h))
    · have hij : i ≠ j := fun h => hi (h ▸ Finset.mem_insert_self _ _)
      have := H i (fun h => hi (Finset.mem_insert_of_mem h))
      rwa [flp_ne z hij] at this

lemma fib_excl {S : Finset (Fin n)} {j : Fin n} (hj : j ∉ S) (x z : Fin n → Bool) :
    ¬ ((∀ i, i ∉ S → x i = z i) ∧ (∀ i, i ∉ S → x i = flp j z i)) := by
  rintro ⟨h1, h2⟩
  have e1 := h1 j hj
  have e2 := h2 j hj
  rw [flp_same, e1] at e2
  cases hz : z j <;> simp [hz] at e2

lemma fib_flp {S : Finset (Fin n)} {j : Fin n} (hj : j ∉ S) {x z : Fin n → Bool}
    (h : ∀ i, i ∉ S → x i = z i) : ∀ i, i ∉ S → flp j x i = flp j z i := by
  intro i hi
  by_cases hij : i = j
  · subst hij; rw [flp_same, flp_same, h i hi]
  · rw [flp_ne _ hij, flp_ne _ hij]; exact h i hi

lemma ite_split {p q r : Prop} [Decidable p] [Decidable q] [Decidable r] (h1 : r ↔ p ∨ q)
    (h2 : ¬ (p ∧ q)) (u : ℕ) :
    (if r then u else 0) = (if p then u else 0) + (if q then u else 0) := by
  by_cases hp : p <;> by_cases hq : q
  · exact absurd ⟨hp, hq⟩ h2
  · rw [if_pos (h1.2 (Or.inl hp)), if_pos hp, if_neg hq]; rfl
  · rw [if_pos (h1.2 (Or.inr hq)), if_neg hp, if_pos hq, zero_add]
  · rw [if_neg (fun h => (h1.1 h).elim hp hq), if_neg hp, if_neg hq]

lemma hC_insert (A : Finset (Fin n → Bool)) {S : Finset (Fin n)} {j : Fin n} (hj : j ∉ S)
    (x : Fin n → Bool) :
    hC A (insert j S) x = (if flp j x ∈ A then 0 else 1) + hC A S x := by
  unfold hC
  exact Finset.sum_insert hj

lemma aC_insert (A : Finset (Fin n → Bool)) {S : Finset (Fin n)} {j : Fin n} (hj : j ∉ S)
    (z : Fin n → Bool) : aC A (insert j S) z = aC A S z + aC A S (flp j z) := by
  unfold aC
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun x _ => ite_split (fib_insert hj x z) (fib_excl hj x z) 1)

lemma eC_insert (A : Finset (Fin n → Bool)) {S : Finset (Fin n)} {j : Fin n} (hj : j ∉ S)
    (z : Fin n → Bool) :
    eC A (insert j S) z = eC A S z + eC A S (flp j z) + wC A S j z + wC A S j (flp j z) := by
  unfold eC wC
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [ite_split (fib_insert hj x z) (fib_excl hj x z), hC_insert A hj]
  simp only [ite_and, ite_not]
  split_ifs <;> omega

lemma vC_insert_le (A : Finset (Fin n → Bool)) {S : Finset (Fin n)} {j : Fin n} (hj : j ∉ S)
    (z : Fin n → Bool) :
    vC A S z + vC A S (flp j z) ≤ vC A (insert j S) z ∧
    vC A S z + wC A S j (flp j z) ≤ vC A (insert j S) z ∧
    vC A S (flp j z) + wC A S j z ≤ vC A (insert j S) z := by
  unfold vC wC
  simp only [← Finset.sum_add_distrib]
  refine ⟨Finset.sum_le_sum fun x _ => ?_, Finset.sum_le_sum fun x _ => ?_,
    Finset.sum_le_sum fun x _ => ?_⟩ <;>
  · have h1 := fib_insert hj x z
    have h2 := fib_excl hj x z
    simp only [h1, Finset.exists_mem_insert]
    by_cases hp : (∀ i, i ∉ S → x i = z i) <;> by_cases hq : (∀ i, i ∉ S → x i = flp j z i)
    · exact absurd ⟨hp, hq⟩ h2
    · by_cases hb : flp j x ∈ A <;> by_cases hs : (∃ i ∈ S, flp i x ∉ A) <;> simp [hq, hb, hs]
    · by_cases hb : flp j x ∈ A <;> by_cases hs : (∃ i ∈ S, flp i x ∉ A) <;> simp [hp, hb, hs]
    · simp [hp, hq]

lemma aC_le (A : Finset (Fin n → Bool)) {S : Finset (Fin n)} {j : Fin n} (hj : j ∉ S)
    (z : Fin n → Bool) : aC A S z ≤ wC A S j z + aC A S (flp j z) := by
  have h1 : aC A S z = wC A S j z +
      ∑ x ∈ A, if ((∀ i, i ∉ S → x i = z i) ∧ flp j x ∈ A) then 1 else 0 := by
    unfold aC wC
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases hp : (∀ i, i ∉ S → x i = z i) <;> by_cases hb : flp j x ∈ A <;> simp [hp, hb]
  have h2 : (∑ x ∈ A, if ((∀ i, i ∉ S → x i = z i) ∧ flp j x ∈ A) then 1 else 0)
      ≤ aC A S (flp j z) := by
    unfold aC
    rw [← Finset.card_filter, ← Finset.card_filter]
    refine Finset.card_le_card_of_injOn (flp j) ?_ ?_
    · intro x hx
      rw [Finset.mem_coe, Finset.mem_filter] at hx ⊢
      exact ⟨hx.2.2, fib_flp hj hx.2.1⟩
    · intro x _ y _ hxy
      have := congrArg (flp j) hxy
      rwa [flp_flp, flp_flp] at this
  omega

lemma inv_all (A : Finset (Fin n → Bool)) : ∀ (S : Finset (Fin n)) (z : Fin n → Bool),
    ((aC A S z : ℝ) ≤ 2 ^ #S) ∧
      Inv (2 ^ #S) (aC A S z) (eC A S z) (vC A S z) := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro z
    have he : eC A ∅ z = 0 := by simp [eC, hC]
    have hv : vC A ∅ z = 0 := by simp [vC]
    have ha : aC A ∅ z ≤ 1 := by
      unfold aC
      rw [← Finset.card_filter]
      calc #{x ∈ A | ∀ i, i ∉ (∅ : Finset (Fin n)) → x i = z i}
          ≤ #({z} : Finset (Fin n → Bool)) := by
            refine Finset.card_le_card (fun x hx => ?_)
            rw [Finset.mem_filter] at hx
            rw [Finset.mem_singleton]
            exact funext (fun i => hx.2 i (Finset.notMem_empty i))
        _ = 1 := Finset.card_singleton z
    have ha' : (aC A ∅ z : ℝ) = 0 ∨ (aC A ∅ z : ℝ) = 1 := by
      have : aC A ∅ z = 0 ∨ aC A ∅ z = 1 := by omega
      rcases this with h | h <;> simp [h]
    rw [he, hv]
    simp only [Finset.card_empty, pow_zero, Nat.cast_zero]
    rcases ha' with h | h <;> rw [h] <;> refine ⟨by norm_num, ?_⟩ <;> unfold Inv <;> norm_num
  | insert j S hj ih =>
    intro z
    obtain ⟨b0, I0⟩ := ih z
    obtain ⟨b1, I1⟩ := ih (flp j z)
    have hcard : ((2 : ℝ) ^ #(insert j S)) = 2 * 2 ^ #S := by
      rw [Finset.card_insert_of_notMem hj, pow_succ]; ring
    have hA' : (aC A (insert j S) z : ℝ) = aC A S z + aC A S (flp j z) := by
      rw [aC_insert A hj z]; push_cast; ring
    have hEn := eC_insert A hj z
    obtain ⟨hv1, hv2, hv3⟩ := vC_insert_le A hj z
    have hw1 := aC_le A hj z
    have hw2 := aC_le A hj (flp j z)
    rw [flp_flp] at hw2
    have hpos : (0 : ℝ) < 2 ^ #S := by positivity
    rw [hcard]
    rcases le_total (aC A S z) (aC A S (flp j z)) with hle | hle
    · refine ⟨by rw [hA']; linarith, ?_⟩
      rw [hA']
      have hE : (eC A S z : ℝ) + eC A S (flp j z) + ((aC A S (flp j z) : ℝ) - aC A S z)
          ≤ eC A (insert j S) z := by
        have : eC A S z + eC A S (flp j z) + aC A S (flp j z) ≤ eC A (insert j S) z + aC A S z := by
          omega
        have h' : (eC A S z : ℝ) + eC A S (flp j z) + aC A S (flp j z)
            ≤ eC A (insert j S) z + aC A S z := by exact_mod_cast this
        linarith
      have hV : (vC A S z : ℝ) + vC A S (flp j z) ≤ vC A (insert j S) z := by exact_mod_cast hv1
      have hV' : (vC A S z : ℝ) + ((aC A S (flp j z) : ℝ) - aC A S z) ≤ vC A (insert j S) z := by
        have : vC A S z + aC A S (flp j z) ≤ vC A (insert j S) z + aC A S z := by omega
        have h' : (vC A S z : ℝ) + aC A S (flp j z) ≤ vC A (insert j S) z + aC A S z := by
          exact_mod_cast this
        linarith
      exact inv_step hpos (Nat.cast_nonneg _) (by exact_mod_cast hle) b1 (Nat.cast_nonneg _)
        (Nat.cast_nonneg _) I0 I1 hE hV hV'
    · refine ⟨by rw [hA']; linarith, ?_⟩
      rw [hA', add_comm]
      have hE : (eC A S (flp j z) : ℝ) + eC A S z + ((aC A S z : ℝ) - aC A S (flp j z))
          ≤ eC A (insert j S) z := by
        have : eC A S (flp j z) + eC A S z + aC A S z ≤ eC A (insert j S) z + aC A S (flp j z) := by
          omega
        have h' : (eC A S (flp j z) : ℝ) + eC A S z + aC A S z
            ≤ eC A (insert j S) z + aC A S (flp j z) := by exact_mod_cast this
        linarith
      have hV : (vC A S (flp j z) : ℝ) + vC A S z ≤ vC A (insert j S) z := by
        have : vC A S (flp j z) + vC A S z ≤ vC A (insert j S) z := by omega
        exact_mod_cast this
      have hV' : (vC A S (flp j z) : ℝ) + ((aC A S z : ℝ) - aC A S (flp j z))
          ≤ vC A (insert j S) z := by
        have : vC A S (flp j z) + aC A S z ≤ vC A (insert j S) z + aC A S (flp j z) := by omega
        have h' : (vC A S (flp j z) : ℝ) + aC A S z ≤ vC A (insert j S) z + aC A S (flp j z) := by
          exact_mod_cast this
        linarith
      exact inv_step hpos (Nat.cast_nonneg _) (by exact_mod_cast hle) b0 (Nat.cast_nonneg _)
        (Nat.cast_nonneg _) I1 I0 hE hV hV'

/-! ### Translation to the graph-theoretic boundaries -/

lemma aC_univ (A : Finset (Fin n → Bool)) (z : Fin n → Bool) : aC A univ z = #A := by
  simp [aC]

lemma vC_univ (A : Finset (Fin n → Bool)) (z : Fin n → Bool) :
    vC A univ z = #((hypercube n).innerVertexBoundary A) := by
  unfold vC SimpleGraph.innerVertexBoundary
  rw [← Finset.card_filter]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, not_true_eq_false, false_imp_iff, implies_true,
    true_and, adj_iff]
  constructor
  · rintro ⟨hx, i, hi⟩
    exact ⟨hx, flp i x, hi, i, rfl⟩
  · rintro ⟨hx, w, hw, i, rfl⟩
    exact ⟨hx, i, hw⟩

lemma eC_univ (A : Finset (Fin n → Bool)) (z : Fin n → Bool) :
    eC A univ z = #((hypercube n).edgeBoundary A) := by
  have h0 : eC A univ z = ∑ x ∈ A, hC A univ x := by simp [eC]
  rw [h0]
  have hfib : ∀ p ∈ (hypercube n).edgeBoundary A, p.1 ∈ A := by
    intro p hp
    unfold SimpleGraph.edgeBoundary at hp
    rw [Finset.mem_filter, Finset.mem_product] at hp
    exact hp.1.1
  rw [Finset.card_eq_sum_card_fiberwise hfib]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  have h1 : hC A univ x = #{i : Fin n | flp i x ∉ A} := by
    unfold hC
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases h : flp i x ∈ A <;> simp [h]
  rw [h1]
  refine Finset.card_bij (fun i _ => (x, flp i x)) ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_filter] at hi
    unfold SimpleGraph.edgeBoundary
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_compl, and_true]
    exact ⟨⟨hx, hi.2⟩, adj_iff.2 ⟨i, rfl⟩⟩
  · intro i _ k _ h
    exact flp_dir_inj (Prod.ext_iff.1 h).2
  · rintro ⟨u, w⟩ hp
    unfold SimpleGraph.edgeBoundary at hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_compl] at hp
    obtain ⟨⟨⟨_, hw⟩, hadj⟩, rfl⟩ := hp
    obtain ⟨i, rfl⟩ := adj_iff.1 hadj
    exact ⟨i, by simp [hw], rfl⟩

end OMA

theorem OMA.solution : type_of% @Mathoverflow508539.mathoverflow_508539 := by
  intro n A hA hn
  obtain ⟨-, -, h2⟩ := OMA.inv_all A Finset.univ (fun _ => false)
  rw [OMA.aC_univ, OMA.eC_univ, OMA.vC_univ] at h2
  simp only [Finset.card_univ, Fintype.card_fin] at h2
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hA ⊢
  rw [hA] at h2
  set E : ℝ := (#((SimpleGraph.hypercube (m + 1)).edgeBoundary A) : ℝ) with hE
  set V : ℝ := (#((SimpleGraph.hypercube (m + 1)).innerVertexBoundary A) : ℝ) with hV
  have hM : (0 : ℝ) < 2 ^ m := by positivity
  have key : ((4 : ℝ) ^ m) ≤ E * V := by
    have e4 : (4 : ℝ) ^ m = (2 ^ m) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [e4]
    push_cast at h2
    have h3 : (12 : ℝ) * (2 ^ m) ^ 2 * (2 ^ m) ^ 2 ≤ 12 * (2 ^ m) ^ 2 * (E * V) := by
      have e5 : (2 : ℝ) ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
      rw [e5] at h2
      nlinarith [h2]
    have hpos : (0 : ℝ) < 12 * (2 ^ m) ^ 2 := by positivity
    exact le_of_mul_le_mul_left h3 hpos
  rw [hE, hV] at key
  exact_mod_cast key
