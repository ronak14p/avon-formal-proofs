import FormalConjectures.GreensOpenProblems.«95»
import Mathlib

/-
Copyright 2026 Ronak Patel (Avon Labs).
Released under Apache 2.0 license as described in the file LICENSE.

Link target for the `formal_proof` attributes of
`Green95.green_95` and `Green95.green_95.variants.zakharov`
in google-deepmind/formal-conjectures (`FormalConjectures/GreensOpenProblems/95.lean`).

WHAT THIS FILE PROVES.  The last section (`bridge_green_95`, `bridge_zakharov`) proves
theorems whose types are, by `type_of%`, EXACTLY the types of the upstream declarations
`Green95.green_95` and `Green95.green_95.variants.zakharov`; there is no retyping by hand.
They are derived from a complete development of Zakharov's quantitative sumset bound for
base-g palindromes, which lives in the non-clashing namespaces `Green95Local` and
`LocalDensity` and re-declares the definitions (for standalone checking); the seven
definition-agreement lemmas in `GreenBridge` are all `rfl`.

References:
  - D. Zakharov, "Most integers are not a sum of two palindromes",
    Math. Proc. Cambridge Philos. Soc. 177 (2024), 363-366 (arXiv:2402.10808).
  - J. Cilleruelo, F. Luca, and L. Baxter, "Every positive integer is a sum of
    three palindromes", Math. Comp. 87 (2018), 3023-3055 (arXiv:1602.06208).
  - B. Green, "100 Open Problems", Problem 95 (2024).

PROVENANCE AND DISCLOSURE.  The development was produced by AI agents operated by Avon Labs
(a Gemini 4 "Carbon" lead with "Hydrogen" workers) and machine-checked by Lean; the mathematics
is Zakharov's, and the only increment over [Za24, Theorem 1] is the statement for all large
natural X.  An AI audit (Claude Opus 5.5) recompiled the unmodified development (Green95.lean,
SHA-256 851867d5eec5c05a2aff7286e489a3fcf57eb482fae961a61cbe4725db7ca0ab, 2,168 lines) and
checked the renaming; no human has reviewed the proof text.  Sources assembled by
`assemble_link_target.py` from `Green95Local.lean` (SHA-256 1277c579...0648d) and `Bridge.lean`
(SHA-256 7572ecd5...5e12d) with no edit to either body.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Topology
open scoped Pointwise BigOperators

namespace LocalDensity

noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  ((S ∩ A) ∩ Set.Iio b).ncard / (A ∩ Set.Iio b).ncard

noncomputable def upperDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : ℝ :=
  atTop.limsup fun (b : β) ↦ partialDensity S A b

noncomputable def lowerDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : ℝ :=
  atTop.liminf fun (b : β) ↦ partialDensity S A b

def HasDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (α : ℝ) (A : Set β := Set.univ) : Prop :=
  Tendsto (fun (b : β) => partialDensity S A b) atTop (𝓝 α)

end LocalDensity

namespace Green95Local

def IsPalindrome (g m : ℕ) : Prop :=
  (Nat.digits g m).reverse = Nat.digits g m

instance instDecidableIsPalindrome (g m : ℕ) : Decidable (IsPalindrome g m) :=
  inferInstanceAs (Decidable ((Nat.digits g m).reverse = Nat.digits g m))

def sumsOfTwo (g : ℕ) : Set ℕ :=
  {n | ∃ p q, IsPalindrome g p ∧ IsPalindrome g q ∧ p + q = n}

def sumsOfTwoPositive (g : ℕ) : Set ℕ :=
  {n | ∃ p q, 0 < p ∧ 0 < q ∧ IsPalindrome g p ∧ IsPalindrome g q ∧ p + q = n}

/-- Positive base-`g` palindromes of exact `g`-adic digit length `n` (`n ≥ 1`). -/
def palSet (g n : ℕ) : Finset ℕ :=
  if n = 0 then ∅
  else (Finset.Ico (g ^ (n - 1)) (g ^ n)).filter
    (fun p => decide (0 < p ∧ (Nat.digits g p).length = n ∧ IsPalindrome g p))

/-! ## Basic Structural Lemmas (Theorems 1–4) -/

theorem isPalindrome_zero (g : ℕ) : IsPalindrome g 0 := by
  simp [IsPalindrome]

theorem sumsOfTwo_subset_union (g : ℕ) :
    sumsOfTwo g ⊆ {0} ∪ {p | 0 < p ∧ IsPalindrome g p} ∪ sumsOfTwoPositive g := by
  rintro n ⟨p, q, hp_pal, hq_pal, rfl⟩
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · rcases Nat.eq_zero_or_pos q with rfl | hq
    · left; left; simp
    · left; right; exact ⟨by simpa using hq, by simpa using hq_pal⟩
  · rcases Nat.eq_zero_or_pos q with rfl | hq
    · left; right; exact ⟨by simpa using hp, by simpa using hp_pal⟩
    · right; exact ⟨p, q, hp, hq, hp_pal, hq_pal, rfl⟩

lemma mem_palSet_iff {g n p : ℕ} (hg : 2 ≤ g) :
    p ∈ palSet g n ↔ n ≠ 0 ∧ 0 < p ∧ (Nat.digits g p).length = n ∧ IsPalindrome g p := by
  by_cases hn : n = 0
  · subst hn
    simp [palSet]
  · simp only [palSet, hn, ↓reduceIte, Finset.mem_filter, Finset.mem_Ico, decide_eq_true_eq]
    constructor
    · rintro ⟨_, hpos, hlen, hpal⟩
      exact ⟨hn, hpos, hlen, hpal⟩
    · rintro ⟨_, hpos, hlen, hpal⟩
      refine ⟨⟨?_, ?_⟩, hpos, hlen, hpal⟩
      · have hle := Nat.base_pow_length_digits_le g p (by omega) hpos.ne'
        rw [hlen] at hle
        have hpow : g ^ n = g * g ^ (n - 1) := by
          obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
          simp [pow_succ']
        rw [hpow] at hle
        exact Nat.le_of_mul_le_mul_left hle (by omega)
      · have hlt := Nat.lt_base_pow_length_digits (b := g) (m := p) (by omega)
        rwa [hlen] at hlt

theorem pos_palindromes_inter_Iio_pow_subset {g k : ℕ} (hg : 2 ≤ g) :
    {p : ℕ | 0 < p ∧ IsPalindrome g p} ∩ Set.Iio (g ^ k) ⊆
      ↑((Finset.Icc 1 k).biUnion (palSet g)) := by
  rintro p ⟨⟨hpos, hpal⟩, hlt⟩
  set n := (Nat.digits g p).length
  have hne : Nat.digits g p ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hpos.ne'
  have hn_pos : 1 ≤ n := List.length_pos_iff.mpr hne
  have hp_mem : p ∈ palSet g n :=
    (mem_palSet_iff hg).mpr ⟨by omega, hpos, rfl, hpal⟩
  have hge : g ^ (n - 1) ≤ p := by
    have hp_ico := hp_mem
    simp only [palSet, show n ≠ 0 by omega, ↓reduceIte, Finset.mem_filter,
      Finset.mem_Ico] at hp_ico
    exact hp_ico.1.1
  have hpow_lt : g ^ (n - 1) < g ^ k := lt_of_le_of_lt hge hlt
  have hnk : n - 1 < k := (Nat.pow_lt_pow_iff_right (by omega : 1 < g)).mp hpow_lt
  simp only [Finset.coe_biUnion, Finset.mem_coe, Finset.mem_Icc, Set.mem_iUnion]
  exact ⟨n, ⟨hn_pos, by omega⟩, hp_mem⟩

theorem sumsOfTwoPositive_inter_Iio_pow_subset {g k : ℕ} (hg : 2 ≤ g) :
    sumsOfTwoPositive g ∩ Set.Iio (g ^ k) ⊆
      ↑((Finset.Icc 1 k).biUnion fun n =>
        (Finset.Icc 1 n).biUnion fun m => (palSet g n + palSet g m)) := by
  rintro x ⟨⟨p, q, hp, hq, hp_pal, hq_pal, rfl⟩, hx_lt⟩
  have hp_lt : p < g ^ k := lt_of_le_of_lt (Nat.le_add_right p q) hx_lt
  have hq_lt : q < g ^ k := lt_of_le_of_lt (Nat.le_add_left q p) hx_lt
  have hp_sub := pos_palindromes_inter_Iio_pow_subset hg ⟨⟨hp, hp_pal⟩, hp_lt⟩
  have hq_sub := pos_palindromes_inter_Iio_pow_subset hg ⟨⟨hq, hq_pal⟩, hq_lt⟩
  simp only [Finset.coe_biUnion, Finset.mem_coe, Finset.mem_Icc, Set.mem_iUnion] at hp_sub hq_sub ⊢
  obtain ⟨n₁, ⟨hn₁_1, hn₁_k⟩, hp_mem⟩ := hp_sub
  obtain ⟨n₂, ⟨hn₂_1, hn₂_k⟩, hq_mem⟩ := hq_sub
  rcases le_total n₂ n₁ with hle | hle
  · refine ⟨n₁, ⟨hn₁_1, hn₁_k⟩, n₂, ⟨hn₂_1, hle⟩, ?_⟩
    exact Finset.add_mem_add hp_mem hq_mem
  · refine ⟨n₂, ⟨hn₂_1, hn₂_k⟩, n₁, ⟨hn₁_1, hle⟩, ?_⟩
    rw [add_comm p q]
    exact Finset.add_mem_add hq_mem hp_mem

/-! ## Digit-Vector Representation & Cardinality Bounds (Theorems 5–7) -/

abbrev HalfPal (g n : ℕ) :=
  { d : Fin g // d.1 ≠ 0 } × (Fin ((n - 1) / 2) → Fin g)

lemma halfToWord_idx_lt {n : ℕ} (i : Fin n) (hr : min i.1 (n - 1 - i.1) ≠ 0) :
    min i.1 (n - 1 - i.1) - 1 < (n - 1) / 2 := by
  omega

def halfToWord {g n : ℕ} (x : HalfPal g n) : Fin n → Fin g :=
  fun i =>
    let r := min i.1 (n - 1 - i.1)
    if hr : r = 0 then x.1.1
    else x.2 ⟨r - 1, halfToWord_idx_lt i hr⟩

def evalWord (g : ℕ) {n : ℕ} (u : Fin n → Fin g) : ℕ :=
  ∑ i : Fin n, (u i).1 * g ^ i.1

def evalHalfPal (g n : ℕ) (x : HalfPal g n) : ℕ :=
  evalWord g (halfToWord x)

lemma evalWord_eq_ofDigits (g : ℕ) :
    ∀ {n : ℕ} (u : Fin n → Fin g),
      evalWord g u = Nat.ofDigits g (List.ofFn fun i : Fin n => (u i).1)
  | 0, u => by simp [evalWord]
  | n + 1, u => by
      rw [evalWord, Fin.sum_univ_succ, List.ofFn_succ, Nat.ofDigits_cons]
      simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ']
      have ih := evalWord_eq_ofDigits g (fun i : Fin n => u i.succ)
      simp only [evalWord] at ih
      rw [← ih, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      ring

lemma halfToWord_symm {g n : ℕ} (x : HalfPal g n) (i : Fin n) :
    halfToWord x ⟨n - 1 - i.1, by omega⟩ = halfToWord x i := by
  have hr : min (n - 1 - i.1) (n - 1 - (n - 1 - i.1)) = min i.1 (n - 1 - i.1) := by omega
  dsimp only [halfToWord]
  split_ifs with h1 h2
  · rfl
  · omega
  · omega
  · exact congrArg x.2 (by ext; dsimp; omega)

lemma halfToWord_zero {g n : ℕ} (hn : 1 ≤ n) (x : HalfPal g n) :
    halfToWord x ⟨0, hn⟩ = x.1.1 := by
  simp [halfToWord]

lemma halfToWord_succ_of_le {g n : ℕ} (x : HalfPal g n) (k : Fin ((n - 1) / 2)) :
    halfToWord x ⟨k.1 + 1, by omega⟩ = x.2 k := by
  have hk : k.1 < (n - 1) / 2 := k.2
  have hmin : min (k.1 + 1) (n - 1 - (k.1 + 1)) = k.1 + 1 := by omega
  dsimp only [halfToWord]
  split_ifs with h
  · omega
  · exact congrArg x.2 (by ext; dsimp; omega)

lemma digits_evalHalfPal {g n : ℕ} (hg : 2 ≤ g) (hn : 1 ≤ n) (x : HalfPal g n) :
    Nat.digits g (evalHalfPal g n x) = List.ofFn (fun i : Fin n => (halfToWord x i).1) := by
  rw [evalHalfPal, evalWord_eq_ofDigits]
  refine Nat.digits_ofDigits g (by omega) _ ?_ ?_
  · intro d hd
    rw [List.mem_ofFn] at hd
    obtain ⟨i, rfl⟩ := hd
    exact (halfToWord x i).isLt
  · intro hne
    rw [List.getLast_eq_getElem]
    simp only [List.length_ofFn, List.getElem_ofFn]
    have hsymm := halfToWord_symm x ⟨0, hn⟩
    have hval : halfToWord x ⟨n - 1, by omega⟩ = halfToWord x ⟨0, hn⟩ := by
      convert hsymm using 2
      exact Fin.ext (by simp)
    rw [hval, halfToWord_zero hn]
    exact x.1.2

lemma evalHalfPal_mem_palSet {g n : ℕ} (hg : 2 ≤ g) (hn : 1 ≤ n) (x : HalfPal g n) :
    evalHalfPal g n x ∈ palSet g n := by
  rw [mem_palSet_iff hg]
  have hdig := digits_evalHalfPal hg hn x
  have hlen : (Nat.digits g (evalHalfPal g n x)).length = n := by
    rw [hdig, List.length_ofFn]
  have hpos : 0 < evalHalfPal g n x := by
    by_contra h0
    have heq0 : evalHalfPal g n x = 0 := by omega
    rw [heq0, Nat.digits_zero, List.length_nil] at hlen
    omega
  have hpal : IsPalindrome g (evalHalfPal g n x) := by
    rw [IsPalindrome, hdig]
    refine List.ext_getElem (by simp) fun i hi1 hi2 => ?_
    simp only [List.length_reverse, List.length_ofFn] at hi1
    rw [List.getElem_reverse]
    simp only [List.length_ofFn, List.getElem_ofFn]
    have hsymm := halfToWord_symm x ⟨i, hi1⟩
    exact congrArg Fin.val hsymm
  exact ⟨by omega, hpos, hlen, hpal⟩

lemma evalHalfPal_injective {g n : ℕ} (hg : 2 ≤ g) (hn : 1 ≤ n) :
    Function.Injective (evalHalfPal g n) := by
  intro x y hxy
  have hdig : List.ofFn (fun i : Fin n => (halfToWord x i).1) =
      List.ofFn (fun i : Fin n => (halfToWord y i).1) := by
    rw [← digits_evalHalfPal hg hn x, ← digits_evalHalfPal hg hn y, hxy]
  have hword : ∀ i : Fin n, halfToWord x i = halfToWord y i := by
    intro i
    have hi := congrArg (fun l : List ℕ => l.getD i.1 0) hdig
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt, ↓reduceDIte,
      Option.getD_some] at hi
    exact Fin.ext hi
  ext
  · have h0 := congrArg Fin.val (hword ⟨0, hn⟩)
    simpa [halfToWord_zero hn] using h0
  · rename_i k
    have hk := congrArg Fin.val (hword ⟨k.1 + 1, by omega⟩)
    simpa [halfToWord_succ_of_le] using hk

lemma evalHalfPal_surjOn_palSet {g n : ℕ} (hg : 2 ≤ g) (hn : 1 ≤ n) :
    ∀ p ∈ palSet g n, ∃ x : HalfPal g n, evalHalfPal g n x = p := by
  intro p hp
  rw [mem_palSet_iff hg] at hp
  rcases hp with ⟨_, hpos, hlen, hpal⟩
  let L := Nat.digits g p
  have hL_len : L.length = n := hlen
  have hL_ne : L ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hpos.ne'
  have hL_lt : ∀ i : ℕ, (hi : i < n) → L[i]'(by omega) < g :=
    fun i hi => Nat.digits_lt_base (by omega) (List.getElem_mem _)
  have hL0_ne : L[0]'(by omega) ≠ 0 := by
    have hrev : L.reverse[n - 1]'(by simp [hL_len]; omega) = L[n - 1]'(by omega) := by
      congr 1
    rw [List.getElem_reverse] at hrev
    have hlast : L[n - 1]'(by omega) = L.getLast hL_ne := by
      rw [List.getLast_eq_getElem]
      congr 1; omega
    have hidx : L.length - 1 - (n - 1) = 0 := by omega
    simp only [hidx] at hrev
    have h0_eq : L[0]'(by omega) = L.getLast hL_ne := hrev.trans hlast
    rw [h0_eq]
    exact Nat.getLast_digit_ne_zero g hpos.ne'
  let x : HalfPal g n :=
    (⟨⟨L[0]'(by omega), hL_lt 0 (by omega)⟩, hL0_ne⟩,
      fun k : Fin ((n - 1) / 2) => ⟨L[k.1 + 1]'(by omega), hL_lt (k.1 + 1) (by omega)⟩)
  refine ⟨x, ?_⟩
  rw [evalHalfPal, evalWord_eq_ofDigits]
  have hlist : List.ofFn (fun i : Fin n => (halfToWord x i).1) = L := by
    refine List.ext_getElem (by simp [hL_len]) fun i hi1 hi2 => ?_
    simp only [List.length_ofFn] at hi1
    simp only [List.getElem_ofFn, halfToWord]
    split_ifs with hr
    · have hi0 : i = 0 ∨ i = n - 1 := by omega
      rcases hi0 with rfl | rfl
      · rfl
      · have hrev : L.reverse[0]'(by simp [hL_len]; omega) = L[0]'(by omega) := by
          congr 1
        rw [List.getElem_reverse] at hrev
        have hidx : L.length - 1 - 0 = n - 1 := by omega
        simpa [hidx, x] using hrev.symm
    · have hcases : min i (n - 1 - i) = i ∨ min i (n - 1 - i) = n - 1 - i :=
        min_choice i (n - 1 - i)
      rcases hcases with hri | hri
      · have hidx : min i (n - 1 - i) - 1 + 1 = i := by omega
        simp only [x]
        congr 1
      · have hrev : L.reverse[i]'(by simp [hL_len]; omega) = L[i]'hi2 := by
          congr 1
        rw [List.getElem_reverse] at hrev
        have hidx : min i (n - 1 - i) - 1 + 1 = L.length - 1 - i := by omega
        dsimp only [x]
        rw [← hrev]
        congr 1
  rw [hlist]
  exact Nat.ofDigits_digits g p

lemma palSet_eq_map {g n : ℕ} (hg : 2 ≤ g) (hn : 1 ≤ n) :
    palSet g n = Finset.univ.map ⟨evalHalfPal g n, evalHalfPal_injective hg hn⟩ := by
  ext p
  simp only [Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk, true_and]
  constructor
  · exact evalHalfPal_surjOn_palSet hg hn p
  · rintro ⟨x, rfl⟩
    exact evalHalfPal_mem_palSet hg hn x

lemma card_nonzero_fin (g : ℕ) (hg : 1 ≤ g) :
    Fintype.card { d : Fin g // d.1 ≠ 0 } = g - 1 := by
  have e : { d : Fin g // d.1 ≠ 0 } ≃ Fin (g - 1) :=
    { toFun := fun d => ⟨d.1.1 - 1, by have := d.1.2; have := d.2; omega⟩
      invFun := fun k => ⟨⟨k.1 + 1, by have := k.2; omega⟩, by dsimp; omega⟩
      left_inv := fun d => Subtype.ext (Fin.ext (by have := d.2; dsimp; omega))
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_fin]

lemma card_palSet_eq {g n : ℕ} (hg : 2 ≤ g) (hn : 1 ≤ n) :
    (palSet g n).card = (g - 1) * g ^ ((n - 1) / 2) := by
  rw [palSet_eq_map hg hn, Finset.card_map, Finset.card_univ, Fintype.card_prod,
    card_nonzero_fin g (by omega), Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

theorem card_palSet_le {g n : ℕ} (hg : 2 ≤ g) (hn : 1 ≤ n) :
    (palSet g n).card ≤ (g - 1) * g ^ ((n - 1) / 2) :=
  (card_palSet_eq hg hn).le

theorem sum_card_palSet_Icc_le_nat {g N : ℕ} (hg : 2 ≤ g) :
    (∑ n ∈ Finset.Icc 1 N, (palSet g n).card) ≤ 2 * g ^ ((N + 1) / 2) := by
  have hle1 : (∑ n ∈ Finset.Icc 1 N, (palSet g n).card) ≤
      ∑ n ∈ Finset.Icc 1 N, (g - 1) * g ^ ((n - 1) / 2) := by
    refine Finset.sum_le_sum fun n hn => ?_
    rw [Finset.mem_Icc] at hn
    exact card_palSet_le hg hn.1
  set E := (N + 1) / 2
  have hmaps : ∀ n ∈ Finset.Icc 1 N, (n - 1) / 2 ∈ Finset.range E := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [Finset.mem_range]
    omega
  have hfib := (Finset.sum_fiberwise_of_maps_to hmaps
    (fun n => (g - 1) * g ^ ((n - 1) / 2))).symm
  have hle2 : ∑ n ∈ Finset.Icc 1 N, (g - 1) * g ^ ((n - 1) / 2) ≤
      ∑ e ∈ Finset.range E, 2 * ((g - 1) * g ^ e) := by
    rw [hfib]
    refine Finset.sum_le_sum fun e _ => ?_
    have hconst : ∑ n ∈ (Finset.Icc 1 N).filter (fun n => (n - 1) / 2 = e),
        (g - 1) * g ^ ((n - 1) / 2) =
        ((Finset.Icc 1 N).filter (fun n => (n - 1) / 2 = e)).card * ((g - 1) * g ^ e) := by
      rw [← smul_eq_mul, ← Finset.sum_const]
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [(Finset.mem_filter.mp hn).2]
    rw [hconst]
    refine Nat.mul_le_mul_right _ ?_
    have hsub : (Finset.Icc 1 N).filter (fun n => (n - 1) / 2 = e) ⊆
        {2 * e + 1, 2 * e + 2} := by
      intro n hn
      rw [Finset.mem_filter, Finset.mem_Icc] at hn
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    exact (Finset.card_le_card hsub).trans (Finset.card_le_two)
  have hgeom : (g - 1) * ∑ e ∈ Finset.range E, g ^ e ≤ g ^ E := by
    have hmul := geom_sum_mul_add (g - 1) E
    rw [tsub_add_cancel_of_le (by omega : 1 ≤ g)] at hmul
    rw [mul_comm]
    omega
  calc
    (∑ n ∈ Finset.Icc 1 N, (palSet g n).card)
      ≤ ∑ n ∈ Finset.Icc 1 N, (g - 1) * g ^ ((n - 1) / 2) := hle1
    _ ≤ ∑ e ∈ Finset.range E, 2 * ((g - 1) * g ^ e) := hle2
    _ = 2 * ((g - 1) * ∑ e ∈ Finset.range E, g ^ e) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 2 * g ^ E := Nat.mul_le_mul_left 2 hgeom

theorem card_palSet_add_le_mul (g n m : ℕ) :
    (palSet g n + palSet g m).card ≤ (palSet g n).card * (palSet g m).card :=
  Finset.card_add_le

/-! ## Block-Swap Collision Identity & Measure-Free MGF Bound (Theorem 8) -/

def blockA (d g : ℕ) (hg : 2 ≤ g) : Fin (d + 2) → Fin g :=
  fun s => if s.1 = 0 ∨ s.1 = d + 1 then ⟨1, by omega⟩ else ⟨0, by omega⟩

def blockB (d g : ℕ) (hg : 2 ≤ g) : Fin (d + 2) → Fin g :=
  fun _ => ⟨0, by omega⟩

def blockA' (d g : ℕ) (hg : 2 ≤ g) : Fin (d + 2) → Fin g :=
  fun s => if s.1 = 0 ∨ s.1 = d + 1 then ⟨0, by omega⟩ else ⟨g - 1, by omega⟩

def blockB' (d g : ℕ) (hg : 2 ≤ g) : Fin (d + 2) → Fin g :=
  fun s => if s.1 = 0 ∨ s.1 = 1 then ⟨1, by omega⟩ else ⟨0, by omega⟩

def blockVal (g : ℕ) {L : ℕ} (blk : Fin L → Fin g) : ℤ :=
  ∑ s : Fin L, ((blk s).1 : ℤ) * (g : ℤ) ^ s.1

def revBlockVal (g : ℕ) {L : ℕ} (blk : Fin L → Fin g) : ℤ :=
  ∑ s : Fin L, ((blk s).1 : ℤ) * (g : ℤ) ^ (L - 1 - s.1)

lemma blockVal_blockA (d g : ℕ) (hg : 2 ≤ g) :
    blockVal g (blockA d g hg) = 1 + (g : ℤ) ^ (d + 1) := by
  unfold blockVal blockA
  have h1 : ∀ s : Fin (d + 2),
      (((if s.1 = 0 ∨ s.1 = d + 1 then (⟨1, by omega⟩ : Fin g) else ⟨0, by omega⟩).1 : ℤ) *
        (g : ℤ) ^ s.1) =
      if s.1 = 0 ∨ s.1 = d + 1 then (g : ℤ) ^ s.1 else 0 := fun s => by split_ifs <;> simp
  simp_rw [h1, ← Finset.sum_filter]
  have heq : Finset.univ.filter (fun s : Fin (d + 2) => s.1 = 0 ∨ s.1 = d + 1) =
      ({⟨0, by omega⟩, ⟨d + 1, by omega⟩} : Finset (Fin (d + 2))) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Fin.ext_iff]
  rw [heq, Finset.sum_pair (by simp [Fin.ext_iff])]
  simp

lemma revBlockVal_blockA (d g : ℕ) (hg : 2 ≤ g) :
    revBlockVal g (blockA d g hg) = 1 + (g : ℤ) ^ (d + 1) := by
  unfold revBlockVal blockA
  have h1 : ∀ s : Fin (d + 2),
      (((if s.1 = 0 ∨ s.1 = d + 1 then (⟨1, by omega⟩ : Fin g) else ⟨0, by omega⟩).1 : ℤ) *
        (g : ℤ) ^ (d + 2 - 1 - s.1)) =
      if s.1 = 0 ∨ s.1 = d + 1 then (g : ℤ) ^ (d + 2 - 1 - s.1) else 0 := fun s => by
    split_ifs <;> simp
  simp_rw [h1, ← Finset.sum_filter]
  have heq : Finset.univ.filter (fun s : Fin (d + 2) => s.1 = 0 ∨ s.1 = d + 1) =
      ({⟨0, by omega⟩, ⟨d + 1, by omega⟩} : Finset (Fin (d + 2))) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Fin.ext_iff]
  rw [heq, Finset.sum_pair (by simp [Fin.ext_iff])]
  simp [add_comm]

lemma blockVal_blockB (d g : ℕ) (hg : 2 ≤ g) :
    blockVal g (blockB d g hg) = 0 := by
  simp [blockVal, blockB]

lemma revBlockVal_blockB (d g : ℕ) (hg : 2 ≤ g) :
    revBlockVal g (blockB d g hg) = 0 := by
  simp [revBlockVal, blockB]

lemma blockVal_blockB' (d g : ℕ) (hg : 2 ≤ g) :
    blockVal g (blockB' d g hg) = 1 + (g : ℤ) := by
  unfold blockVal blockB'
  have h1 : ∀ s : Fin (d + 2),
      (((if s.1 = 0 ∨ s.1 = 1 then (⟨1, by omega⟩ : Fin g) else ⟨0, by omega⟩).1 : ℤ) *
        (g : ℤ) ^ s.1) =
      if s.1 = 0 ∨ s.1 = 1 then (g : ℤ) ^ s.1 else 0 := fun s => by split_ifs <;> simp
  simp_rw [h1, ← Finset.sum_filter]
  have heq : Finset.univ.filter (fun s : Fin (d + 2) => s.1 = 0 ∨ s.1 = 1) =
      ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin (d + 2))) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Fin.ext_iff]
  rw [heq, Finset.sum_pair (by simp)]
  simp

lemma revBlockVal_blockB' (d g : ℕ) (hg : 2 ≤ g) :
    revBlockVal g (blockB' d g hg) = (g : ℤ) ^ (d + 1) + (g : ℤ) ^ d := by
  unfold revBlockVal blockB'
  have h1 : ∀ s : Fin (d + 2),
      (((if s.1 = 0 ∨ s.1 = 1 then (⟨1, by omega⟩ : Fin g) else ⟨0, by omega⟩).1 : ℤ) *
        (g : ℤ) ^ (d + 2 - 1 - s.1)) =
      if s.1 = 0 ∨ s.1 = 1 then (g : ℤ) ^ (d + 2 - 1 - s.1) else 0 := fun s => by
    split_ifs <;> simp
  simp_rw [h1, ← Finset.sum_filter]
  have heq : Finset.univ.filter (fun s : Fin (d + 2) => s.1 = 0 ∨ s.1 = 1) =
      ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin (d + 2))) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Fin.ext_iff]
  rw [heq, Finset.sum_pair (by simp)]
  simp

lemma blockVal_blockA' (d g : ℕ) (hg : 2 ≤ g) :
    blockVal g (blockA' d g hg) = (g : ℤ) ^ (d + 1) - (g : ℤ) := by
  have hsum : blockVal g (blockA' d g hg) + ((g : ℤ) - 1) * blockVal g (blockA d g hg) =
      (g : ℤ) ^ (d + 2) - 1 := by
    unfold blockVal
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    have hterm : ∑ s : Fin (d + 2),
        (((blockA' d g hg s).1 : ℤ) * (g : ℤ) ^ s.1 +
          ((g : ℤ) - 1) * (((blockA d g hg s).1 : ℤ) * (g : ℤ) ^ s.1)) =
        ∑ s : Fin (d + 2), ((g : ℤ) - 1) * (g : ℤ) ^ s.1 := by
      refine Finset.sum_congr rfl fun s _ => ?_
      simp only [blockA', blockA]
      split_ifs
      · simp
      · have hcast : ((g - 1 : ℕ) : ℤ) = (g : ℤ) - 1 := by omega
        simp [hcast]
    rw [hterm, ← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun i => (g : ℤ) ^ i)]
    rw [mul_comm, geom_sum_mul (g : ℤ) (d + 2)]
  rw [blockVal_blockA d g hg] at hsum
  linear_combination hsum

lemma revBlockVal_blockA' (d g : ℕ) (hg : 2 ≤ g) :
    revBlockVal g (blockA' d g hg) = (g : ℤ) ^ (d + 1) - (g : ℤ) := by
  have heq : revBlockVal g (blockA' d g hg) = blockVal g (blockA' d g hg) := by
    unfold revBlockVal blockVal
    refine Equiv.sum_comp (Fin.revPerm) _ |>.symm.trans ?_
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [Fin.revPerm_apply, Fin.val_rev, blockA']
    have hs := s.isLt
    have h1 : (d + 2 - (s.1 + 1) = 0 ∨ d + 2 - (s.1 + 1) = d + 1) ↔
        (s.1 = 0 ∨ s.1 = d + 1) := by omega
    have h2 : d + 2 - 1 - (d + 2 - (s.1 + 1)) = s.1 := by omega
    simp only [h1, h2]
  rw [heq, blockVal_blockA' d g hg]

lemma block_collision_lower (d g : ℕ) (hg : 2 ≤ g) :
    (blockVal g (blockA' d g hg) - blockVal g (blockA d g hg)) +
      (blockVal g (blockB' d g hg) - blockVal g (blockB d g hg)) = 0 := by
  rw [blockVal_blockA, blockVal_blockB, blockVal_blockA', blockVal_blockB']
  ring

lemma block_collision_upper (d g : ℕ) (hg : 2 ≤ g) :
    (g : ℤ) ^ d * (revBlockVal g (blockA' d g hg) - revBlockVal g (blockA d g hg)) +
      (revBlockVal g (blockB' d g hg) - revBlockVal g (blockB d g hg)) = 0 := by
  rw [revBlockVal_blockA, revBlockVal_blockB, revBlockVal_blockA', revBlockVal_blockB']
  ring

/-! ### Block Embeddings & Coordinate Splitting -/

lemma block_fit_bound {m t L : ℕ} (hL : 2 ≤ L) (ht : 1 ≤ t) (hm_bound : 2 * (t + 1) * L ≤ m)
    (j : Fin t) (s : Fin L) :
    (j.1 + 1) * L + s.1 - 1 < (m - 1) / 2 := by
  have hj : j.1 + 1 ≤ t := j.isLt
  have hs : s.1 ≤ L - 1 := Nat.le_pred_of_lt s.isLt
  have h1 : (j.1 + 1) * L ≤ t * L := Nat.mul_le_mul_right L hj
  have h2 : t * L + L = (t + 1) * L := by ring
  have h3 : (j.1 + 1) * L + s.1 + 1 ≤ (t + 1) * L := by omega
  have h4 : 8 ≤ 2 * (t + 1) * L := by
    have : 2 * 2 * 2 ≤ 2 * (t + 1) * L :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 (by omega)) hL
    omega
  have hm_mul : 2 * ((t + 1) * L) ≤ m := by linarith
  have h5 : 2 * ((j.1 + 1) * L + s.1) ≤ m - 2 := by omega
  omega

def blockEmb {t L K : ℕ} (hL : 1 ≤ L)
    (hfit : ∀ (j : Fin t) (s : Fin L), (j.1 + 1) * L + s.1 - 1 < K) :
    Fin t × Fin L ↪ Fin K where
  toFun p := ⟨(p.1.1 + 1) * L + p.2.1 - 1, hfit p.1 p.2⟩
  inj' p₁ p₂ h := by
    have hval := congrArg Fin.val h
    dsimp only at hval
    have hp1 : 1 ≤ (p₁.1.1 + 1) * L + p₁.2.1 :=
      le_trans hL (Nat.le_trans (Nat.le_mul_of_pos_left L (Nat.succ_pos _)) (Nat.le_add_right _ _))
    have hp2 : 1 ≤ (p₂.1.1 + 1) * L + p₂.2.1 :=
      le_trans hL (Nat.le_trans (Nat.le_mul_of_pos_left L (Nat.succ_pos _)) (Nat.le_add_right _ _))
    have heq : (p₁.1.1 + 1) * L + p₁.2.1 = (p₂.1.1 + 1) * L + p₂.2.1 := by omega
    have hmod := congrArg (· % L) heq
    rw [Nat.mul_add_mod_self_right, Nat.mul_add_mod_self_right,
      Nat.mod_eq_of_lt p₁.2.isLt, Nat.mod_eq_of_lt p₂.2.isLt] at hmod
    have hdiv := congrArg (· / L) heq
    rw [Nat.add_comm ((p₁.1.1 + 1) * L), Nat.add_comm ((p₂.1.1 + 1) * L),
      Nat.add_mul_div_right _ _ (by omega), Nat.add_mul_div_right _ _ (by omega),
      Nat.div_eq_of_lt p₁.2.isLt, Nat.div_eq_of_lt p₂.2.isLt, zero_add, zero_add] at hdiv
    ext <;> omega

noncomputable def blockSplitEquiv {g t L K : ℕ} (emb : Fin t × Fin L ↪ Fin K) :
    (Fin K → Fin g) ≃
      (Fin t → Fin L → Fin g) × ({ b : Fin K // b ∉ Set.range emb } → Fin g) := by
  classical
  exact
    { toFun := fun w => (fun j s => w (emb (j, s)), fun b => w b.1)
      invFun := fun p b =>
        if hb : b ∈ Set.range emb then
          let idx := Classical.choose hb
          p.1 idx.1 idx.2
        else
          p.2 ⟨b, hb⟩
      left_inv := fun w => by
        ext b
        by_cases hb : b ∈ Set.range emb
        · simp only [dif_pos hb]
          rw [Classical.choose_spec hb]
        · simp only [dif_neg hb]
      right_inv := fun p => by
        ext
        · rename_i j s
          have hb : emb (j, s) ∈ Set.range emb := ⟨(j, s), rfl⟩
          simp only [dif_pos hb]
          have heq := emb.injective (Classical.choose_spec hb)
          rw [heq]
        · rename_i b
          simp only [dif_neg b.2] }

lemma blockSplitEquiv_symm_emb {g t L K : ℕ} (emb : Fin t × Fin L ↪ Fin K)
    (f : Fin t → Fin L → Fin g) (r : { b : Fin K // b ∉ Set.range emb } → Fin g)
    (j : Fin t) (s : Fin L) :
    (blockSplitEquiv emb).symm (f, r) (emb (j, s)) = f j s := by
  have hb : emb (j, s) ∈ Set.range emb := ⟨(j, s), rfl⟩
  dsimp [blockSplitEquiv]
  rw [dif_pos hb]
  have hspec := Classical.choose_spec hb
  have heq := emb.injective hspec
  rw [heq]

lemma blockSplitEquiv_symm_compl {g t L K : ℕ} (emb : Fin t × Fin L ↪ Fin K)
    (f : Fin t → Fin L → Fin g) (r : { b : Fin K // b ∉ Set.range emb } → Fin g)
    {b : Fin K} (hb : b ∉ Set.range emb) :
    (blockSplitEquiv emb).symm (f, r) b = r ⟨b, hb⟩ := by
  dsimp [blockSplitEquiv]
  exact dif_neg hb

noncomputable def halfPalSplitEquiv {g n t L : ℕ} (emb : Fin t × Fin L ↪ Fin ((n - 1) / 2)) :
    HalfPal g n ≃
      (Fin t → Fin L → Fin g) ×
        ({ d : Fin g // d.1 ≠ 0 } × ({ b : Fin ((n - 1) / 2) // b ∉ Set.range emb } → Fin g)) :=
  (Equiv.prodCongr (Equiv.refl _) (blockSplitEquiv emb)).trans
    { toFun := fun ⟨d₀, ⟨blk, rest⟩⟩ => (blk, (d₀, rest))
      invFun := fun ⟨blk, ⟨d₀, rest⟩⟩ => ⟨d₀, ⟨blk, rest⟩⟩
      left_inv := fun ⟨_, ⟨_, _⟩⟩ => rfl
      right_inv := fun ⟨_, ⟨_, _⟩⟩ => rfl }

lemma halfPalSplitEquiv_symm_emb {g n t L : ℕ} (emb : Fin t × Fin L ↪ Fin ((n - 1) / 2))
    (blk : Fin t → Fin L → Fin g)
    (rest : { d : Fin g // d.1 ≠ 0 } × ({ b : Fin ((n - 1) / 2) // b ∉ Set.range emb } → Fin g))
    (j : Fin t) (s : Fin L) :
    ((halfPalSplitEquiv emb).symm (blk, rest)).2 (emb (j, s)) = blk j s :=
  blockSplitEquiv_symm_emb emb blk rest.2 j s

lemma halfPalSplitEquiv_symm_compl {g n t L : ℕ} (emb : Fin t × Fin L ↪ Fin ((n - 1) / 2))
    (blk : Fin t → Fin L → Fin g)
    (rest : { d : Fin g // d.1 ≠ 0 } × ({ b : Fin ((n - 1) / 2) // b ∉ Set.range emb } → Fin g))
    {b : Fin ((n - 1) / 2)} (hb : b ∉ Set.range emb) :
    ((halfPalSplitEquiv emb).symm (blk, rest)).2 b = rest.2 ⟨b, hb⟩ :=
  blockSplitEquiv_symm_compl emb blk rest.2 hb

lemma evalHalfPal_blockSwap_diff {g n t L : ℕ} (hL : 2 ≤ L)
    (hn_bound : 2 * (t + 1) * L ≤ n)
    (emb : Fin t × Fin L ↪ Fin ((n - 1) / 2))
    (hemb : ∀ j s, (emb (j, s)).1 = (j.1 + 1) * L + s.1 - 1)
    (x x' : HalfPal g n) (U : Finset (Fin t))
    (blk blk' : Fin L → Fin g)
    (hx_fst : x'.1 = x.1)
    (hx_rest : ∀ b : Fin ((n - 1) / 2), b ∉ Set.range emb → x'.2 b = x.2 b)
    (hx_blk_out : ∀ j ∉ U, ∀ s : Fin L, x'.2 (emb (j, s)) = x.2 (emb (j, s)))
    (hx_blk_in : ∀ j ∈ U, ∀ s : Fin L, x.2 (emb (j, s)) = blk s ∧ x'.2 (emb (j, s)) = blk' s) :
    (evalHalfPal g n x' : ℤ) - (evalHalfPal g n x : ℤ) =
      ∑ j ∈ U,
        ((g : ℤ) ^ ((j.1 + 1) * L) * (blockVal g blk' - blockVal g blk) +
          (g : ℤ) ^ (n - (j.1 + 1) * L - L) * (revBlockVal g blk' - revBlockVal g blk)) := by
  have hn_mul : 2 * ((t + 1) * L) ≤ n := by linarith
  have hn4 : 4 ≤ n := by
    have : 2 * 1 * 2 ≤ 2 * ((t + 1) * L) := by nlinarith
    omega
  have h_word_fit : ∀ (j : Fin t) (s : Fin L), 2 * ((j.1 + 1) * L + s.1) ≤ n - 2 := by
    intro j s
    have hj : j.1 + 1 ≤ t := j.isLt
    have hs : s.1 ≤ L - 1 := Nat.le_pred_of_lt s.isLt
    have h1 : (j.1 + 1) * L ≤ t * L := Nat.mul_le_mul_right L hj
    have h2 : t * L + L = (t + 1) * L := by ring
    have h3 : (j.1 + 1) * L + s.1 + 1 ≤ (t + 1) * L := by omega
    omega
  let lowIdx : Fin t × Fin L → Fin n := fun p =>
    ⟨(p.1.1 + 1) * L + p.2.1, by have := h_word_fit p.1 p.2; omega⟩
  let highIdx : Fin t × Fin L → Fin n := fun p =>
    ⟨n - 1 - ((p.1.1 + 1) * L + p.2.1), by have := h_word_fit p.1 p.2; omega⟩
  have hlow_inj : Function.Injective lowIdx := by
    intro p₁ p₂ hp
    have hv := congrArg Fin.val hp
    dsimp only [lowIdx] at hv
    have h1 : 1 ≤ (p₁.1.1 + 1) * L + p₁.2.1 :=
      le_trans (by omega) (Nat.le_trans (Nat.le_mul_of_pos_left L (Nat.succ_pos _)) (Nat.le_add_right _ _))
    have h2 : 1 ≤ (p₂.1.1 + 1) * L + p₂.2.1 :=
      le_trans (by omega) (Nat.le_trans (Nat.le_mul_of_pos_left L (Nat.succ_pos _)) (Nat.le_add_right _ _))
    have hemb_eq : emb p₁ = emb p₂ := Fin.ext (by rw [hemb p₁.1 p₁.2, hemb p₂.1 p₂.2]; omega)
    exact emb.injective hemb_eq
  have hhigh_inj : Function.Injective highIdx := by
    intro p₁ p₂ hp
    have hv := congrArg Fin.val hp
    dsimp only [highIdx] at hv
    have hf1 := h_word_fit p₁.1 p₁.2
    have hf2 := h_word_fit p₂.1 p₂.2
    have hlow : lowIdx p₁ = lowIdx p₂ := Fin.ext (by dsimp [lowIdx]; omega)
    exact hlow_inj hlow
  let Δ : Fin n → ℤ := fun i =>
    (((halfToWord x' i).1 : ℤ) - ((halfToWord x i).1 : ℤ)) * (g : ℤ) ^ i.1
  have hdiff_eq : (evalHalfPal g n x' : ℤ) - (evalHalfPal g n x : ℤ) = ∑ i : Fin n, Δ i := by
    simp only [evalHalfPal, evalWord, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow,
      ← Finset.sum_sub_distrib, Δ]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  let S_low : Finset (Fin n) := (U ×ˢ Finset.univ).image lowIdx
  let S_high : Finset (Fin n) := (U ×ˢ Finset.univ).image highIdx
  have hdisj : Disjoint S_low S_high := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    rw [Finset.mem_image] at hi1 hi2
    obtain ⟨p₁, _, rfl⟩ := hi1
    obtain ⟨p₂, _, hp2⟩ := hi2
    have hv := congrArg Fin.val hp2
    have hf1 := h_word_fit p₁.1 p₁.2
    have hf2 := h_word_fit p₂.1 p₂.2
    dsimp [lowIdx, highIdx] at hv
    omega
  have hzero : ∀ i : Fin n, i ∉ S_low ∪ S_high → Δ i = 0 := by
    intro i hi
    have heq_word : halfToWord x' i = halfToWord x i := by
      dsimp only [halfToWord]
      split_ifs with hr
      · rw [hx_fst]
      · set r := min i.1 (n - 1 - i.1)
        have hrb : r - 1 < (n - 1) / 2 := halfToWord_idx_lt i hr
        let b : Fin ((n - 1) / 2) := ⟨r - 1, hrb⟩
        by_cases hb : b ∈ Set.range emb
        · obtain ⟨⟨j, s⟩, hjs⟩ := hb
          have hr_eq : r = (j.1 + 1) * L + s.1 := by
            have hv := congrArg Fin.val hjs
            rw [hemb j s] at hv
            have hr_ge : 1 ≤ r := Nat.pos_of_ne_zero hr
            have hjs_ge : 1 ≤ (j.1 + 1) * L + s.1 :=
              le_trans (by omega) (Nat.le_trans (Nat.le_mul_of_pos_left L (Nat.succ_pos _)) (Nat.le_add_right _ _))
            dsimp [b] at hv
            omega
          by_cases hjU : j ∈ U
          · exfalso
            apply hi
            rw [Finset.mem_union]
            have hmin : r = i.1 ∨ r = n - 1 - i.1 := min_choice i.1 (n - 1 - i.1)
            rcases hmin with hri | hri
            · left
              rw [Finset.mem_image]
              exact ⟨(j, s), Finset.mem_product.mpr ⟨hjU, Finset.mem_univ _⟩,
                Fin.ext (by dsimp [lowIdx]; omega)⟩
            · right
              rw [Finset.mem_image]
              exact ⟨(j, s), Finset.mem_product.mpr ⟨hjU, Finset.mem_univ _⟩,
                Fin.ext (by dsimp [highIdx]; have := h_word_fit j s; omega)⟩
          · change x'.2 b = x.2 b
            rw [← hjs]
            exact hx_blk_out j hjU s
        · exact hx_rest b hb
    simp [Δ, heq_word]
  rw [hdiff_eq]
  have hsub := (Finset.sum_subset (Finset.subset_univ (S_low ∪ S_high))
    (fun i _ hi => hzero i hi)).symm
  rw [hsub, Finset.sum_union hdisj]
  have hsum_low : ∑ i ∈ S_low, Δ i =
      ∑ j ∈ U, (g : ℤ) ^ ((j.1 + 1) * L) * (blockVal g blk' - blockVal g blk) := by
    rw [Finset.sum_image (fun p₁ _ p₂ _ h => hlow_inj h), Finset.sum_product]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [blockVal, blockVal, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    have hf := h_word_fit j s
    have hw_eq : halfToWord x (lowIdx (j, s)) = x.2 (emb (j, s)) ∧
        halfToWord x' (lowIdx (j, s)) = x'.2 (emb (j, s)) := by
      have hmin : min ((j.1 + 1) * L + s.1) (n - 1 - ((j.1 + 1) * L + s.1)) =
          (j.1 + 1) * L + s.1 := by omega
      have hge1 : (j.1 + 1) * L + s.1 ≠ 0 := by
        have : 1 ≤ (j.1 + 1) * L := Nat.le_trans (by omega) (Nat.le_mul_of_pos_left L (Nat.succ_pos _))
        omega
      constructor <;>
      · dsimp only [halfToWord, lowIdx]
        split_ifs with hr
        · omega
        · exact congrArg _ (by ext; dsimp; rw [hemb j s]; omega)
    obtain ⟨h1, h2⟩ := hw_eq
    obtain ⟨hb1, hb2⟩ := hx_blk_in j hj s
    dsimp only [Δ]
    rw [h1, h2, hb1, hb2]
    dsimp [lowIdx]
    rw [pow_add]
    ring
  have hsum_high : ∑ i ∈ S_high, Δ i =
      ∑ j ∈ U, (g : ℤ) ^ (n - (j.1 + 1) * L - L) * (revBlockVal g blk' - revBlockVal g blk) := by
    rw [Finset.sum_image (fun p₁ _ p₂ _ h => hhigh_inj h), Finset.sum_product]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [revBlockVal, revBlockVal, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    have hf := h_word_fit j s
    have hw_eq : halfToWord x (highIdx (j, s)) = x.2 (emb (j, s)) ∧
        halfToWord x' (highIdx (j, s)) = x'.2 (emb (j, s)) := by
      have hmin : min (n - 1 - ((j.1 + 1) * L + s.1)) (n - 1 - (n - 1 - ((j.1 + 1) * L + s.1))) =
          (j.1 + 1) * L + s.1 := by omega
      have hge1 : (j.1 + 1) * L + s.1 ≠ 0 := by
        have : 1 ≤ (j.1 + 1) * L := Nat.le_trans (by omega) (Nat.le_mul_of_pos_left L (Nat.succ_pos _))
        omega
      constructor <;>
      · dsimp only [halfToWord, highIdx]
        split_ifs with hr
        · omega
        · exact congrArg _ (by ext; dsimp; rw [hemb j s]; omega)
    obtain ⟨h1, h2⟩ := hw_eq
    obtain ⟨hb1, hb2⟩ := hx_blk_in j hj s
    dsimp only [Δ]
    rw [h1, h2, hb1, hb2]
    dsimp [highIdx]
    have hjL : (j.1 + 1) * L + L ≤ n := by nlinarith [j.isLt, hn_mul]
    have hexp : n - 1 - ((j.1 + 1) * L + s.1) = (n - (j.1 + 1) * L - L) + (L - 1 - s.1) := by
      have hs := s.isLt
      omega
    rw [hexp, pow_add]
    ring
  rw [hsum_low, hsum_high, ← Finset.sum_add_distrib]

/-! ### Proof of Theorem 8 -/

lemma real_log_two_ge_quarter : (1 / 4 : ℝ) ≤ Real.log 2 := by
  linarith [Real.log_two_gt_d9]

lemma real_log_two_le_three_quarters : Real.log 2 ≤ (3 / 4 : ℝ) := by
  linarith [Real.log_two_lt_d9]

theorem card_palSet_add_le_exp {g n m : ℕ} (hg : 2 ≤ g) (hm : 1 ≤ m) (hmn : m ≤ n) :
    let d := n - m
    let t := m / (2 * (d + 2)) - 1
    ((palSet g n + palSet g m).card : ℝ) ≤
      2 * Real.exp (- (t : ℝ) / (8 * (g : ℝ) ^ (2 * d + 4))) *
        ((palSet g n).card : ℝ) * ((palSet g m).card : ℝ) := by
  intro d t
  by_cases ht0 : t = 0
  · simp only [ht0, Nat.cast_zero, neg_zero, zero_div, Real.exp_zero, mul_one]
    have hmul : ((palSet g n + palSet g m).card : ℝ) ≤
        ((palSet g n).card : ℝ) * ((palSet g m).card : ℝ) := by
      exact_mod_cast card_palSet_add_le_mul g n m
    have hnonneg : (0 : ℝ) ≤ ((palSet g n).card : ℝ) * ((palSet g m).card : ℝ) := by positivity
    linarith
  · have ht : 1 ≤ t := Nat.pos_of_ne_zero ht0
    set L := d + 2
    have hL : 2 ≤ L := by omega
    have hn : 1 ≤ n := hm.trans hmn
    have hm_bound : 2 * (t + 1) * L ≤ m := by
      have hdiv : t + 1 ≤ m / (2 * L) := by
        dsimp [t, L] at ht ⊢
        omega
      have hmul := Nat.mul_le_mul_right (2 * L) hdiv
      have hdm := Nat.div_mul_le_self m (2 * L)
      linarith
    have hn_bound : 2 * (t + 1) * L ≤ n := hm_bound.trans hmn
    have hfit_m : ∀ (j : Fin t) (s : Fin L), (j.1 + 1) * L + s.1 - 1 < (m - 1) / 2 :=
      fun j s => block_fit_bound hL ht hm_bound j s
    have hfit_n : ∀ (j : Fin t) (s : Fin L), (j.1 + 1) * L + s.1 - 1 < (n - 1) / 2 :=
      fun j s => lt_of_lt_of_le (hfit_m j s) (by omega)
    let emb_n : Fin t × Fin L ↪ Fin ((n - 1) / 2) := blockEmb (by omega) hfit_n
    let emb_m : Fin t × Fin L ↪ Fin ((m - 1) / 2) := blockEmb (by omega) hfit_m
    have hemb_n : ∀ j s, (emb_n (j, s)).1 = (j.1 + 1) * L + s.1 - 1 := fun _ _ => rfl
    have hemb_m : ∀ j s, (emb_m (j, s)).1 = (j.1 + 1) * L + s.1 - 1 := fun _ _ => rfl
    -- Define J_hp on HalfPal g n × HalfPal g m and push forward via halfPalEquiv
    let P := palSet g n
    let Q := palSet g m
    let eP : HalfPal g n ≃ P :=
      { toFun := fun x => ⟨evalHalfPal g n x, evalHalfPal_mem_palSet hg hn x⟩
        invFun := fun p => Classical.choose (evalHalfPal_surjOn_palSet hg hn p.1 p.2)
        left_inv := fun x => evalHalfPal_injective hg hn
          (Classical.choose_spec (evalHalfPal_surjOn_palSet hg hn (evalHalfPal g n x)
            (evalHalfPal_mem_palSet hg hn x)))
        right_inv := fun p => Subtype.ext
          (Classical.choose_spec (evalHalfPal_surjOn_palSet hg hn p.1 p.2)) }
    let eQ : HalfPal g m ≃ Q :=
      { toFun := fun y => ⟨evalHalfPal g m y, evalHalfPal_mem_palSet hg hm y⟩
        invFun := fun q => Classical.choose (evalHalfPal_surjOn_palSet hg hm q.1 q.2)
        left_inv := fun y => evalHalfPal_injective hg hm
          (Classical.choose_spec (evalHalfPal_surjOn_palSet hg hm (evalHalfPal g m y)
            (evalHalfPal_mem_palSet hg hm y)))
        right_inv := fun q => Subtype.ext
          (Classical.choose_spec (evalHalfPal_surjOn_palSet hg hm q.1 q.2)) }
    let J_hp (x : HalfPal g n) (y : HalfPal g m) : Finset (Fin t) :=
      Finset.univ.filter fun j : Fin t =>
        (fun s : Fin L => x.2 (emb_n (j, s))) = blockA d g hg ∧
        (fun s : Fin L => y.2 (emb_m (j, s))) = blockB d g hg
    let J_pq (p q : ℕ) : Finset (Fin t) :=
      if hp : p ∈ P then if hq : q ∈ Q then J_hp (eP.symm ⟨p, hp⟩) (eQ.symm ⟨q, hq⟩)
      else ∅ else ∅
    let S (p q : ℕ) : ℕ := (J_pq p q).card
    have hJ_eval : ∀ (x : HalfPal g n) (y : HalfPal g m),
        J_pq (evalHalfPal g n x) (evalHalfPal g m y) = J_hp x y := by
      intro x y
      have hp : evalHalfPal g n x ∈ P := evalHalfPal_mem_palSet hg hn x
      have hq : evalHalfPal g m y ∈ Q := evalHalfPal_mem_palSet hg hm y
      dsimp only [J_pq]
      rw [dif_pos hp, dif_pos hq]
      have hx : eP.symm ⟨evalHalfPal g n x, hp⟩ = x := eP.left_inv x
      have hy : eQ.symm ⟨evalHalfPal g m y, hq⟩ = y := eQ.left_inv y
      rw [hx, hy]
    set M : ℝ := (g : ℝ) ^ (2 * d + 4)
    have hg_pos : (0 : ℝ) < (g : ℝ) := by positivity
    have hM_pos : 0 < M := by positivity
    have hM_ge : (16 : ℝ) ≤ M := by
      have hg2 : (2 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
      calc (16 : ℝ) = (2 : ℝ) ^ 4 := by norm_num
        _ ≤ (2 : ℝ) ^ (2 * d + 4) := by gcongr; norm_num; omega
        _ ≤ (g : ℝ) ^ (2 * d + 4) := by gcongr
    set μ : ℝ := (t : ℝ) / M
    have hμ_nonneg : 0 ≤ μ := by positivity
    have hexp_eq : - (t : ℝ) / (8 * (g : ℝ) ^ (2 * d + 4)) = - μ / 8 := by
      dsimp only [μ, M]
      ring
    rw [hexp_eq]
    let Good : Finset (ℕ × ℕ) := (P ×ˢ Q).filter (fun z => μ / 2 ≤ (S z.1 z.2 : ℝ))
    let Bad : Finset (ℕ × ℕ) := (P ×ˢ Q).filter (fun z => (S z.1 z.2 : ℝ) < μ / 2)
    have hPQ_sub : P + Q ⊆
        Good.image (fun z => z.1 + z.2) ∪ Bad.image (fun z => z.1 + z.2) := by
      intro w hw
      rw [Finset.add_def, Finset.mem_image] at hw
      obtain ⟨z, hz, rfl⟩ := hw
      rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
      by_cases hgood : μ / 2 ≤ (S z.1 z.2 : ℝ)
      · left; exact ⟨z, Finset.mem_filter.mpr ⟨hz, hgood⟩, rfl⟩
      · right; exact ⟨z, Finset.mem_filter.mpr ⟨hz, lt_of_not_ge hgood⟩, rfl⟩
    have hcard_split : ((P + Q).card : ℝ) ≤
        ((Good.image (fun z => z.1 + z.2)).card : ℝ) +
          ((Bad.image (fun z => z.1 + z.2)).card : ℝ) := by
      have hnat : (P + Q).card ≤
          (Good.image (fun z => z.1 + z.2)).card + (Bad.image (fun z => z.1 + z.2)).card :=
        (Finset.card_le_card hPQ_sub).trans (Finset.card_union_le _ _)
      exact_mod_cast hnat
    -- Part A: Good bound via block-swap fiber lower bound
    have hGood_bound : ((Good.image (fun z => z.1 + z.2)).card : ℝ) ≤
        Real.exp (- μ / 8) * (P.card : ℝ) * (Q.card : ℝ) := by
      let fib (w : ℕ) : Finset (ℕ × ℕ) := (P ×ˢ Q).filter (fun z => z.1 + z.2 = w)
      have hfib_le : ∀ w ∈ Good.image (fun z => z.1 + z.2),
          (1 : ℝ) ≤ Real.exp (- μ / 8) * (fib w).card := by
        intro w hw
        rw [Finset.mem_image] at hw
        obtain ⟨⟨p₀, q₀⟩, hmem, hw_eq⟩ := hw
        rw [Finset.mem_filter, Finset.mem_product] at hmem
        rcases hmem with ⟨⟨hp₀, hq₀⟩, hS_ge⟩
        let x₀ : HalfPal g n := eP.symm ⟨p₀, hp₀⟩
        let y₀ : HalfPal g m := eQ.symm ⟨q₀, hq₀⟩
        have hx₀_eval : evalHalfPal g n x₀ = p₀ :=
          congrArg Subtype.val (eP.apply_symm_apply ⟨p₀, hp₀⟩)
        have hy₀_eval : evalHalfPal g m y₀ = q₀ :=
          congrArg Subtype.val (eQ.apply_symm_apply ⟨q₀, hq₀⟩)
        have hJ₀ : J_pq p₀ q₀ = J_hp x₀ y₀ := by
          dsimp only [J_pq]
          rw [dif_pos hp₀, dif_pos hq₀]
        -- Swap map on U ⊆ J_hp x₀ y₀
        let swapPair (U : Finset (Fin t)) : ℕ × ℕ :=
          let sp_n := halfPalSplitEquiv emb_n x₀
          let sp_m := halfPalSplitEquiv emb_m y₀
          let blk_n' : Fin t → Fin L → Fin g := fun j => if j ∈ U then blockA' d g hg else sp_n.1 j
          let blk_m' : Fin t → Fin L → Fin g := fun j => if j ∈ U then blockB' d g hg else sp_m.1 j
          (evalHalfPal g n ((halfPalSplitEquiv emb_n).symm (blk_n', sp_n.2)),
           evalHalfPal g m ((halfPalSplitEquiv emb_m).symm (blk_m', sp_m.2)))
        have hswap_mem : ∀ U ∈ (J_hp x₀ y₀).powerset, swapPair U ∈ fib w := by
          intro U hU
          rw [Finset.mem_powerset] at hU
          dsimp only [fib, swapPair]
          rw [Finset.mem_filter, Finset.mem_product]
          set x' := (halfPalSplitEquiv emb_n).symm
            (fun j => if j ∈ U then blockA' d g hg else (halfPalSplitEquiv emb_n x₀).1 j,
             (halfPalSplitEquiv emb_n x₀).2)
          set y' := (halfPalSplitEquiv emb_m).symm
            (fun j => if j ∈ U then blockB' d g hg else (halfPalSplitEquiv emb_m y₀).1 j,
             (halfPalSplitEquiv emb_m y₀).2)
          refine ⟨⟨evalHalfPal_mem_palSet hg hn x', evalHalfPal_mem_palSet hg hm y'⟩, ?_⟩
          have hdiff_n := evalHalfPal_blockSwap_diff hL hn_bound emb_n hemb_n x₀ x' U
            (blockA d g hg) (blockA' d g hg) rfl
            (fun b hb => halfPalSplitEquiv_symm_compl emb_n _ _ hb)
            (fun j hj s => by
              dsimp only [x']
              rw [halfPalSplitEquiv_symm_emb]
              simp only [hj, ↓reduceIte]
              rfl)
            (fun j hj s => by
              have hJ := hU hj
              simp only [J_hp, Finset.mem_filter, Finset.mem_univ, true_and] at hJ
              constructor
              · exact congrFun hJ.1 s
              · dsimp only [x']
                rw [halfPalSplitEquiv_symm_emb]
                simp [hj])
          have hdiff_m := evalHalfPal_blockSwap_diff hL hm_bound emb_m hemb_m y₀ y' U
            (blockB d g hg) (blockB' d g hg) rfl
            (fun b hb => halfPalSplitEquiv_symm_compl emb_m _ _ hb)
            (fun j hj s => by
              dsimp only [y']
              rw [halfPalSplitEquiv_symm_emb]
              simp only [hj, ↓reduceIte]
              rfl)
            (fun j hj s => by
              have hJ := hU hj
              simp only [J_hp, Finset.mem_filter, Finset.mem_univ, true_and] at hJ
              constructor
              · exact congrFun hJ.2 s
              · dsimp only [y']
                rw [halfPalSplitEquiv_symm_emb]
                simp [hj])
          have hsum_zero : ((evalHalfPal g n x' : ℤ) - (evalHalfPal g n x₀ : ℤ)) +
              ((evalHalfPal g m y' : ℤ) - (evalHalfPal g m y₀ : ℤ)) = 0 := by
            rw [hdiff_n, hdiff_m, ← Finset.sum_add_distrib]
            refine Finset.sum_eq_zero fun j _ => ?_
            have hexp : n - (j.1 + 1) * L - L = (m - (j.1 + 1) * L - L) + d := by
              have hj_lt : (j.1 + 1) * L + L ≤ (t + 1) * L := by
                have := Nat.mul_le_mul_right L (by omega : j.1 + 1 + 1 ≤ t + 1)
                linarith
              have hm_ge : (j.1 + 1) * L + L ≤ m := by
                have : (t + 1) * L ≤ 2 * ((t + 1) * L) := by omega
                linarith [hm_bound, this]
              dsimp [d]
              omega
            rw [hexp, pow_add]
            have hl := block_collision_lower d g hg
            have hu := block_collision_upper d g hg
            calc
              ((g : ℤ) ^ ((j.1 + 1) * L) * (blockVal g (blockA' d g hg) - blockVal g (blockA d g hg)) +
                (g : ℤ) ^ (m - (j.1 + 1) * L - L) * (g : ℤ) ^ d *
                  (revBlockVal g (blockA' d g hg) - revBlockVal g (blockA d g hg))) +
                ((g : ℤ) ^ ((j.1 + 1) * L) * (blockVal g (blockB' d g hg) - blockVal g (blockB d g hg)) +
                  (g : ℤ) ^ (m - (j.1 + 1) * L - L) *
                    (revBlockVal g (blockB' d g hg) - revBlockVal g (blockB d g hg)))
                = (g : ℤ) ^ ((j.1 + 1) * L) *
                    ((blockVal g (blockA' d g hg) - blockVal g (blockA d g hg)) +
                      (blockVal g (blockB' d g hg) - blockVal g (blockB d g hg))) +
                  (g : ℤ) ^ (m - (j.1 + 1) * L - L) *
                    ((g : ℤ) ^ d * (revBlockVal g (blockA' d g hg) - revBlockVal g (blockA d g hg)) +
                      (revBlockVal g (blockB' d g hg) - revBlockVal g (blockB d g hg))) := by ring
              _ = 0 := by rw [hl, hu]; ring
          have heq_nat : evalHalfPal g n x' + evalHalfPal g m y' =
              evalHalfPal g n x₀ + evalHalfPal g m y₀ := by omega
          rw [heq_nat, hx₀_eval, hy₀_eval, hw_eq]
        have hswap_inj : Set.InjOn swapPair (J_hp x₀ y₀).powerset := by
          intro U₁ hU₁ U₂ hU₂ heq
          rw [Finset.mem_coe, Finset.mem_powerset] at hU₁ hU₂
          have h2 : (swapPair U₁).2 = (swapPair U₂).2 := congrArg Prod.snd heq
          dsimp only [swapPair] at h2
          have hy_eq := evalHalfPal_injective hg hm h2
          have hsp_eq := congrArg (fun y => (halfPalSplitEquiv emb_m y).1) hy_eq
          rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at hsp_eq
          ext j
          have hj_eq := congrArg (fun f => f j ⟨0, by omega⟩) hsp_eq
          dsimp only at hj_eq
          by_cases hj1 : j ∈ U₁ <;> by_cases hj2 : j ∈ U₂
          · simp [hj1, hj2]
          · exfalso
            simp only [hj1, ↓reduceIte, hj2] at hj_eq
            have hJ2 := hU₁ hj1
            simp only [J_hp, Finset.mem_filter, Finset.mem_univ, true_and] at hJ2
            have hsp0 : (halfPalSplitEquiv emb_m y₀).1 j ⟨0, by omega⟩ = blockB d g hg ⟨0, by omega⟩ := by
              have := congrFun hJ2.2 ⟨0, by omega⟩
              exact this
            rw [hsp0] at hj_eq
            have hval := congrArg Fin.val hj_eq
            simp [blockB', blockB] at hval
          · exfalso
            simp only [hj1, ↓reduceIte, hj2] at hj_eq
            have hJ1 := hU₂ hj2
            simp only [J_hp, Finset.mem_filter, Finset.mem_univ, true_and] at hJ1
            have hsp0 : (halfPalSplitEquiv emb_m y₀).1 j ⟨0, by omega⟩ = blockB d g hg ⟨0, by omega⟩ := by
              have := congrFun hJ1.2 ⟨0, by omega⟩
              exact this
            rw [hsp0] at hj_eq
            have hval := congrArg Fin.val hj_eq
            simp [blockB', blockB] at hval
          · simp [hj1, hj2]
        have hcard_fib : 2 ^ (J_hp x₀ y₀).card ≤ (fib w).card := by
          rw [← Finset.card_powerset]
          exact Finset.card_le_card_of_injOn swapPair hswap_mem hswap_inj
        have hS_eq : S p₀ q₀ = (J_hp x₀ y₀).card := by simp [S, hJ₀]
        have hpow_real : Real.exp (μ / 8) ≤ ((fib w).card : ℝ) := by
          have h1 : (2 : ℝ) ^ (S p₀ q₀) ≤ ((fib w).card : ℝ) := by
            rw [hS_eq]
            exact_mod_cast hcard_fib
          have h2 : Real.exp (μ / 8) ≤ Real.exp ((μ / 2) * Real.log 2) := by
            refine Real.exp_le_exp.mpr ?_
            have hlog := real_log_two_ge_quarter
            nlinarith
          have h3 : Real.exp ((μ / 2) * Real.log 2) ≤ Real.exp ((S p₀ q₀ : ℝ) * Real.log 2) := by
            refine Real.exp_le_exp.mpr ?_
            have hlog_pos : 0 ≤ Real.log 2 := by linarith [real_log_two_ge_quarter]
            exact mul_le_mul_of_nonneg_right hS_ge hlog_pos
          have h4 : Real.exp ((S p₀ q₀ : ℝ) * Real.log 2) = (2 : ℝ) ^ (S p₀ q₀) := by
            rw [mul_comm (S p₀ q₀ : ℝ) (Real.log 2),
              ← Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast]
          linarith
        calc
          (1 : ℝ) = Real.exp (- μ / 8) * Real.exp (μ / 8) := by
              rw [← Real.exp_add]; ring_nf; simp
          _ ≤ Real.exp (- μ / 8) * ((fib w).card : ℝ) := by
              gcongr
      calc
        ((Good.image (fun z => z.1 + z.2)).card : ℝ)
          = ∑ _w ∈ Good.image (fun z => z.1 + z.2), (1 : ℝ) := by simp
        _ ≤ ∑ w ∈ Good.image (fun z => z.1 + z.2), Real.exp (- μ / 8) * ((fib w).card : ℝ) :=
            Finset.sum_le_sum hfib_le
        _ = Real.exp (- μ / 8) * ∑ w ∈ Good.image (fun z => z.1 + z.2), ((fib w).card : ℝ) := by
            rw [← Finset.mul_sum]
        _ ≤ Real.exp (- μ / 8) * ∑ w ∈ (P ×ˢ Q).image (fun z => z.1 + z.2), ((fib w).card : ℝ) := by
            refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
            have hsub_img : Good.image (fun z => z.1 + z.2) ⊆
                (P ×ˢ Q).image (fun z => z.1 + z.2) :=
              Finset.image_subset_image (Finset.filter_subset _ _)
            exact Finset.sum_le_sum_of_subset_of_nonneg hsub_img (fun _ _ _ => by positivity)
        _ = Real.exp (- μ / 8) * ((P ×ˢ Q).card : ℝ) := by
            congr 1
            norm_cast
            exact (Finset.card_eq_sum_card_fiberwise (fun _ hz => Finset.mem_image_of_mem _ hz)).symm
        _ = Real.exp (- μ / 8) * (P.card : ℝ) * (Q.card : ℝ) := by
            rw [Finset.card_product, Nat.cast_mul]
            ring
    -- Part B: Exact MGF identity and Bad bound
    have hMGF : (∑ z ∈ P ×ˢ Q, (1 / 2 : ℝ) ^ S z.1 z.2) =
        (P.card : ℝ) * (Q.card : ℝ) * (1 - 1 / (2 * M)) ^ t := by
      have hPQ_eq : (∑ z ∈ P ×ˢ Q, (1 / 2 : ℝ) ^ S z.1 z.2) =
          ∑ x : HalfPal g n, ∑ y : HalfPal g m, (1 / 2 : ℝ) ^ (J_hp x y).card := by
        rw [Finset.sum_product]
        have hP_eq : P = Finset.univ.map ⟨evalHalfPal g n, evalHalfPal_injective hg hn⟩ :=
          palSet_eq_map hg hn
        have hQ_eq : Q = Finset.univ.map ⟨evalHalfPal g m, evalHalfPal_injective hg hm⟩ :=
          palSet_eq_map hg hm
        conv_lhs => rw [hP_eq, Finset.sum_map]
        refine Finset.sum_congr rfl fun x _ => ?_
        conv_lhs => rw [hQ_eq, Finset.sum_map]
        refine Finset.sum_congr rfl fun y _ => ?_
        simp [S, hJ_eval x y]
      rw [hPQ_eq]
      let E_n := halfPalSplitEquiv (g := g) emb_n
      let E_m := halfPalSplitEquiv (g := g) emb_m
      have hsplit_sum : (∑ x : HalfPal g n, ∑ y : HalfPal g m, (1 / 2 : ℝ) ^ (J_hp x y).card) =
          ∑ a : (Fin t → Fin L → Fin g) ×
            ({ d : Fin g // d.1 ≠ 0 } × ({ b : Fin ((n - 1) / 2) // b ∉ Set.range emb_n } → Fin g)),
          ∑ b : (Fin t → Fin L → Fin g) ×
            ({ d : Fin g // d.1 ≠ 0 } × ({ b : Fin ((m - 1) / 2) // b ∉ Set.range emb_m } → Fin g)),
            (1 / 2 : ℝ) ^ (Finset.univ.filter fun j : Fin t =>
              a.1 j = blockA d g hg ∧ b.1 j = blockB d g hg).card := by
        rw [← Equiv.sum_comp E_n.symm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Equiv.sum_comp E_m.symm]
        refine Finset.sum_congr rfl fun b _ => ?_
        congr 2
        refine Finset.filter_congr fun j _ => ?_
        have ha : (fun s : Fin L => (E_n.symm a).2 (emb_n (j, s))) = a.1 j := by
          ext s
          exact congrArg Fin.val (halfPalSplitEquiv_symm_emb emb_n a.1 a.2 j s)
        have hb : (fun s : Fin L => (E_m.symm b).2 (emb_m (j, s))) = b.1 j := by
          ext s
          exact congrArg Fin.val (halfPalSplitEquiv_symm_emb emb_m b.1 b.2 j s)
        rw [ha, hb]
      rw [hsplit_sum]
      -- Factor out the rest components
      let Rest_n := { d : Fin g // d.1 ≠ 0 } ×
        ({ b : Fin ((n - 1) / 2) // b ∉ Set.range emb_n } → Fin g)
      let Rest_m := { d : Fin g // d.1 ≠ 0 } ×
        ({ b : Fin ((m - 1) / 2) // b ∉ Set.range emb_m } → Fin g)
      have hfactor_rest :
          (∑ a : (Fin t → Fin L → Fin g) × Rest_n,
           ∑ b : (Fin t → Fin L → Fin g) × Rest_m,
            (1 / 2 : ℝ) ^ (Finset.univ.filter fun j : Fin t =>
              a.1 j = blockA d g hg ∧ b.1 j = blockB d g hg).card) =
          (Fintype.card Rest_n : ℝ) * (Fintype.card Rest_m : ℝ) *
            (∑ f : Fin t → Fin L → Fin g, ∑ k : Fin t → Fin L → Fin g,
              (1 / 2 : ℝ) ^ (Finset.univ.filter fun j : Fin t =>
                f j = blockA d g hg ∧ k j = blockB d g hg).card) := by
        rw [Fintype.sum_prod_type]
        simp_rw [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ← Finset.mul_sum]
        rw [mul_assoc]
      rw [hfactor_rest]
      -- Combine (f, k) into F : Fin t → (Fin L → Fin g) × (Fin L → Fin g)
      let α := (Fin L → Fin g) × (Fin L → Fin g)
      let ePair : (Fin t → α) ≃ (Fin t → Fin L → Fin g) × (Fin t → Fin L → Fin g) :=
        Equiv.arrowProdEquivProdArrow (Fin t) (fun _ => Fin L → Fin g) (fun _ => Fin L → Fin g)
      have hpair_sum :
          (∑ f : Fin t → Fin L → Fin g, ∑ k : Fin t → Fin L → Fin g,
            (1 / 2 : ℝ) ^ (Finset.univ.filter fun j : Fin t =>
              f j = blockA d g hg ∧ k j = blockB d g hg).card) =
          ∑ F : Fin t → α, ∏ j : Fin t,
            if F j = (blockA d g hg, blockB d g hg) then (1 / 2 : ℝ) else 1 := by
        rw [← Fintype.sum_prod_type', ← Equiv.sum_comp ePair]
        refine Finset.sum_congr rfl fun F _ => ?_
        have hcard_sum : (Finset.univ.filter fun j : Fin t =>
            (ePair F).1 j = blockA d g hg ∧ (ePair F).2 j = blockB d g hg).card =
            ∑ j : Fin t, if F j = (blockA d g hg, blockB d g hg) then 1 else 0 := by
          rw [Finset.card_filter]
          refine Finset.sum_congr rfl fun j _ => ?_
          have hiff : ((F j).1 = blockA d g hg ∧ (F j).2 = blockB d g hg) ↔
              F j = (blockA d g hg, blockB d g hg) :=
            ⟨fun ⟨h1, h2⟩ => Prod.ext h1 h2, fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩⟩
          simp only [ePair, Equiv.arrowProdEquivProdArrow_apply, hiff]
        rw [hcard_sum, ← Finset.prod_pow_eq_pow_sum]
        refine Finset.prod_congr rfl fun j _ => ?_
        split_ifs <;> simp
      rw [hpair_sum,
        ← Fintype.sum_pow (fun x : α => if x = (blockA d g hg, blockB d g hg) then (1 / 2 : ℝ) else 1) t]
      let x₀ : α := (blockA d g hg, blockB d g hg)
      have hα_sum : (∑ x : α, if x = x₀ then (1 / 2 : ℝ) else 1) =
          M * (1 - 1 / (2 * M)) := by
        have hcard_α : (Fintype.card α : ℝ) = M := by
          dsimp [α, M]
          rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
          push_cast
          have hexp : L + L = 2 * d + 4 := by dsimp [L]; omega
          rw [← pow_add, hexp]
        have hite : (∑ x : α, if x = x₀ then (1 / 2 : ℝ) else 1) =
            ∑ x : α, ((1 : ℝ) - if x = x₀ then (1 / 2 : ℝ) else 0) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          split_ifs <;> norm_num
        rw [hite, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          mul_one, hcard_α]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        have hM_ne : M ≠ 0 := hM_pos.ne'
        field_simp
      rw [hα_sum]
      have hcard_prod : (Fintype.card Rest_n : ℝ) * (Fintype.card Rest_m : ℝ) * M ^ t =
          (P.card : ℝ) * (Q.card : ℝ) := by
        have hP_card : (P.card : ℝ) = (Fintype.card Rest_n : ℝ) * ((g : ℝ) ^ L) ^ t := by
          have hc : P.card = Fintype.card (HalfPal g n) := by
            dsimp only [P]
            rw [palSet_eq_map hg hn, Finset.card_map, Finset.card_univ]
          rw [hc, Fintype.card_congr E_n, Fintype.card_prod, Fintype.card_fun, Fintype.card_fun,
            Fintype.card_fin, Fintype.card_fin, Fintype.card_fin]
          dsimp only [Rest_n]
          push_cast
          ring
        have hQ_card : (Q.card : ℝ) = (Fintype.card Rest_m : ℝ) * ((g : ℝ) ^ L) ^ t := by
          have hc : Q.card = Fintype.card (HalfPal g m) := by
            dsimp only [Q]
            rw [palSet_eq_map hg hm, Finset.card_map, Finset.card_univ]
          rw [hc, Fintype.card_congr E_m, Fintype.card_prod, Fintype.card_fun, Fintype.card_fun,
            Fintype.card_fin, Fintype.card_fin, Fintype.card_fin]
          dsimp only [Rest_m]
          push_cast
          ring
        have hM_eq : M = (g : ℝ) ^ L * (g : ℝ) ^ L := by
          dsimp [M, L]
          rw [← pow_add, show (d + 2) + (d + 2) = 2 * d + 4 by omega]
        rw [hP_card, hQ_card, hM_eq, mul_pow]
        ring
      calc
        (Fintype.card Rest_n : ℝ) * (Fintype.card Rest_m : ℝ) * (M * (1 - 1 / (2 * M))) ^ t
          = ((Fintype.card Rest_n : ℝ) * (Fintype.card Rest_m : ℝ) * M ^ t) *
              (1 - 1 / (2 * M)) ^ t := by rw [mul_pow]; ring
        _ = (P.card : ℝ) * (Q.card : ℝ) * (1 - 1 / (2 * M)) ^ t := by rw [hcard_prod]
    have hBad_bound : ((Bad.image (fun z => z.1 + z.2)).card : ℝ) ≤
        Real.exp (- μ / 8) * (P.card : ℝ) * (Q.card : ℝ) := by
      have hBad_term : ∀ z ∈ Bad,
          (1 : ℝ) ≤ Real.exp ((μ / 2) * Real.log 2) * (1 / 2 : ℝ) ^ (S z.1 z.2) := by
        intro z hz
        have hlt : (S z.1 z.2 : ℝ) < μ / 2 := (Finset.mem_filter.mp hz).2
        have hpow_exp : (1 / 2 : ℝ) ^ (S z.1 z.2) =
            Real.exp (- ((S z.1 z.2 : ℝ) * Real.log 2)) := by
          rw [one_div, inv_pow, ← Real.rpow_natCast,
            Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
            mul_comm (Real.log 2) (S z.1 z.2 : ℝ), ← Real.exp_neg]
        rw [hpow_exp, ← Real.exp_add]
        refine Real.one_le_exp ?_
        have hlog_pos : 0 ≤ Real.log 2 := by linarith [real_log_two_ge_quarter]
        nlinarith
      have hBad_sum : (Bad.card : ℝ) ≤
          Real.exp ((μ / 2) * Real.log 2) * ∑ z ∈ P ×ˢ Q, (1 / 2 : ℝ) ^ S z.1 z.2 := by
        calc
          (Bad.card : ℝ)
            = ∑ _z ∈ Bad, (1 : ℝ) := by simp
          _ ≤ ∑ z ∈ Bad, Real.exp ((μ / 2) * Real.log 2) * (1 / 2 : ℝ) ^ (S z.1 z.2) :=
              Finset.sum_le_sum hBad_term
          _ = Real.exp ((μ / 2) * Real.log 2) * ∑ z ∈ Bad, (1 / 2 : ℝ) ^ (S z.1 z.2) := by
              rw [← Finset.mul_sum]
          _ ≤ Real.exp ((μ / 2) * Real.log 2) * ∑ z ∈ P ×ˢ Q, (1 / 2 : ℝ) ^ (S z.1 z.2) := by
              refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
              have hsub_bad : Bad ⊆ P ×ˢ Q := Finset.filter_subset _ _
              exact Finset.sum_le_sum_of_subset_of_nonneg hsub_bad
                (fun _ _ _ => pow_nonneg (by norm_num) _)
      have hmgf_exp : (1 - 1 / (2 * M)) ^ t ≤ Real.exp (- μ / 2) := by
        have hbase_le : 1 - 1 / (2 * M) ≤ Real.exp (- (1 / (2 * M))) := by
          linarith [Real.add_one_le_exp (- (1 / (2 * M)))]
        have hbase_nonneg : 0 ≤ 1 - 1 / (2 * M) := by
          have : 1 / (2 * M) ≤ 1 := by
            rw [div_le_one (mul_pos zero_lt_two hM_pos)]
            linarith
          linarith
        calc
          (1 - 1 / (2 * M)) ^ t
            ≤ (Real.exp (- (1 / (2 * M)))) ^ t := pow_le_pow_left₀ hbase_nonneg hbase_le t
          _ = Real.exp ((t : ℝ) * (- (1 / (2 * M)))) := (Real.exp_nat_mul _ t).symm
          _ = Real.exp (- μ / 2) := by
              congr 1
              dsimp only [μ]
              ring
      have hcombine_exp : Real.exp ((μ / 2) * Real.log 2) * Real.exp (- μ / 2) ≤
          Real.exp (- μ / 8) := by
        rw [← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        have hlog := real_log_two_le_three_quarters
        nlinarith
      have himg_le : ((Bad.image (fun z => z.1 + z.2)).card : ℝ) ≤ (Bad.card : ℝ) := by
        exact_mod_cast Finset.card_image_le
      have hBad_sum' : (Bad.card : ℝ) ≤ Real.exp ((μ / 2) * Real.log 2) *
          ((P.card : ℝ) * (Q.card : ℝ) * (1 - 1 / (2 * M)) ^ t) := by
        rw [← hMGF]
        exact hBad_sum
      have hPQ_nonneg : (0 : ℝ) ≤ (P.card : ℝ) * (Q.card : ℝ) :=
        mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      calc
        ((Bad.image (fun z => z.1 + z.2)).card : ℝ)
          ≤ (Bad.card : ℝ) := himg_le
        _ ≤ Real.exp ((μ / 2) * Real.log 2) *
              ((P.card : ℝ) * (Q.card : ℝ) * (1 - 1 / (2 * M)) ^ t) := hBad_sum'
        _ ≤ Real.exp ((μ / 2) * Real.log 2) *
              ((P.card : ℝ) * (Q.card : ℝ) * Real.exp (- μ / 2)) := by
            refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
            exact mul_le_mul_of_nonneg_left hmgf_exp hPQ_nonneg
        _ = (Real.exp ((μ / 2) * Real.log 2) * Real.exp (- μ / 2)) *
              ((P.card : ℝ) * (Q.card : ℝ)) := by ring
        _ ≤ Real.exp (- μ / 8) * ((P.card : ℝ) * (Q.card : ℝ)) :=
            mul_le_mul_of_nonneg_right hcombine_exp hPQ_nonneg
        _ = Real.exp (- μ / 8) * (P.card : ℝ) * (Q.card : ℝ) := by ring
    linarith


namespace AsymptoticsInternal

private lemma eventually_const_le_natCast_rpow {r : ℝ} (hr : 0 < r) (B : ℝ) :
    ∀ᶠ k : ℕ in atTop, B ≤ (k : ℝ) ^ r :=
  ((tendsto_rpow_atTop hr).comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop B)

private lemma eventually_mul_log_le_natCast_rpow {r C : ℝ} (hr : 0 < r) (hC : 0 < C) :
    ∀ᶠ k : ℕ in atTop, C * Real.log (k : ℝ) ≤ (k : ℝ) ^ r := by
  have h1 : ∀ᶠ k : ℕ in atTop, ‖Real.log (k : ℝ)‖ ≤ C⁻¹ * ‖(k : ℝ) ^ r‖ :=
    tendsto_natCast_atTop_atTop.eventually
      ((isLittleO_log_rpow_atTop hr).bound (inv_pos.mpr hC))
  filter_upwards [h1, eventually_ge_atTop 2] with k hk h2
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
  have hlog_nonneg : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg hk1
  have hrpow_nonneg : 0 ≤ (k : ℝ) ^ r := Real.rpow_nonneg (by linarith) r
  rw [Real.norm_of_nonneg hlog_nonneg, Real.norm_of_nonneg hrpow_nonneg] at hk
  calc
    C * Real.log (k : ℝ) ≤ C * (C⁻¹ * (k : ℝ) ^ r) := mul_le_mul_of_nonneg_left hk hC.le
    _ = (k : ℝ) ^ r := by rw [← mul_assoc, mul_inv_cancel₀ hC.ne', one_mul]

private lemma rpow_div_log_eq_rpow {b x c : ℝ} (hb : 1 < b) (hx : 0 < x) :
    b ^ (c * Real.log x / Real.log b) = x ^ c := by
  have hb_pos : 0 < b := zero_lt_one.trans hb
  have hlog : Real.log b ≠ 0 := (Real.log_pos hb).ne'
  rw [Real.rpow_def_of_pos hb_pos, Real.rpow_def_of_pos hx]
  congr 1
  field_simp

private lemma nat_div_sub_one_ge (a b : ℕ) (hb : 0 < b) :
    (a : ℝ) / (b : ℝ) - 2 ≤ ((a / b - 1 : ℕ) : ℝ) := by
  have hbR : (0 : ℝ) < (b : ℝ) := Nat.cast_pos.mpr hb
  have hlt : (a : ℝ) < (b : ℝ) * (((a / b : ℕ) : ℝ) + 1) := by
    exact_mod_cast Nat.lt_mul_div_succ a hb
  have hdiv : (a : ℝ) / (b : ℝ) < ((a / b : ℕ) : ℝ) + 1 :=
    (div_lt_iff₀ hbR).mpr (by linarith)
  by_cases h0 : a / b = 0
  · rw [h0] at hdiv ⊢
    simp only [Nat.cast_zero, zero_add, zero_tsub] at hdiv ⊢
    linarith
  · have h1 : 1 ≤ a / b := Nat.pos_of_ne_zero h0
    rw [Nat.cast_sub h1, Nat.cast_one]
    linarith

private lemma sum_off_diag_le (g : ℕ) (hg : 2 ≤ g) (palSet : ℕ → ℕ → Finset ℕ)
    (h_sum_card : ∀ N : ℕ, (∑ n ∈ Finset.Icc 1 N, (palSet g n).card) ≤ 2 * g ^ ((N + 1) / 2))
    (h_add_mul : ∀ n m : ℕ, (palSet g n + palSet g m).card ≤ (palSet g n).card * (palSet g m).card)
    (k M₀ : ℕ) :
    (∑ n ∈ Finset.Icc 1 k, ∑ m ∈ (Finset.Icc 1 n).filter (· ≤ M₀),
      ((palSet g n + palSet g m).card : ℝ)) ≤
      4 * (g : ℝ) ^ (((k : ℝ) + (M₀ : ℝ) + 2) / 2) := by
  have hg1 : (1 : ℝ) ≤ (g : ℝ) := by exact_mod_cast (by omega : 1 ≤ g)
  have h_nat :
      (∑ n ∈ Finset.Icc 1 k, ∑ m ∈ (Finset.Icc 1 n).filter (· ≤ M₀),
        (palSet g n + palSet g m).card) ≤
        4 * g ^ ((k + 1) / 2 + (M₀ + 1) / 2) := by
    calc
      (∑ n ∈ Finset.Icc 1 k, ∑ m ∈ (Finset.Icc 1 n).filter (· ≤ M₀),
          (palSet g n + palSet g m).card)
        ≤ ∑ n ∈ Finset.Icc 1 k, ∑ m ∈ (Finset.Icc 1 n).filter (· ≤ M₀),
            (palSet g n).card * (palSet g m).card := by
          refine Finset.sum_le_sum fun n _ => Finset.sum_le_sum fun m _ => h_add_mul n m
      _ ≤ ∑ n ∈ Finset.Icc 1 k, ∑ m ∈ Finset.Icc 1 M₀,
            (palSet g n).card * (palSet g m).card := by
          refine Finset.sum_le_sum fun n _ => Finset.sum_le_sum_of_subset fun m hm => ?_
          simp only [Finset.mem_filter, Finset.mem_Icc] at hm ⊢
          exact ⟨hm.1.1, hm.2⟩
      _ = (∑ n ∈ Finset.Icc 1 k, (palSet g n).card) *
            (∑ m ∈ Finset.Icc 1 M₀, (palSet g m).card) := by
          rw [Finset.sum_mul_sum]
      _ ≤ (2 * g ^ ((k + 1) / 2)) * (2 * g ^ ((M₀ + 1) / 2)) :=
          Nat.mul_le_mul (h_sum_card k) (h_sum_card M₀)
      _ = 4 * g ^ ((k + 1) / 2 + (M₀ + 1) / 2) := by
          rw [pow_add]; ring
  have h_real :
      (∑ n ∈ Finset.Icc 1 k, ∑ m ∈ (Finset.Icc 1 n).filter (· ≤ M₀),
        ((palSet g n + palSet g m).card : ℝ)) ≤
        4 * (g : ℝ) ^ (((k + 1) / 2 + (M₀ + 1) / 2 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast h_nat
  refine h_real.trans ?_
  gcongr
  have hk_div : (((k + 1) / 2 : ℕ) : ℝ) ≤ ((k : ℝ) + 1) / 2 := by
    have h2 : 2 * ((k + 1) / 2) ≤ k + 1 := by omega
    have h2R : (2 : ℝ) * (((k + 1) / 2 : ℕ) : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast h2
    linarith
  have hm_div : (((M₀ + 1) / 2 : ℕ) : ℝ) ≤ ((M₀ : ℝ) + 1) / 2 := by
    have h2 : 2 * ((M₀ + 1) / 2) ≤ M₀ + 1 := by omega
    have h2R : (2 : ℝ) * (((M₀ + 1) / 2 : ℕ) : ℝ) ≤ (M₀ : ℝ) + 1 := by exact_mod_cast h2
    linarith
  push_cast
  linarith

private lemma sum_near_diag_le (g : ℕ) (hg : 2 ≤ g) (palSet : ℕ → ℕ → Finset ℕ)
    (h_card : ∀ n : ℕ, 1 ≤ n → (palSet g n).card ≤ (g - 1) * g ^ ((n - 1) / 2))
    (h_add_exp : ∀ n m : ℕ, 1 ≤ m → m ≤ n → let d := n - m; let t := m / (2 * (d + 2)) - 1;
      ((palSet g n + palSet g m).card : ℝ) ≤
        2 * Real.exp (- (t : ℝ) / (8 * (g : ℝ) ^ (2 * d + 4))) *
          ((palSet g n).card : ℝ) * ((palSet g m).card : ℝ))
    (k : ℕ) (hk2 : 2 ≤ k)
    (hD_le : (⌊Real.log (k : ℝ) / (4 * Real.log (g : ℝ))⌋₊ : ℝ) ≤ (k : ℝ) / 2)
    (hd_bound : 2 * (Real.log (k : ℝ) / (4 * Real.log (g : ℝ)) + 2) ≤ (k : ℝ) ^ (1 / 4 : ℝ))
    (hk_34 : 8 ≤ (k : ℝ) ^ (3 / 4 : ℝ))
    (hk_14 : 3 * Real.log (k : ℝ) ≤ (1 / (32 * (g : ℝ) ^ 4)) * (k : ℝ) ^ (1 / 4 : ℝ)) :
    let D := ⌊Real.log (k : ℝ) / (4 * Real.log (g : ℝ))⌋₊
    let M₀ := k - D
    (∑ n ∈ Finset.Icc 1 k, ∑ m ∈ (Finset.Icc 1 n).filter (fun m => ¬ m ≤ M₀),
      ((palSet g n + palSet g m).card : ℝ)) ≤
      2 * (g : ℝ) ^ 2 * (g ^ k : ℝ) / (k : ℝ) := by
  intro D M₀
  have hg1 : (1 : ℝ) < (g : ℝ) := by exact_mod_cast (by omega : 1 < g)
  have hg_pos : (0 : ℝ) < (g : ℝ) := zero_lt_one.trans hg1
  have hlog_g_pos : 0 < Real.log (g : ℝ) := Real.log_pos hg1
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
  have hlog_k_nonneg : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg hk1
  have hD_le_nat : D ≤ k := by
    have : (D : ℝ) ≤ (k : ℝ) := hD_le.trans (by linarith)
    exact_mod_cast this
  have hM₀_ge : (k : ℝ) / 2 ≤ (M₀ : ℝ) := by
    dsimp [M₀]
    rw [Nat.cast_sub hD_le_nat]
    linarith
  have h_term : ∀ n ∈ Finset.Icc 1 k,
      ∀ m ∈ (Finset.Icc 1 n).filter (fun m => ¬ m ≤ M₀),
      ((palSet g n + palSet g m).card : ℝ) ≤
        2 * (g : ℝ) ^ 2 * (g ^ k : ℝ) / (k : ℝ) ^ 3 := by
    intro n hn m hm
    simp only [Finset.mem_Icc] at hn
    simp only [Finset.mem_filter, Finset.mem_Icc, not_le] at hm
    rcases hn with ⟨hn1, hnk⟩
    rcases hm with ⟨⟨hm1, hmn⟩, hM₀m⟩
    set d := n - m
    set t := m / (2 * (d + 2)) - 1
    have hexp_bound := h_add_exp n m hm1 hmn
    dsimp only at hexp_bound
    change ((palSet g n + palSet g m).card : ℝ) ≤
      2 * Real.exp (- (t : ℝ) / (8 * (g : ℝ) ^ (2 * d + 4))) *
        ((palSet g n).card : ℝ) * ((palSet g m).card : ℝ) at hexp_bound
    have hcard_prod_nat : (palSet g n).card * (palSet g m).card ≤ g ^ 2 * g ^ k := by
      have h1 : (palSet g n).card ≤ g * g ^ ((n - 1) / 2) :=
        (h_card n hn1).trans (Nat.mul_le_mul_right _ (Nat.sub_le g 1))
      have h2 : (palSet g m).card ≤ g * g ^ ((m - 1) / 2) :=
        (h_card m hm1).trans (Nat.mul_le_mul_right _ (Nat.sub_le g 1))
      have hexp_sum : (n - 1) / 2 + (m - 1) / 2 ≤ k := by omega
      calc
        (palSet g n).card * (palSet g m).card
          ≤ (g * g ^ ((n - 1) / 2)) * (g * g ^ ((m - 1) / 2)) := Nat.mul_le_mul h1 h2
        _ = g ^ 2 * g ^ ((n - 1) / 2 + (m - 1) / 2) := by rw [pow_add]; ring
        _ ≤ g ^ 2 * g ^ k :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega : 0 < g) hexp_sum)
    have hcard_prod : ((palSet g n).card : ℝ) * ((palSet g m).card : ℝ) ≤
        (g : ℝ) ^ 2 * (g ^ k : ℝ) := by
      exact_mod_cast hcard_prod_nat
    have hd_le_D : d ≤ D := by
      dsimp [d, M₀] at *
      omega
    have hD_le_log : (D : ℝ) ≤ Real.log (k : ℝ) / (4 * Real.log (g : ℝ)) := by
      dsimp [D]
      exact Nat.floor_le (div_nonneg hlog_k_nonneg (by positivity))
    have hd_le_log : (d : ℝ) ≤ Real.log (k : ℝ) / (4 * Real.log (g : ℝ)) :=
      (Nat.cast_le.mpr hd_le_D).trans hD_le_log
    have h2d4_le : 2 * ((d : ℝ) + 2) ≤ (k : ℝ) ^ (1 / 4 : ℝ) := by
      have : 2 * ((d : ℝ) + 2) ≤ 2 * (Real.log (k : ℝ) / (4 * Real.log (g : ℝ)) + 2) := by
        linarith
      exact this.trans hd_bound
    have h2d4_pos : (0 : ℝ) < 2 * ((d : ℝ) + 2) := by positivity
    have hk14_pos : (0 : ℝ) < (k : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hk_pos _
    have hm_ge : (k : ℝ) / 2 ≤ (m : ℝ) := hM₀_ge.trans (Nat.cast_le.mpr hM₀m.le)
    have hdiv_ge : (1 / 2 : ℝ) * (k : ℝ) ^ (3 / 4 : ℝ) ≤ (m : ℝ) / (2 * ((d : ℝ) + 2)) := by
      have h34 : (k : ℝ) / (k : ℝ) ^ (1 / 4 : ℝ) = (k : ℝ) ^ (3 / 4 : ℝ) := by
        calc
          (k : ℝ) / (k : ℝ) ^ (1 / 4 : ℝ)
            = (k : ℝ) ^ (1 : ℝ) / (k : ℝ) ^ (1 / 4 : ℝ) := by rw [Real.rpow_one]
          _ = (k : ℝ) ^ ((1 : ℝ) - 1 / 4) := (Real.rpow_sub hk_pos _ _).symm
          _ = (k : ℝ) ^ (3 / 4 : ℝ) := by norm_num
      calc
        (1 / 2 : ℝ) * (k : ℝ) ^ (3 / 4 : ℝ)
          = ((k : ℝ) / 2) / (k : ℝ) ^ (1 / 4 : ℝ) := by rw [← h34]; ring
        _ ≤ (m : ℝ) / (k : ℝ) ^ (1 / 4 : ℝ) :=
          div_le_div_of_nonneg_right hm_ge hk14_pos.le
        _ ≤ (m : ℝ) / (2 * ((d : ℝ) + 2)) :=
          div_le_div_of_nonneg_left (Nat.cast_nonneg m) h2d4_pos h2d4_le
    have ht_ge : (1 / 4 : ℝ) * (k : ℝ) ^ (3 / 4 : ℝ) ≤ (t : ℝ) := by
      have ht0 : (m : ℝ) / ((2 * (d + 2) : ℕ) : ℝ) - 2 ≤ (t : ℝ) :=
        nat_div_sub_one_ge m (2 * (d + 2)) (by omega)
      push_cast at ht0
      linarith
    have hg_pow_le : (g : ℝ) ^ (2 * d) ≤ (k : ℝ) ^ (1 / 2 : ℝ) := by
      have hexp_le : ((2 * d : ℕ) : ℝ) ≤ (1 / 2 : ℝ) * Real.log (k : ℝ) / Real.log (g : ℝ) := by
        have heq : (1 / 2 : ℝ) * Real.log (k : ℝ) / Real.log (g : ℝ) =
            2 * (Real.log (k : ℝ) / (4 * Real.log (g : ℝ))) := by ring
        rw [heq]
        push_cast
        linarith
      calc
        (g : ℝ) ^ (2 * d) = (g : ℝ) ^ ((2 * d : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
        _ ≤ (g : ℝ) ^ ((1 / 2 : ℝ) * Real.log (k : ℝ) / Real.log (g : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hg1.le hexp_le
        _ = (k : ℝ) ^ (1 / 2 : ℝ) := rpow_div_log_eq_rpow hg1 hk_pos
    have hden_le : 8 * (g : ℝ) ^ (2 * d + 4) ≤ 8 * (g : ℝ) ^ 4 * (k : ℝ) ^ (1 / 2 : ℝ) := by
      rw [pow_add]
      have : (g : ℝ) ^ (2 * d) * (g : ℝ) ^ 4 ≤ (k : ℝ) ^ (1 / 2 : ℝ) * (g : ℝ) ^ 4 :=
        mul_le_mul_of_nonneg_right hg_pow_le (by positivity)
      linarith
    have hden_pos : 0 < 8 * (g : ℝ) ^ (2 * d + 4) := by positivity
    have h_ratio_ge : 3 * Real.log (k : ℝ) ≤ (t : ℝ) / (8 * (g : ℝ) ^ (2 * d + 4)) := by
      have h12 : (k : ℝ) ^ (3 / 4 : ℝ) / (k : ℝ) ^ (1 / 2 : ℝ) = (k : ℝ) ^ (1 / 4 : ℝ) := by
        rw [← Real.rpow_sub hk_pos]
        norm_num
      have h_rhs :
          (1 / (32 * (g : ℝ) ^ 4)) * (k : ℝ) ^ (1 / 4 : ℝ) =
            ((1 / 4 : ℝ) * (k : ℝ) ^ (3 / 4 : ℝ)) / (8 * (g : ℝ) ^ 4 * (k : ℝ) ^ (1 / 2 : ℝ)) := by
        rw [← h12]
        field_simp
        ring
      refine hk_14.trans ?_
      rw [h_rhs]
      exact div_le_div₀ (by positivity) ht_ge hden_pos hden_le
    have hexp_le : Real.exp (- (t : ℝ) / (8 * (g : ℝ) ^ (2 * d + 4))) ≤ 1 / (k : ℝ) ^ 3 := by
      have h_neg : - (t : ℝ) / (8 * (g : ℝ) ^ (2 * d + 4)) ≤ - (3 * Real.log (k : ℝ)) := by
        rw [neg_div]
        linarith
      calc
        Real.exp (- (t : ℝ) / (8 * (g : ℝ) ^ (2 * d + 4)))
          ≤ Real.exp (- (3 * Real.log (k : ℝ))) := Real.exp_le_exp.mpr h_neg
        _ = (Real.exp (Real.log (k : ℝ)) ^ 3)⁻¹ := by
          rw [Real.exp_neg,
            show (3 : ℝ) * Real.log (k : ℝ) = ((3 : ℕ) : ℝ) * Real.log (k : ℝ) by norm_num,
            Real.exp_nat_mul]
        _ = 1 / (k : ℝ) ^ 3 := by
          rw [Real.exp_log hk_pos, one_div]
    calc
      ((palSet g n + palSet g m).card : ℝ)
        ≤ 2 * Real.exp (- (t : ℝ) / (8 * (g : ℝ) ^ (2 * d + 4))) *
            (((palSet g n).card : ℝ) * ((palSet g m).card : ℝ)) := by
          linarith
      _ ≤ 2 * (1 / (k : ℝ) ^ 3) * ((g : ℝ) ^ 2 * (g ^ k : ℝ)) := by
          gcongr
      _ = 2 * (g : ℝ) ^ 2 * (g ^ k : ℝ) / (k : ℝ) ^ 3 := by ring
  have h_inner : ∀ n ∈ Finset.Icc 1 k,
      (∑ m ∈ (Finset.Icc 1 n).filter (fun m => ¬ m ≤ M₀),
        ((palSet g n + palSet g m).card : ℝ)) ≤
        (k : ℝ) * (2 * (g : ℝ) ^ 2 * (g ^ k : ℝ) / (k : ℝ) ^ 3) := by
    intro n hn
    have hnk : n ≤ k := (Finset.mem_Icc.mp hn).2
    have hcard_le : ((Finset.Icc 1 n).filter (fun m => ¬ m ≤ M₀)).card ≤ k := by
      calc
        ((Finset.Icc 1 n).filter (fun m => ¬ m ≤ M₀)).card ≤ (Finset.Icc 1 n).card :=
          Finset.card_filter_le _ _
        _ = n := by simp [Nat.card_Icc]
        _ ≤ k := hnk
    calc
      (∑ m ∈ (Finset.Icc 1 n).filter (fun m => ¬ m ≤ M₀),
          ((palSet g n + palSet g m).card : ℝ))
        ≤ ∑ _m ∈ (Finset.Icc 1 n).filter (fun m => ¬ m ≤ M₀),
            (2 * (g : ℝ) ^ 2 * (g ^ k : ℝ) / (k : ℝ) ^ 3) :=
          Finset.sum_le_sum fun m hm => h_term n hn m hm
      _ = (((Finset.Icc 1 n).filter (fun m => ¬ m ≤ M₀)).card : ℝ) *
            (2 * (g : ℝ) ^ 2 * (g ^ k : ℝ) / (k : ℝ) ^ 3) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (k : ℝ) * (2 * (g : ℝ) ^ 2 * (g ^ k : ℝ) / (k : ℝ) ^ 3) := by
          gcongr
  calc
    (∑ n ∈ Finset.Icc 1 k, ∑ m ∈ (Finset.Icc 1 n).filter (fun m => ¬ m ≤ M₀),
        ((palSet g n + palSet g m).card : ℝ))
      ≤ ∑ _n ∈ Finset.Icc 1 k,
          ((k : ℝ) * (2 * (g : ℝ) ^ 2 * (g ^ k : ℝ) / (k : ℝ) ^ 3)) :=
        Finset.sum_le_sum fun n hn => h_inner n hn
    _ = ((Finset.Icc 1 k).card : ℝ) *
          ((k : ℝ) * (2 * (g : ℝ) ^ 2 * (g ^ k : ℝ) / (k : ℝ) ^ 3)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (k : ℝ) * ((k : ℝ) * (2 * (g : ℝ) ^ 2 * (g ^ k : ℝ) / (k : ℝ) ^ 3)) := by
        simp [Nat.card_Icc]
    _ = 2 * (g : ℝ) ^ 2 * (g ^ k : ℝ) / (k : ℝ) := by
        have hk_ne : (k : ℝ) ≠ 0 := hk_pos.ne'
        field_simp

section Asymptotics

variable (g : ℕ) (hg : 2 ≤ g) (palSet : ℕ → ℕ → Finset ℕ)
  (h_sub : sumsOfTwo g ⊆ {0} ∪ {p | 0 < p ∧ IsPalindrome g p} ∪ sumsOfTwoPositive g)
  (h_pos_cov : ∀ k : ℕ, {p : ℕ | 0 < p ∧ IsPalindrome g p} ∩ Set.Iio (g ^ k) ⊆
    ↑((Finset.Icc 1 k).biUnion (palSet g)))
  (h_sum_cov : ∀ k : ℕ, sumsOfTwoPositive g ∩ Set.Iio (g ^ k) ⊆
    ↑((Finset.Icc 1 k).biUnion fun n => (Finset.Icc 1 n).biUnion fun m =>
      (palSet g n + palSet g m)))
  (h_card : ∀ n : ℕ, 1 ≤ n → (palSet g n).card ≤ (g - 1) * g ^ ((n - 1) / 2))
  (h_sum_card : ∀ N : ℕ, (∑ n ∈ Finset.Icc 1 N, (palSet g n).card) ≤ 2 * g ^ ((N + 1) / 2))
  (h_add_mul : ∀ n m : ℕ, (palSet g n + palSet g m).card ≤ (palSet g n).card * (palSet g m).card)
  (h_add_exp : ∀ n m : ℕ, 1 ≤ m → m ≤ n → let d := n - m; let t := m / (2 * (d + 2)) - 1;
    ((palSet g n + palSet g m).card : ℝ) ≤
      2 * Real.exp (- (t : ℝ) / (8 * (g : ℝ) ^ (2 * d + 4))) *
        ((palSet g n).card : ℝ) * ((palSet g m).card : ℝ))

section Positive

include hg palSet h_sum_cov h_card h_sum_card h_add_mul h_add_exp

theorem card_sumsOfTwoPositive_lt_pow :
    ∀ᶠ k : ℕ in atTop,
      ((sumsOfTwoPositive g ∩ Set.Iio (g ^ k)).ncard : ℝ) ≤ (g ^ k : ℝ) / (k : ℝ) ^ (1 / 9 : ℝ) := by
  have hg1 : (1 : ℝ) < (g : ℝ) := by exact_mod_cast (by omega : 1 < g)
  have hg_pos : (0 : ℝ) < (g : ℝ) := zero_lt_one.trans hg1
  have hlog_g_pos : 0 < Real.log (g : ℝ) := Real.log_pos hg1
  have ev_D : ∀ᶠ k : ℕ in atTop,
      (1 / (2 * Real.log (g : ℝ))) * Real.log (k : ℝ) ≤ (k : ℝ) ^ (1 : ℝ) :=
    eventually_mul_log_le_natCast_rpow zero_lt_one (by positivity)
  have ev_d : ∀ᶠ k : ℕ in atTop,
      (1 / Real.log (g : ℝ)) * Real.log (k : ℝ) ≤ (k : ℝ) ^ (1 / 4 : ℝ) :=
    eventually_mul_log_le_natCast_rpow (by norm_num) (by positivity)
  have ev_k14_const : ∀ᶠ k : ℕ in atTop, (8 : ℝ) ≤ (k : ℝ) ^ (1 / 4 : ℝ) :=
    eventually_const_le_natCast_rpow (by norm_num) 8
  have ev_k34_const : ∀ᶠ k : ℕ in atTop, (8 : ℝ) ≤ (k : ℝ) ^ (3 / 4 : ℝ) :=
    eventually_const_le_natCast_rpow (by norm_num) 8
  have ev_exp : ∀ᶠ k : ℕ in atTop,
      (96 * (g : ℝ) ^ 4) * Real.log (k : ℝ) ≤ (k : ℝ) ^ (1 / 4 : ℝ) :=
    eventually_mul_log_le_natCast_rpow (by norm_num) (by positivity)
  have ev_case1 : ∀ᶠ k : ℕ in atTop,
      8 * (g : ℝ) ^ (3 / 2 : ℝ) ≤ (k : ℝ) ^ (1 / 72 : ℝ) :=
    eventually_const_le_natCast_rpow (by norm_num) (8 * (g : ℝ) ^ (3 / 2 : ℝ))
  have ev_case2 : ∀ᶠ k : ℕ in atTop,
      4 * (g : ℝ) ^ 2 ≤ (k : ℝ) ^ (8 / 9 : ℝ) :=
    eventually_const_le_natCast_rpow (by norm_num) (4 * (g : ℝ) ^ 2)
  filter_upwards [eventually_ge_atTop 2, ev_D, ev_d, ev_k14_const, ev_k34_const, ev_exp,
    ev_case1, ev_case2] with k hk2 hD h_d hk14c hk34c hexp hc1 hc2
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
  have hlog_k_nonneg : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg hk1
  set D := ⌊Real.log (k : ℝ) / (4 * Real.log (g : ℝ))⌋₊
  set M₀ := k - D
  have hD_le : (D : ℝ) ≤ (k : ℝ) / 2 := by
    have hD_floor : (D : ℝ) ≤ Real.log (k : ℝ) / (4 * Real.log (g : ℝ)) :=
      Nat.floor_le (div_nonneg hlog_k_nonneg (by positivity))
    rw [Real.rpow_one] at hD
    have h_half : Real.log (k : ℝ) / (4 * Real.log (g : ℝ)) ≤ (k : ℝ) / 2 := by
      have : Real.log (k : ℝ) / (4 * Real.log (g : ℝ)) =
          ((1 / (2 * Real.log (g : ℝ))) * Real.log (k : ℝ)) / 2 := by
        field_simp
        ring
      rw [this]
      linarith
    exact hD_floor.trans h_half
  have hD_le_nat : D ≤ k := by
    have : (D : ℝ) ≤ (k : ℝ) := hD_le.trans (by linarith)
    exact_mod_cast this
  have hd_bound : 2 * (Real.log (k : ℝ) / (4 * Real.log (g : ℝ)) + 2) ≤ (k : ℝ) ^ (1 / 4 : ℝ) := by
    have hpart1 : 2 * (Real.log (k : ℝ) / (4 * Real.log (g : ℝ))) ≤
        (1 / 2 : ℝ) * (k : ℝ) ^ (1 / 4 : ℝ) := by
      have h_eq : 2 * (Real.log (k : ℝ) / (4 * Real.log (g : ℝ))) =
          (1 / 2 : ℝ) * ((1 / Real.log (g : ℝ)) * Real.log (k : ℝ)) := by
        field_simp
        ring
      rw [h_eq]
      linarith
    linarith
  have hk_14 : 3 * Real.log (k : ℝ) ≤ (1 / (32 * (g : ℝ) ^ 4)) * (k : ℝ) ^ (1 / 4 : ℝ) := by
    have hpos : 0 < 32 * (g : ℝ) ^ 4 := by positivity
    have : 3 * Real.log (k : ℝ) = (1 / (32 * (g : ℝ) ^ 4)) * ((96 * (g : ℝ) ^ 4) * Real.log (k : ℝ)) := by
      field_simp
      ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hexp (by positivity)
  have hcov_card :
      ((sumsOfTwoPositive g ∩ Set.Iio (g ^ k)).ncard : ℝ) ≤
        (∑ n ∈ Finset.Icc 1 k, ∑ m ∈ (Finset.Icc 1 n).filter (· ≤ M₀),
          ((palSet g n + palSet g m).card : ℝ)) +
        (∑ n ∈ Finset.Icc 1 k, ∑ m ∈ (Finset.Icc 1 n).filter (fun m => ¬ m ≤ M₀),
          ((palSet g n + palSet g m).card : ℝ)) := by
    have h_nat_cov :
        (sumsOfTwoPositive g ∩ Set.Iio (g ^ k)).ncard ≤
          ∑ n ∈ Finset.Icc 1 k, ∑ m ∈ Finset.Icc 1 n, (palSet g n + palSet g m).card := by
      calc
        (sumsOfTwoPositive g ∩ Set.Iio (g ^ k)).ncard
          ≤ (((Finset.Icc 1 k).biUnion fun n =>
              (Finset.Icc 1 n).biUnion fun m => palSet g n + palSet g m : Finset ℕ) : Set ℕ).ncard :=
            Set.ncard_le_ncard (h_sum_cov k) (Finset.finite_toSet _)
        _ = ((Finset.Icc 1 k).biUnion fun n =>
              (Finset.Icc 1 n).biUnion fun m => palSet g n + palSet g m).card :=
            Set.ncard_coe_finset _
        _ ≤ ∑ n ∈ Finset.Icc 1 k,
              ((Finset.Icc 1 n).biUnion fun m => palSet g n + palSet g m).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ n ∈ Finset.Icc 1 k, ∑ m ∈ Finset.Icc 1 n, (palSet g n + palSet g m).card :=
            Finset.sum_le_sum fun n _ => Finset.card_biUnion_le
    have h_split :
        (∑ n ∈ Finset.Icc 1 k, ∑ m ∈ Finset.Icc 1 n, (palSet g n + palSet g m).card) =
          (∑ n ∈ Finset.Icc 1 k, ∑ m ∈ (Finset.Icc 1 n).filter (· ≤ M₀),
            (palSet g n + palSet g m).card) +
          (∑ n ∈ Finset.Icc 1 k, ∑ m ∈ (Finset.Icc 1 n).filter (fun m => ¬ m ≤ M₀),
            (palSet g n + palSet g m).card) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      exact (Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 n) (· ≤ M₀)
        (fun m => (palSet g n + palSet g m).card)).symm
    have h_real :
        ((sumsOfTwoPositive g ∩ Set.Iio (g ^ k)).ncard : ℝ) ≤
          ((∑ n ∈ Finset.Icc 1 k, ∑ m ∈ (Finset.Icc 1 n).filter (· ≤ M₀),
            (palSet g n + palSet g m).card) +
          (∑ n ∈ Finset.Icc 1 k, ∑ m ∈ (Finset.Icc 1 n).filter (fun m => ¬ m ≤ M₀),
            (palSet g n + palSet g m).card) : ℕ) := by
      exact_mod_cast h_nat_cov.trans_eq h_split
    push_cast at h_real
    exact h_real
  have hcase1 :
      (∑ n ∈ Finset.Icc 1 k, ∑ m ∈ (Finset.Icc 1 n).filter (· ≤ M₀),
        ((palSet g n + palSet g m).card : ℝ)) ≤
        (1 / 2 : ℝ) * ((g ^ k : ℝ) / (k : ℝ) ^ (1 / 9 : ℝ)) := by
    have h_off := sum_off_diag_le g hg palSet h_sum_card h_add_mul k M₀
    have hD_lt : Real.log (k : ℝ) / (4 * Real.log (g : ℝ)) < (D : ℝ) + 1 := by
      dsimp [D]
      exact Nat.lt_floor_add_one _
    have hexp_le :
        ((k : ℝ) + (M₀ : ℝ) + 2) / 2 ≤
          (k : ℝ) + 3 / 2 + (- (1 / 8 : ℝ) * Real.log (k : ℝ) / Real.log (g : ℝ)) := by
      have hM₀_cast : (M₀ : ℝ) = (k : ℝ) - (D : ℝ) := by
        dsimp [M₀]
        exact Nat.cast_sub hD_le_nat
      have heq : (- (1 / 8 : ℝ) * Real.log (k : ℝ) / Real.log (g : ℝ)) =
          - (Real.log (k : ℝ) / (4 * Real.log (g : ℝ))) / 2 := by ring
      rw [hM₀_cast, heq]
      linarith
    have hrpow_bound :
        4 * (g : ℝ) ^ (((k : ℝ) + (M₀ : ℝ) + 2) / 2) ≤
          4 * (g : ℝ) ^ (3 / 2 : ℝ) * (g ^ k : ℝ) / (k : ℝ) ^ (1 / 8 : ℝ) := by
      calc
        4 * (g : ℝ) ^ (((k : ℝ) + (M₀ : ℝ) + 2) / 2)
          ≤ 4 * (g : ℝ) ^ ((k : ℝ) + 3 / 2 + (- (1 / 8 : ℝ) * Real.log (k : ℝ) / Real.log (g : ℝ))) := by
            gcongr
            exact hg1.le
        _ = 4 * ((g : ℝ) ^ (k : ℝ) * (g : ℝ) ^ (3 / 2 : ℝ) *
              (g : ℝ) ^ (- (1 / 8 : ℝ) * Real.log (k : ℝ) / Real.log (g : ℝ))) := by
            rw [Real.rpow_add hg_pos, Real.rpow_add hg_pos]
        _ = 4 * ((g ^ k : ℝ) * (g : ℝ) ^ (3 / 2 : ℝ) * (k : ℝ) ^ (- (1 / 8 : ℝ))) := by
            rw [Real.rpow_natCast, rpow_div_log_eq_rpow hg1 hk_pos]
        _ = 4 * (g : ℝ) ^ (3 / 2 : ℝ) * (g ^ k : ℝ) / (k : ℝ) ^ (1 / 8 : ℝ) := by
            rw [Real.rpow_neg hk_pos.le]
            ring
    have hk_split : (k : ℝ) ^ (1 / 8 : ℝ) = (k : ℝ) ^ (1 / 9 : ℝ) * (k : ℝ) ^ (1 / 72 : ℝ) := by
      rw [← Real.rpow_add hk_pos]
      norm_num
    have hc1' : 4 * (g : ℝ) ^ (3 / 2 : ℝ) ≤ (1 / 2 : ℝ) * (k : ℝ) ^ (1 / 72 : ℝ) := by linarith
    have hk19_pos : 0 < (k : ℝ) ^ (1 / 9 : ℝ) := Real.rpow_pos_of_pos hk_pos _
    have hk172_pos : 0 < (k : ℝ) ^ (1 / 72 : ℝ) := Real.rpow_pos_of_pos hk_pos _
    refine (h_off.trans hrpow_bound).trans ?_
    rw [hk_split]
    calc
      4 * (g : ℝ) ^ (3 / 2 : ℝ) * (g ^ k : ℝ) / ((k : ℝ) ^ (1 / 9 : ℝ) * (k : ℝ) ^ (1 / 72 : ℝ))
        ≤ ((1 / 2 : ℝ) * (k : ℝ) ^ (1 / 72 : ℝ)) * (g ^ k : ℝ) /
            ((k : ℝ) ^ (1 / 9 : ℝ) * (k : ℝ) ^ (1 / 72 : ℝ)) := by
          gcongr
      _ = (1 / 2 : ℝ) * ((g ^ k : ℝ) / (k : ℝ) ^ (1 / 9 : ℝ)) := by
          have hk172_ne : (k : ℝ) ^ (1 / 72 : ℝ) ≠ 0 := hk172_pos.ne'
          field_simp
  have hcase2 :
      (∑ n ∈ Finset.Icc 1 k, ∑ m ∈ (Finset.Icc 1 n).filter (fun m => ¬ m ≤ M₀),
        ((palSet g n + palSet g m).card : ℝ)) ≤
        (1 / 2 : ℝ) * ((g ^ k : ℝ) / (k : ℝ) ^ (1 / 9 : ℝ)) := by
    have h_near := sum_near_diag_le g hg palSet h_card h_add_exp k hk2 hD_le hd_bound hk34c hk_14
    have hk_split : (k : ℝ) = (k : ℝ) ^ (1 / 9 : ℝ) * (k : ℝ) ^ (8 / 9 : ℝ) := by
      nth_rewrite 1 [← Real.rpow_one (k : ℝ)]
      rw [← Real.rpow_add hk_pos]
      norm_num
    have hc2' : 2 * (g : ℝ) ^ 2 ≤ (1 / 2 : ℝ) * (k : ℝ) ^ (8 / 9 : ℝ) := by linarith
    have hk19_pos : 0 < (k : ℝ) ^ (1 / 9 : ℝ) := Real.rpow_pos_of_pos hk_pos _
    have hk89_pos : 0 < (k : ℝ) ^ (8 / 9 : ℝ) := Real.rpow_pos_of_pos hk_pos _
    refine h_near.trans ?_
    calc
      2 * (g : ℝ) ^ 2 * (g ^ k : ℝ) / (k : ℝ)
        ≤ ((1 / 2 : ℝ) * (k : ℝ) ^ (8 / 9 : ℝ)) * (g ^ k : ℝ) /
            ((k : ℝ) ^ (1 / 9 : ℝ) * (k : ℝ) ^ (8 / 9 : ℝ)) := by
          rw [← hk_split]
          gcongr
      _ = (1 / 2 : ℝ) * ((g ^ k : ℝ) / (k : ℝ) ^ (1 / 9 : ℝ)) := by
          have hk89_ne : (k : ℝ) ^ (8 / 9 : ℝ) ≠ 0 := hk89_pos.ne'
          field_simp
  linarith

private lemma zakharov_explicit_positive_half :
    ∀ᶠ X : ℕ in atTop,
      ((sumsOfTwoPositive g ∩ Set.Iio X).ncard : ℝ) ≤
        (1 / 2 : ℝ) * ((X : ℝ) / Real.log (X : ℝ) ^ (1 / 10 : ℝ)) := by
  have hg1 : (1 : ℝ) < (g : ℝ) := by exact_mod_cast (by omega : 1 < g)
  have hlog_g_pos : 0 < Real.log (g : ℝ) := Real.log_pos hg1
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp (card_sumsOfTwoPositive_lt_pow g hg palSet h_sum_cov
    h_card h_sum_card h_add_mul h_add_exp)
  have ev_log_pow : ∀ᶠ X : ℕ in atTop,
      2 * (g : ℝ) * Real.log (g : ℝ) ^ (1 / 9 : ℝ) ≤ Real.log (X : ℝ) ^ (1 / 90 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 90)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
      (eventually_ge_atTop (2 * (g : ℝ) * Real.log (g : ℝ) ^ (1 / 9 : ℝ)))
  filter_upwards [eventually_ge_atTop (max (g ^ max K₀ 2) 3), ev_log_pow] with X hX h_log_pow
  have hX_pos_nat : 0 < X := by omega
  have hX3 : (3 : ℝ) ≤ (X : ℝ) := by exact_mod_cast (le_trans (le_max_right _ _) hX)
  have hlogX_pos : 0 < Real.log (X : ℝ) := Real.log_pos (by linarith)
  set k := Nat.log g X + 1
  have hX_lt_pow : X < g ^ k := Nat.lt_pow_succ_log_self (by omega : 1 < g) X
  have hpow_le_X : g ^ (Nat.log g X) ≤ X := Nat.pow_log_le_self g hX_pos_nat.ne'
  have hk_ge : max K₀ 2 ≤ k := by
    have hpow_lt : g ^ max K₀ 2 < g ^ k :=
      (le_trans (le_max_left _ _) hX).trans_lt hX_lt_pow
    exact ((Nat.pow_lt_pow_iff_right (by omega : 1 < g)).mp hpow_lt).le
  have hpow_bound := hK₀ k ((le_max_left K₀ 2).trans hk_ge)
  have hncard_le : ((sumsOfTwoPositive g ∩ Set.Iio X).ncard : ℝ) ≤
      (g ^ k : ℝ) / (k : ℝ) ^ (1 / 9 : ℝ) := by
    have hsub_X : sumsOfTwoPositive g ∩ Set.Iio X ⊆ sumsOfTwoPositive g ∩ Set.Iio (g ^ k) :=
      Set.inter_subset_inter_right _ (Set.Iio_subset_Iio hX_lt_pow.le)
    have hle : (sumsOfTwoPositive g ∩ Set.Iio X).ncard ≤
        (sumsOfTwoPositive g ∩ Set.Iio (g ^ k)).ncard :=
      Set.ncard_le_ncard hsub_X ((Set.finite_Iio _).inter_of_right _)
    exact (Nat.cast_le.mpr hle).trans hpow_bound
  have hgk_le : (g ^ k : ℝ) ≤ (g : ℝ) * (X : ℝ) := by
    have h_nat : g ^ k ≤ g * X := by
      dsimp [k]
      rw [pow_succ']
      exact Nat.mul_le_mul_left g hpow_le_X
    exact_mod_cast h_nat
  have hk_ge_log : Real.log (X : ℝ) / Real.log (g : ℝ) ≤ (k : ℝ) := by
    have hX_lt_R : (X : ℝ) < (g : ℝ) ^ k := by exact_mod_cast hX_lt_pow
    have hlog_lt : Real.log (X : ℝ) < (k : ℝ) * Real.log (g : ℝ) := by
      calc
        Real.log (X : ℝ) < Real.log ((g : ℝ) ^ k) :=
          Real.log_lt_log (by linarith) hX_lt_R
        _ = (k : ℝ) * Real.log (g : ℝ) := Real.log_pow (g : ℝ) k
    exact (div_le_iff₀ hlog_g_pos).mpr hlog_lt.le
  have hk19_ge :
      Real.log (X : ℝ) ^ (1 / 9 : ℝ) / Real.log (g : ℝ) ^ (1 / 9 : ℝ) ≤ (k : ℝ) ^ (1 / 9 : ℝ) := by
    rw [← Real.div_rpow hlogX_pos.le hlog_g_pos.le]
    exact Real.rpow_le_rpow (div_nonneg hlogX_pos.le hlog_g_pos.le) hk_ge_log (by norm_num)
  have hk19_pos : 0 < Real.log (X : ℝ) ^ (1 / 9 : ℝ) / Real.log (g : ℝ) ^ (1 / 9 : ℝ) := by
    positivity
  have hstep1 :
      (g ^ k : ℝ) / (k : ℝ) ^ (1 / 9 : ℝ) ≤
        (g : ℝ) * Real.log (g : ℝ) ^ (1 / 9 : ℝ) * (X : ℝ) / Real.log (X : ℝ) ^ (1 / 9 : ℝ) := by
    calc
      (g ^ k : ℝ) / (k : ℝ) ^ (1 / 9 : ℝ)
        ≤ ((g : ℝ) * (X : ℝ)) /
            (Real.log (X : ℝ) ^ (1 / 9 : ℝ) / Real.log (g : ℝ) ^ (1 / 9 : ℝ)) :=
          div_le_div₀ (by positivity) hgk_le hk19_pos hk19_ge
      _ = (g : ℝ) * Real.log (g : ℝ) ^ (1 / 9 : ℝ) * (X : ℝ) / Real.log (X : ℝ) ^ (1 / 9 : ℝ) := by
          rw [div_div_eq_mul_div]
          ring
  have hlog_split :
      Real.log (X : ℝ) ^ (1 / 9 : ℝ) =
        Real.log (X : ℝ) ^ (1 / 10 : ℝ) * Real.log (X : ℝ) ^ (1 / 90 : ℝ) := by
    rw [← Real.rpow_add hlogX_pos]
    norm_num
  have hstep2 :
      (g : ℝ) * Real.log (g : ℝ) ^ (1 / 9 : ℝ) * (X : ℝ) / Real.log (X : ℝ) ^ (1 / 9 : ℝ) ≤
        (1 / 2 : ℝ) * ((X : ℝ) / Real.log (X : ℝ) ^ (1 / 10 : ℝ)) := by
    have hlog90_pos : 0 < Real.log (X : ℝ) ^ (1 / 90 : ℝ) := Real.rpow_pos_of_pos hlogX_pos _
    have hlog10_pos : 0 < Real.log (X : ℝ) ^ (1 / 10 : ℝ) := Real.rpow_pos_of_pos hlogX_pos _
    have h_coeff : (g : ℝ) * Real.log (g : ℝ) ^ (1 / 9 : ℝ) ≤
        (1 / 2 : ℝ) * Real.log (X : ℝ) ^ (1 / 90 : ℝ) := by linarith
    rw [hlog_split]
    calc
      (g : ℝ) * Real.log (g : ℝ) ^ (1 / 9 : ℝ) * (X : ℝ) /
          (Real.log (X : ℝ) ^ (1 / 10 : ℝ) * Real.log (X : ℝ) ^ (1 / 90 : ℝ))
        ≤ ((1 / 2 : ℝ) * Real.log (X : ℝ) ^ (1 / 90 : ℝ)) * (X : ℝ) /
            (Real.log (X : ℝ) ^ (1 / 10 : ℝ) * Real.log (X : ℝ) ^ (1 / 90 : ℝ)) := by
          gcongr
      _ = (1 / 2 : ℝ) * ((X : ℝ) / Real.log (X : ℝ) ^ (1 / 10 : ℝ)) := by
          have hne : Real.log (X : ℝ) ^ (1 / 90 : ℝ) ≠ 0 := hlog90_pos.ne'
          field_simp
  exact hncard_le.trans (hstep1.trans hstep2)

theorem zakharov_explicit_positive :
    ∀ᶠ X : ℕ in atTop,
      ((sumsOfTwoPositive g ∩ Set.Iio X).ncard : ℝ) ≤
        (X : ℝ) / Real.log (X : ℝ) ^ (1 / 10 : ℝ) := by
  filter_upwards [zakharov_explicit_positive_half g hg palSet h_sum_cov h_card h_sum_card
    h_add_mul h_add_exp, eventually_ge_atTop 3] with X hX hX3
  have hX_pos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hlogX_pos : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  have h_nonneg : 0 ≤ (X : ℝ) / Real.log (X : ℝ) ^ (1 / 10 : ℝ) := by positivity
  linarith

theorem green_95_zakharov :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in atTop,
      ((sumsOfTwoPositive g ∩ Set.Iio X).ncard : ℝ) ≤ (X : ℝ) / Real.log X ^ c :=
  ⟨1 / 10, by norm_num,
    zakharov_explicit_positive g hg palSet h_sum_cov h_card h_sum_card h_add_mul h_add_exp⟩

end Positive

section SumsOfTwo

include hg palSet h_sub h_pos_cov h_sum_cov h_card h_sum_card h_add_mul h_add_exp

theorem zakharov_explicit_sumsOfTwo :
    ∀ᶠ X : ℕ in atTop,
      ((sumsOfTwo g ∩ Set.Iio X).ncard : ℝ) ≤
        (X : ℝ) / Real.log (X : ℝ) ^ (1 / 10 : ℝ) := by
  have ev_half := zakharov_explicit_positive_half g hg palSet h_sum_cov h_card h_sum_card
    h_add_mul h_add_exp
  have ev_pow : ∀ᶠ X : ℕ in atTop, 2 * (1 + 2 * (g : ℝ)) ≤ (X : ℝ) ^ (2 / 5 : ℝ) :=
    eventually_const_le_natCast_rpow (by norm_num) (2 * (1 + 2 * (g : ℝ)))
  filter_upwards [ev_half, ev_pow, eventually_ge_atTop 3] with X hX_pos_half hX_pow hX3
  have hX_pos_nat : 0 < X := by omega
  have hX_pos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX_pos_nat
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast (by omega : 1 ≤ X)
  have hlogX_pos : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  set k := Nat.log g X + 1
  have hX_lt_pow : X < g ^ k := Nat.lt_pow_succ_log_self (by omega : 1 < g) X
  have hpow_le_X : g ^ (Nat.log g X) ≤ X := Nat.pow_log_le_self g hX_pos_nat.ne'
  have h_decomp :
      (sumsOfTwo g ∩ Set.Iio X).ncard ≤
        1 + 2 * g ^ ((k + 1) / 2) + (sumsOfTwoPositive g ∩ Set.Iio X).ncard := by
    have hsub_inter : sumsOfTwo g ∩ Set.Iio X ⊆
        ({0} ∩ Set.Iio X) ∪ ({p | 0 < p ∧ IsPalindrome g p} ∩ Set.Iio X) ∪
          (sumsOfTwoPositive g ∩ Set.Iio X) := by
      intro n hn
      rcases hn with ⟨hnS, hnX⟩
      rcases h_sub hnS with (h0 | hp) | hp2
      · exact Or.inl (Or.inl ⟨h0, hnX⟩)
      · exact Or.inl (Or.inr ⟨hp, hnX⟩)
      · exact Or.inr ⟨hp2, hnX⟩
    have h0_le : ({0} ∩ Set.Iio X).ncard ≤ 1 := Set.ncard_singleton_inter 0 (Set.Iio X)
    have hpal_le : ({p | 0 < p ∧ IsPalindrome g p} ∩ Set.Iio X).ncard ≤ 2 * g ^ ((k + 1) / 2) := by
      have h1 : {p | 0 < p ∧ IsPalindrome g p} ∩ Set.Iio X ⊆
          {p | 0 < p ∧ IsPalindrome g p} ∩ Set.Iio (g ^ k) :=
        Set.inter_subset_inter_right _ (Set.Iio_subset_Iio hX_lt_pow.le)
      calc
        ({p | 0 < p ∧ IsPalindrome g p} ∩ Set.Iio X).ncard
          ≤ ({p | 0 < p ∧ IsPalindrome g p} ∩ Set.Iio (g ^ k)).ncard :=
            Set.ncard_le_ncard h1 ((Set.finite_Iio _).inter_of_right _)
        _ ≤ (((Finset.Icc 1 k).biUnion (palSet g) : Finset ℕ) : Set ℕ).ncard :=
            Set.ncard_le_ncard (h_pos_cov k) (Finset.finite_toSet _)
        _ = ((Finset.Icc 1 k).biUnion (palSet g)).card := Set.ncard_coe_finset _
        _ ≤ ∑ n ∈ Finset.Icc 1 k, (palSet g n).card := Finset.card_biUnion_le
        _ ≤ 2 * g ^ ((k + 1) / 2) := h_sum_card k
    have hfin : (({0} ∩ Set.Iio X) ∪ ({p | 0 < p ∧ IsPalindrome g p} ∩ Set.Iio X) ∪
        (sumsOfTwoPositive g ∩ Set.Iio X)).Finite :=
      (((Set.finite_Iio X).inter_of_right _).union ((Set.finite_Iio X).inter_of_right _)).union
        ((Set.finite_Iio X).inter_of_right _)
    calc
      (sumsOfTwo g ∩ Set.Iio X).ncard
        ≤ (({0} ∩ Set.Iio X) ∪ ({p | 0 < p ∧ IsPalindrome g p} ∩ Set.Iio X) ∪
            (sumsOfTwoPositive g ∩ Set.Iio X)).ncard :=
          Set.ncard_le_ncard hsub_inter hfin
      _ ≤ (({0} ∩ Set.Iio X) ∪ ({p | 0 < p ∧ IsPalindrome g p} ∩ Set.Iio X)).ncard +
            (sumsOfTwoPositive g ∩ Set.Iio X).ncard :=
          Set.ncard_union_le _ _
      _ ≤ ({0} ∩ Set.Iio X).ncard + ({p | 0 < p ∧ IsPalindrome g p} ∩ Set.Iio X).ncard +
            (sumsOfTwoPositive g ∩ Set.Iio X).ncard := by
          gcongr
          exact Set.ncard_union_le _ _
      _ ≤ 1 + 2 * g ^ ((k + 1) / 2) + (sumsOfTwoPositive g ∩ Set.Iio X).ncard := by
          gcongr
  have hgk_half_le : (g ^ ((k + 1) / 2) : ℝ) ≤ (g : ℝ) * (X : ℝ) ^ (1 / 2 : ℝ) := by
    have h_exp : 2 * ((k + 1) / 2) ≤ Nat.log g X + 2 := by
      dsimp [k]
      omega
    have h_sq_nat : (g ^ ((k + 1) / 2)) ^ 2 ≤ X * g ^ 2 := by
      calc
        (g ^ ((k + 1) / 2)) ^ 2 = g ^ (2 * ((k + 1) / 2)) := by
          rw [← pow_mul, mul_comm]
        _ ≤ g ^ (Nat.log g X + 2) := Nat.pow_le_pow_right (by omega : 0 < g) h_exp
        _ = g ^ (Nat.log g X) * g ^ 2 := by rw [pow_add]
        _ ≤ X * g ^ 2 := Nat.mul_le_mul_right _ hpow_le_X
    have h_sq_real : (g ^ ((k + 1) / 2) : ℝ) ^ 2 ≤ ((g : ℝ) * (X : ℝ) ^ (1 / 2 : ℝ)) ^ 2 := by
      have h_rhs : ((g : ℝ) * (X : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = (X : ℝ) * (g : ℝ) ^ 2 := by
        rw [mul_pow, ← Real.rpow_natCast ((X : ℝ) ^ (1 / 2 : ℝ)) 2, ← Real.rpow_mul hX_pos.le]
        norm_num
        ring
      rw [h_rhs]
      exact_mod_cast h_sq_nat
    exact le_of_sq_le_sq h_sq_real (by positivity)
  have h_extra_le :
      (1 : ℝ) + 2 * (g ^ ((k + 1) / 2) : ℝ) ≤
        (1 / 2 : ℝ) * ((X : ℝ) / Real.log (X : ℝ) ^ (1 / 10 : ℝ)) := by
    have hX12_ge : (1 : ℝ) ≤ (X : ℝ) ^ (1 / 2 : ℝ) := Real.one_le_rpow hX1 (by norm_num)
    have h_lhs : (1 : ℝ) + 2 * (g ^ ((k + 1) / 2) : ℝ) ≤
        (1 + 2 * (g : ℝ)) * (X : ℝ) ^ (1 / 2 : ℝ) := by
      calc
        (1 : ℝ) + 2 * (g ^ ((k + 1) / 2) : ℝ)
          ≤ 1 * (X : ℝ) ^ (1 / 2 : ℝ) + 2 * ((g : ℝ) * (X : ℝ) ^ (1 / 2 : ℝ)) := by
            gcongr
            linarith
        _ = (1 + 2 * (g : ℝ)) * (X : ℝ) ^ (1 / 2 : ℝ) := by ring
    have hlog_le_X : Real.log (X : ℝ) ^ (1 / 10 : ℝ) ≤ (X : ℝ) ^ (1 / 10 : ℝ) := by
      have hlog_le : Real.log (X : ℝ) ≤ (X : ℝ) :=
        (Real.log_le_sub_one_of_pos hX_pos).trans (by linarith)
      exact Real.rpow_le_rpow hlogX_pos.le hlog_le (by norm_num)
    have h_rhs : (1 + 2 * (g : ℝ)) * (X : ℝ) ^ (1 / 2 : ℝ) ≤
        (1 / 2 : ℝ) * ((X : ℝ) / Real.log (X : ℝ) ^ (1 / 10 : ℝ)) := by
      have hX910 : (X : ℝ) / (X : ℝ) ^ (1 / 10 : ℝ) = (X : ℝ) ^ (9 / 10 : ℝ) := by
        nth_rewrite 1 [← Real.rpow_one (X : ℝ)]
        rw [← Real.rpow_sub hX_pos]
        norm_num
      have hX910_split : (X : ℝ) ^ (9 / 10 : ℝ) = (X : ℝ) ^ (1 / 2 : ℝ) * (X : ℝ) ^ (2 / 5 : ℝ) := by
        rw [← Real.rpow_add hX_pos]
        norm_num
      have h_half_pow : (1 + 2 * (g : ℝ)) * (X : ℝ) ^ (1 / 2 : ℝ) ≤
          (1 / 2 : ℝ) * (X : ℝ) ^ (9 / 10 : ℝ) := by
        rw [hX910_split]
        have : 1 + 2 * (g : ℝ) ≤ (1 / 2 : ℝ) * (X : ℝ) ^ (2 / 5 : ℝ) := by linarith
        nlinarith [Real.rpow_pos_of_pos hX_pos (1 / 2 : ℝ)]
      have h_div_le : (X : ℝ) ^ (9 / 10 : ℝ) ≤ (X : ℝ) / Real.log (X : ℝ) ^ (1 / 10 : ℝ) := by
        rw [← hX910]
        exact div_le_div_of_nonneg_left hX_pos.le (Real.rpow_pos_of_pos hlogX_pos _) hlog_le_X
      linarith
    exact h_lhs.trans h_rhs
  have h_cast :
      ((sumsOfTwo g ∩ Set.Iio X).ncard : ℝ) ≤
        (1 : ℝ) + 2 * (g ^ ((k + 1) / 2) : ℝ) + ((sumsOfTwoPositive g ∩ Set.Iio X).ncard : ℝ) := by
    exact_mod_cast h_decomp
  linarith

theorem green_95_hasDensity_zero :
    LocalDensity.HasDensity (sumsOfTwo g) 0 := by
  rw [LocalDensity.HasDensity]
  have h_upper : ∀ᶠ X : ℕ in atTop,
      LocalDensity.partialDensity (sumsOfTwo g) Set.univ X ≤ (Real.log (X : ℝ) ^ (1 / 10 : ℝ))⁻¹ := by
    filter_upwards [zakharov_explicit_sumsOfTwo g hg palSet h_sub h_pos_cov h_sum_cov
      h_card h_sum_card h_add_mul h_add_exp, eventually_ge_atTop 2] with X hX hX2
    have hX_pos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
    simp only [LocalDensity.partialDensity, Set.inter_univ, Set.univ_inter, Set.ncard_Iio_nat]
    calc
      ((sumsOfTwo g ∩ Set.Iio X).ncard : ℝ) / (X : ℝ)
        ≤ ((X : ℝ) / Real.log (X : ℝ) ^ (1 / 10 : ℝ)) / (X : ℝ) :=
          div_le_div_of_nonneg_right hX hX_pos.le
      _ = (Real.log (X : ℝ) ^ (1 / 10 : ℝ))⁻¹ := by
          have hX_ne : (X : ℝ) ≠ 0 := hX_pos.ne'
          field_simp
  have h_lower : ∀ᶠ X : ℕ in atTop, (0 : ℝ) ≤ LocalDensity.partialDensity (sumsOfTwo g) Set.univ X :=
    Eventually.of_forall fun _ => by simp only [LocalDensity.partialDensity]; positivity
  have h_tendsto_zero :
      Tendsto (fun X : ℕ => (Real.log (X : ℝ) ^ (1 / 10 : ℝ))⁻¹) atTop (𝓝 0) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).inv_tendsto_atTop
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_tendsto_zero h_lower h_upper

theorem green_95_upperDensity_zero :
    LocalDensity.upperDensity (sumsOfTwo g) = 0 := by
  rw [LocalDensity.upperDensity]
  exact (green_95_hasDensity_zero g hg palSet h_sub h_pos_cov h_sum_cov h_card h_sum_card
    h_add_mul h_add_exp).limsup_eq

theorem green_95_lowerDensity_zero :
    LocalDensity.lowerDensity (sumsOfTwo g) = 0 := by
  rw [LocalDensity.lowerDensity]
  exact (green_95_hasDensity_zero g hg palSet h_sub h_pos_cov h_sum_cov h_card h_sum_card
    h_add_mul h_add_exp).liminf_eq

theorem green_95 :
    ¬ 0 < LocalDensity.lowerDensity (sumsOfTwo g) := by
  rw [green_95_lowerDensity_zero g hg palSet h_sub h_pos_cov h_sum_cov h_card h_sum_card
    h_add_mul h_add_exp]
  norm_num

end SumsOfTwo

end Asymptotics

end AsymptoticsInternal

/-! ## Main Exported Theorems (1:1 Standalone & FormalConjectures Signatures) -/

/-- Explicit quantitative Zakharov bound (`c = 1 / 10`) for sums of two positive base-`g` palindromes. -/
theorem zakharov_explicit_positive :
    ∀ g : ℕ, 2 ≤ g → ∀ᶠ X : ℕ in atTop,
      ((sumsOfTwoPositive g ∩ Set.Iio X).ncard : ℝ) ≤
        (X : ℝ) / Real.log X ^ ((1 : ℝ) / 10) := by
  intro g hg
  exact AsymptoticsInternal.zakharov_explicit_positive g hg palSet
    (fun k => sumsOfTwoPositive_inter_Iio_pow_subset hg)
    (fun n hn => card_palSet_le hg hn)
    (fun N => sum_card_palSet_Icc_le_nat hg)
    (card_palSet_add_le_mul g)
    (fun n m hm hmn => card_palSet_add_le_exp hg hm hmn)

/-- Explicit quantitative Zakharov bound (`c = 1 / 10`) for sums of two base-`g` palindromes (`0` allowed). -/
theorem zakharov_explicit_sumsOfTwo :
    ∀ g : ℕ, 2 ≤ g → ∀ᶠ X : ℕ in atTop,
      ((sumsOfTwo g ∩ Set.Iio X).ncard : ℝ) ≤
        (X : ℝ) / Real.log X ^ ((1 : ℝ) / 10) := by
  intro g hg
  exact AsymptoticsInternal.zakharov_explicit_sumsOfTwo g hg palSet
    (sumsOfTwo_subset_union g)
    (fun k => pos_palindromes_inter_Iio_pow_subset hg)
    (fun k => sumsOfTwoPositive_inter_Iio_pow_subset hg)
    (fun n hn => card_palSet_le hg hn)
    (fun N => sum_card_palSet_Icc_le_nat hg)
    (card_palSet_add_le_mul g)
    (fun n m hm hmn => card_palSet_add_le_exp hg hm hmn)

/-- Zakharov's Theorem (2024), matching `FormalConjectures` `Green95.green_95.variants.zakharov` 1:1. -/
theorem green_95_zakharov :
    ∀ g : ℕ, 2 ≤ g → ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in atTop,
      ((sumsOfTwoPositive g ∩ Set.Iio X).ncard : ℝ) ≤ (X : ℝ) / Real.log X ^ c := by
  intro g hg
  exact AsymptoticsInternal.green_95_zakharov g hg palSet
    (fun k => sumsOfTwoPositive_inter_Iio_pow_subset hg)
    (fun n hn => card_palSet_le hg hn)
    (fun N => sum_card_palSet_Icc_le_nat hg)
    (card_palSet_add_le_mul g)
    (fun n m hm hmn => card_palSet_add_le_exp hg hm hmn)

/-- Sums of two base-`g` palindromes have natural density zero for every base `g ≥ 2`. -/
theorem green_95_hasDensity_zero :
    ∀ g : ℕ, 2 ≤ g → LocalDensity.HasDensity (sumsOfTwo g) 0 := by
  intro g hg
  exact AsymptoticsInternal.green_95_hasDensity_zero g hg palSet
    (sumsOfTwo_subset_union g)
    (fun k => pos_palindromes_inter_Iio_pow_subset hg)
    (fun k => sumsOfTwoPositive_inter_Iio_pow_subset hg)
    (fun n hn => card_palSet_le hg hn)
    (fun N => sum_card_palSet_Icc_le_nat hg)
    (card_palSet_add_le_mul g)
    (fun n m hm hmn => card_palSet_add_le_exp hg hm hmn)

/-- Sums of two base-`g` palindromes have upper natural density zero for every base `g ≥ 2`. -/
theorem green_95_upperDensity_zero :
    ∀ g : ℕ, 2 ≤ g → LocalDensity.upperDensity (sumsOfTwo g) = 0 := by
  intro g hg
  exact AsymptoticsInternal.green_95_upperDensity_zero g hg palSet
    (sumsOfTwo_subset_union g)
    (fun k => pos_palindromes_inter_Iio_pow_subset hg)
    (fun k => sumsOfTwoPositive_inter_Iio_pow_subset hg)
    (fun n hn => card_palSet_le hg hn)
    (fun N => sum_card_palSet_Icc_le_nat hg)
    (card_palSet_add_le_mul g)
    (fun n m hm hmn => card_palSet_add_le_exp hg hm hmn)

/-- Sums of two base-`g` palindromes have lower natural density zero for every base `g ≥ 2`. -/
theorem green_95_lowerDensity_zero :
    ∀ g : ℕ, 2 ≤ g → LocalDensity.lowerDensity (sumsOfTwo g) = 0 := by
  intro g hg
  exact AsymptoticsInternal.green_95_lowerDensity_zero g hg palSet
    (sumsOfTwo_subset_union g)
    (fun k => pos_palindromes_inter_Iio_pow_subset hg)
    (fun k => sumsOfTwoPositive_inter_Iio_pow_subset hg)
    (fun n hn => card_palSet_le hg hn)
    (fun N => sum_card_palSet_Icc_le_nat hg)
    (card_palSet_add_le_mul g)
    (fun n m hm hmn => card_palSet_add_le_exp hg hm hmn)

/-- Ben Green's Open Problem 95 (answered negatively by Zakharov), matching `FormalConjectures` `Green95.green_95` 1:1. -/
theorem green_95 :
    ∀ g : ℕ, 2 ≤ g → ¬ 0 < LocalDensity.lowerDensity (sumsOfTwo g) := by
  intro g hg
  exact AsymptoticsInternal.green_95 g hg palSet
    (sumsOfTwo_subset_union g)
    (fun k => pos_palindromes_inter_Iio_pow_subset hg)
    (fun k => sumsOfTwoPositive_inter_Iio_pow_subset hg)
    (fun n hn => card_palSet_le hg hn)
    (fun N => sum_card_palSet_Icc_le_nat hg)
    (card_palSet_add_le_mul g)
    (fun n m hm hmn => card_palSet_add_le_exp hg hm hmn)

end Green95Local

#print axioms Green95Local.card_palSet_add_le_exp
#print axioms Green95Local.zakharov_explicit_positive
#print axioms Green95Local.zakharov_explicit_sumsOfTwo
#print axioms Green95Local.green_95_zakharov
#print axioms Green95Local.green_95_hasDensity_zero
#print axioms Green95Local.green_95_upperDensity_zero
#print axioms Green95Local.green_95_lowerDensity_zero
#print axioms Green95Local.green_95

namespace GreenBridge

/-! ### Definitional agreement of the local and upstream definitions -/

theorem isPalindrome_eq : Green95Local.IsPalindrome = Green95.IsPalindrome := rfl

theorem sumsOfTwo_eq : Green95Local.sumsOfTwo = Green95.sumsOfTwo := rfl

theorem sumsOfTwoPositive_eq : Green95Local.sumsOfTwoPositive = Green95.sumsOfTwoPositive := rfl

theorem partialDensity_eq (S A : Set ℕ) (b : ℕ) :
    LocalDensity.partialDensity S A b = Set.partialDensity S A b := rfl

theorem upperDensity_eq (S A : Set ℕ) : LocalDensity.upperDensity S A = Set.upperDensity S A := rfl

theorem lowerDensity_eq (S A : Set ℕ) : LocalDensity.lowerDensity S A = Set.lowerDensity S A := rfl

theorem hasDensity_eq (S : Set ℕ) (α : ℝ) (A : Set ℕ) :
    LocalDensity.HasDensity S α A = Set.HasDensity S α A := rfl

end GreenBridge

/-! ### The two bridge theorems: types are *exactly* those of the upstream statements -/

theorem bridge_green_95 : type_of% @Green95.green_95 := by
  intro g hg
  have h := Green95Local.green_95 g hg
  rw [GreenBridge.sumsOfTwo_eq, GreenBridge.lowerDensity_eq] at h
  exact h

theorem bridge_zakharov : type_of% @Green95.green_95.variants.zakharov := by
  intro g hg
  have h := Green95Local.green_95_zakharov g hg
  rw [GreenBridge.sumsOfTwoPositive_eq] at h
  exact h

/-! ### Sanity checks: the types, spelled out with the upstream names -/

example : ∀ g : ℕ, 2 ≤ g → ¬ 0 < (Green95.sumsOfTwo g).lowerDensity := bridge_green_95

example : ∀ g : ℕ, 2 ≤ g → ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in atTop,
    ((Green95.sumsOfTwoPositive g ∩ Set.Iio X).ncard : ℝ) ≤ (X : ℝ) / Real.log X ^ c :=
  bridge_zakharov

#check @bridge_green_95
#check @bridge_zakharov

#print axioms bridge_green_95
#print axioms bridge_zakharov
