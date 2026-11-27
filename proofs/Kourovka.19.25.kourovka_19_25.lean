import FormalConjectures.Kourovka.«19_25»

-- Problem: Conjecture 19.25
-- Upstream: formal-conjectures FormalConjectures/Kourovka/19_25.lean:51 (declaration Kourovka.«19.25».kourovka_19_25)
-- Credit: @ronak14p (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/- Counterexample: G = PSU(3,3) (as a permutation group on 28 points, simple via conjugacy-class
   certificates), H = C6 × S4 × (C7 ⋊ C6); both of order 6048 with totient sum 23984.
   All finite computations are checked by the kernel (decide +kernel). -/


namespace OMA1925

/-! ## Base-128 codes of functions on `{0, …, n-1}` -/

def get (c p : ℕ) : ℕ := c / 128 ^ p % 128

def encN (f : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, k => f k + 128 * encN f n (k + 1)

theorem get_lt (c p : ℕ) : get c p < 128 := Nat.mod_lt _ (by norm_num)

theorem get_zero_add (x y : ℕ) (hx : x < 128) : get (x + 128 * y) 0 = x := by
  unfold get
  rw [pow_zero, Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]

theorem get_succ_add (x y p : ℕ) (hx : x < 128) : get (x + 128 * y) (p + 1) = get y p := by
  unfold get
  rw [pow_succ', ← Nat.div_div_eq_div_mul]
  congr 2
  rw [Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt hx, zero_add]

theorem get_encN (f : ℕ → ℕ) : ∀ (n k : ℕ), (∀ i, k ≤ i → i < k + n → f i < 128) →
    ∀ p, p < n → get (encN f n k) p = f (k + p)
  | 0, _, _, _, hp => absurd hp (Nat.not_lt_zero _)
  | n + 1, k, hf, 0, _ => by
      rw [encN, get_zero_add _ _ (hf k le_rfl (by omega)), Nat.add_zero]
  | n + 1, k, hf, p + 1, hp => by
      rw [encN, get_succ_add _ _ _ (hf k le_rfl (by omega)),
        get_encN f n (k + 1) (fun i h1 h2 => hf i (by omega) (by omega)) p (by omega)]
      congr 1
      omega

theorem encN_congr (f g : ℕ → ℕ) : ∀ (n k : ℕ), (∀ i, k ≤ i → i < k + n → f i = g i) →
    encN f n k = encN g n k
  | 0, _, _ => rfl
  | n + 1, k, h => by
      rw [encN, encN, h k le_rfl (by omega),
        encN_congr f g n (k + 1) (fun i h1 h2 => h i (by omega) (by omega))]

def allBelow : ℕ → (ℕ → Bool) → Bool
  | 0, _ => true
  | k + 1, f => f k && allBelow k f

theorem allBelow_spec : ∀ (k : ℕ) (f : ℕ → Bool), allBelow k f = true → ∀ i, i < k → f i = true
  | 0, _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | k + 1, f, h, i, hi => by
      rw [allBelow, Bool.and_eq_true] at h
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
      · exact allBelow_spec k f h.2 i hi
      · subst hi; exact h.1

def sumBelow : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | k + 1, f => sumBelow k f + f k

theorem sumBelow_eq : ∀ (k : ℕ) (f : ℕ → ℕ), sumBelow k f = ∑ i ∈ Finset.range k, f i
  | 0, _ => rfl
  | k + 1, f => by rw [sumBelow, Finset.sum_range_succ, sumBelow_eq k f]

def comp (n c d : ℕ) : ℕ := encN (fun p => get c (get d p)) n 0

def idc (n : ℕ) : ℕ := encN (fun p => p) n 0

theorem get_comp (n c d p : ℕ) (hp : p < n) : get (comp n c d) p = get c (get d p) := by
  unfold comp
  rw [get_encN _ n 0 (fun i _ _ => get_lt _ _) p hp, zero_add]

theorem get_idc (n p : ℕ) (hn : n ≤ 128) (hp : p < n) : get (idc n) p = p := by
  unfold idc
  rw [get_encN _ n 0 (fun i _ h => by omega) p hp, zero_add]

/-! ## Codes of permutations -/

section perm
variable {n : ℕ}

def code (σ : Equiv.Perm (Fin n)) : ℕ :=
  encN (fun p => if h : p < n then ((σ ⟨p, h⟩ : Fin n) : ℕ) else 0) n 0

theorem get_code (hn : n ≤ 128) (σ : Equiv.Perm (Fin n)) (p : Fin n) :
    get (code σ) p = σ p := by
  unfold code
  rw [get_encN _ n 0 (fun i _ _ => by split <;> omega) p p.isLt, zero_add, dif_pos p.isLt]

theorem code_inj (hn : n ≤ 128) {σ τ : Equiv.Perm (Fin n)} (h : code σ = code τ) : σ = τ :=
  Equiv.ext fun p => Fin.ext (by rw [← get_code hn σ p, h, get_code hn τ p])

theorem code_mul (hn : n ≤ 128) (σ τ : Equiv.Perm (Fin n)) :
    code (σ * τ) = comp n (code σ) (code τ) := by
  show encN _ n 0 = encN _ n 0
  apply encN_congr
  intro i _ hi
  rw [zero_add] at hi
  rw [dif_pos hi, get_code hn τ ⟨i, hi⟩, get_code hn σ]
  rfl

theorem code_one (hn : n ≤ 128) : code (1 : Equiv.Perm (Fin n)) = idc n := by
  show encN _ n 0 = encN _ n 0
  apply encN_congr
  intro i _ hi
  rw [zero_add] at hi
  rw [dif_pos hi]
  rfl

theorem eq_one_iff (hn : n ≤ 128) (σ : Equiv.Perm (Fin n)) : σ = 1 ↔ code σ = idc n := by
  constructor
  · rintro rfl; exact code_one hn
  · intro h; exact code_inj hn (h.trans (code_one hn).symm)

def canon (n c : ℕ) : Bool := c == encN (get c) n 0 && allBelow n (fun p => decide (get c p < n))

def okPair (n c d : ℕ) : Bool :=
  canon n c && canon n d && comp n c d == idc n && comp n d c == idc n

theorem canon_spec {c : ℕ} (h : canon n c = true) :
    c = encN (get c) n 0 ∧ ∀ p, p < n → get c p < n := by
  unfold canon at h
  rw [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1, fun p hp => of_decide_eq_true (allBelow_spec n _ h.2 p hp)⟩

theorem okPair_spec {c d : ℕ} (h : okPair n c d = true) :
    canon n c = true ∧ canon n d = true ∧ comp n c d = idc n ∧ comp n d c = idc n := by
  unfold okPair at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem npos_of_fin (p : Fin n) : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) p.isLt

def ofC (n c d : ℕ) (hn : n ≤ 128) (h : okPair n c d = true) : Equiv.Perm (Fin n) where
  toFun p := ⟨get c p % n, Nat.mod_lt _ (npos_of_fin p)⟩
  invFun p := ⟨get d p % n, Nat.mod_lt _ (npos_of_fin p)⟩
  left_inv p := by
    obtain ⟨hc, _, _, hdc⟩ := okPair_spec h
    apply Fin.ext
    simp only
    rw [Nat.mod_eq_of_lt ((canon_spec hc).2 p p.isLt), ← get_comp n d c p p.isLt, hdc,
      get_idc n p hn p.isLt, Nat.mod_eq_of_lt p.isLt]
  right_inv p := by
    obtain ⟨_, hd, hcd, _⟩ := okPair_spec h
    apply Fin.ext
    simp only
    rw [Nat.mod_eq_of_lt ((canon_spec hd).2 p p.isLt), ← get_comp n c d p p.isLt, hcd,
      get_idc n p hn p.isLt, Nat.mod_eq_of_lt p.isLt]

theorem code_ofC (c d : ℕ) (hn : n ≤ 128) (h : okPair n c d = true) : code (ofC n c d hn h) = c := by
  obtain ⟨hc, _, _, _⟩ := okPair_spec h
  obtain ⟨h1, h2⟩ := canon_spec hc
  conv_rhs => rw [h1]
  show encN _ n 0 = encN _ n 0
  apply encN_congr
  intro i _ hi
  rw [zero_add] at hi
  rw [dif_pos hi]
  exact Nat.mod_eq_of_lt (h2 i hi)

theorem code_ofC_inv (c d : ℕ) (hn : n ≤ 128) (h : okPair n c d = true) :
    code (ofC n c d hn h)⁻¹ = d := by
  obtain ⟨_, hd, _, _⟩ := okPair_spec h
  obtain ⟨h1, h2⟩ := canon_spec hd
  conv_rhs => rw [h1]
  show encN _ n 0 = encN _ n 0
  apply encN_congr
  intro i _ hi
  rw [zero_add] at hi
  rw [dif_pos hi]
  exact Nat.mod_eq_of_lt (h2 i hi)

/-! ## Orders -/

def ordAux (n c : ℕ) : ℕ → ℕ → ℕ → ℕ
  | _, _, 0 => 0
  | x, k, f + 1 => if x == idc n then k else ordAux n c (comp n c x) (k + 1) f

theorem ordAux_spec (hn : n ≤ 128) (σ : Equiv.Perm (Fin n)) :
    ∀ (f k : ℕ), 0 < k → (∀ m, 0 < m → m < k → σ ^ m ≠ 1) →
      ordAux n (code σ) (code (σ ^ k)) k f ≠ 0 →
      orderOf σ = ordAux n (code σ) (code (σ ^ k)) k f ∧ ordAux n (code σ) (code (σ ^ k)) k f ≤ k + f
  | 0, k, _, _, h => absurd rfl h
  | f + 1, k, hk, hm, h => by
      by_cases hx : code (σ ^ k) = idc n
      · have e : ordAux n (code σ) (code (σ ^ k)) k (f + 1) = k := by
          rw [ordAux, if_pos (beq_iff_eq.mpr hx)]
        rw [e]
        refine ⟨?_, by omega⟩
        rw [orderOf_eq_iff hk]
        exact ⟨(eq_one_iff hn _).mpr hx, fun m h1 h2 => hm m h2 h1⟩
      · have e : ordAux n (code σ) (code (σ ^ k)) k (f + 1) =
            ordAux n (code σ) (code (σ ^ (k + 1))) (k + 1) f := by
          rw [ordAux, if_neg (by simpa using hx), pow_succ', code_mul hn]
        rw [e] at h ⊢
        have hk1 : σ ^ k ≠ 1 := fun h' => hx ((eq_one_iff hn _).mp h')
        have := ordAux_spec hn σ f (k + 1) (by omega)
          (fun m h1 h2 => by
            rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h2 | h2
            · exact hm m h1 h2
            · subst h2; exact hk1) h
        exact ⟨this.1, by omega⟩

def ordc (n c : ℕ) : ℕ := ordAux n c c 1 90

theorem ordc_spec (hn : n ≤ 128) (σ : Equiv.Perm (Fin n)) (h : ordc n (code σ) ≠ 0) :
    orderOf σ = ordc n (code σ) ∧ ordc n (code σ) ≤ 91 := by
  have := ordAux_spec hn σ 90 1 (by norm_num) (fun m h1 h2 => by omega) (by simpa [ordc] using h)
  simpa [ordc] using this

end perm

def totT : List ℕ := [0, 1, 1, 2, 2, 4, 2, 6, 4, 6, 4, 10, 4, 12, 6, 8, 8, 16, 6, 18, 8, 12, 10, 22, 8, 20, 12, 18, 12, 28, 8, 30, 16, 20, 16, 24, 12, 36, 18, 24, 16, 40, 12, 42, 20, 24, 22, 46, 16, 42, 20, 32, 24, 52, 18, 40, 24, 36, 28, 58, 16, 60, 30, 36, 32, 48, 20, 66, 32, 44, 24, 70, 24, 72, 36, 40, 36, 60, 24, 78, 32, 54, 40, 82, 24, 64, 42, 56, 40, 88, 24, 72]

theorem totT_all : allBelow 92 (fun r => totT.getD r 0 == Nat.totient r) = true := by decide +kernel

theorem totT_spec (r : ℕ) (hr : r ≤ 91) : totT.getD r 0 = Nat.totient r :=
  beq_iff_eq.mp (allBelow_spec 92 _ totT_all r (by omega))

end OMA1925

/- Stabiliser chains with three levels -/

namespace OMA1925

structure Chain where
  n : ℕ
  gens : List (ℕ × ℕ)
  s0 : ℕ
  s1 : ℕ
  s2 : ℕ
  b0 : ℕ
  b1 : ℕ
  b2 : ℕ
  T0 : List (ℕ × ℕ)
  T1 : List (ℕ × ℕ)
  T2 : List (ℕ × ℕ)
  I0 : List ℕ
  I1 : List ℕ
  I2 : List ℕ
  W0 : List (List ℕ)
  W1 : List (List ℕ)
  W2 : List (List ℕ)

namespace Chain

variable (C : Chain)

def T : ℕ → List (ℕ × ℕ)
  | 0 => C.T0
  | 1 => C.T1
  | _ => C.T2

def W : ℕ → List (List ℕ)
  | 0 => C.W0
  | 1 => C.W1
  | _ => C.W2

def sz : ℕ → ℕ
  | 0 => C.s0
  | 1 => C.s1
  | _ => C.s2

def uc (l i : ℕ) : ℕ := ((C.T l).getD i (0, 0)).1
def uic (l i : ℕ) : ℕ := ((C.T l).getD i (0, 0)).2
def gc (i : ℕ) : ℕ := (C.gens.getD i (0, 0)).1
def gic (i : ℕ) : ℕ := (C.gens.getD i (0, 0)).2
def wd (l i : ℕ) : List ℕ := (C.W l).getD i []
def ng : ℕ := C.gens.length

def wordc (w : List ℕ) : ℕ := w.foldr (fun i acc => comp C.n (C.gc i) acc) (idc C.n)

def ec3 (i j k : ℕ) : ℕ := comp C.n (C.uc 0 i) (comp C.n (C.uc 1 j) (C.uc 2 k))

def vc (v : ℕ) : ℕ := if v < C.s1 then C.uc 1 v else C.uc 2 (v - C.s1)

def c2ok' (k x : ℕ) : Bool := decide (k < C.s2) && C.uc 2 k == x
def c2ok (x : ℕ) : Bool := C.c2ok' (C.I2.getD (get x C.b2) 0) x

def c1ok'' (j k x : ℕ) : Bool := decide (j < C.s1) && decide (k < C.s2) && x == comp C.n (C.uc 1 j) (C.uc 2 k)
def c1ok' (j x : ℕ) : Bool := C.c1ok'' j (C.I2.getD (get (comp C.n (C.uic 1 j) x) C.b2) 0) x
def c1ok (x : ℕ) : Bool := C.c1ok' (C.I1.getD (get x C.b1) 0) x

def c0d (i j k x : ℕ) : Bool :=
  decide (i < C.s0) && decide (j < C.s1) && decide (k < C.s2) && x == C.ec3 i j k
def c0c (i j r1 x : ℕ) : Bool := C.c0d i j (C.I2.getD (get (comp C.n (C.uic 1 j) r1) C.b2) 0) x
def c0b (i r1 x : ℕ) : Bool := C.c0c i (C.I1.getD (get r1 C.b1) 0) r1 x
def c0a (i x : ℕ) : Bool := C.c0b i (comp C.n (C.uic 0 i) x) x
def c0ok (x : ℕ) : Bool := C.c0a (C.I0.getD (get x C.b0) 0) x

def checkBasic : Bool :=
  decide (C.n ≤ 128) && decide (C.b0 < C.n) && decide (C.b1 < C.n) && decide (C.b2 < C.n) &&
  decide (0 < C.s0) && decide (0 < C.s1) && decide (0 < C.s2)

def checkGens : Bool := allBelow C.ng (fun i => okPair C.n (C.gc i) (C.gic i))

def checkLevel (l : ℕ) : Bool :=
  allBelow (C.sz l) (fun i => okPair C.n (C.uc l i) (C.uic l i) &&
    C.uc l i == C.wordc (C.wd l i) && (C.wd l i).all (fun j => decide (j < C.ng)))

def checkFix : Bool :=
  allBelow C.s1 (fun i => get (C.uc 1 i) C.b0 == C.b0) &&
  allBelow C.s2 (fun i => get (C.uc 2 i) C.b0 == C.b0 && get (C.uc 2 i) C.b1 == C.b1)

def checkDist : Bool :=
  allBelow C.s0 (fun i => C.I0.getD (get (C.uc 0 i) C.b0) 0 == i) &&
  allBelow C.s1 (fun i => C.I1.getD (get (C.uc 1 i) C.b1) 0 == i) &&
  allBelow C.s2 (fun i => C.I2.getD (get (C.uc 2 i) C.b2) 0 == i)

def checkC2 : Bool := allBelow C.s2 (fun v => allBelow C.s2 (fun w => C.c2ok (comp C.n (C.uc 2 v) (C.uc 2 w))))

def checkC1 : Bool := allBelow (C.s1 + C.s2) (fun v => allBelow C.s1 (fun u => C.c1ok (comp C.n (C.vc v) (C.uc 1 u))))

def checkC0 : Bool := allBelow C.ng (fun g => allBelow C.s0 (fun u =>
  C.c0ok (comp C.n (C.gc g) (C.uc 0 u)) && C.c0ok (comp C.n (C.gic g) (C.uc 0 u))))

def checkId : Bool := C.uc 0 0 == idc C.n && C.uc 1 0 == idc C.n && C.uc 2 0 == idc C.n

def valid : Bool :=
  C.checkId && C.checkBasic && C.checkGens && C.checkLevel 0 && C.checkLevel 1 && C.checkLevel 2 &&
  C.checkFix && C.checkDist && C.checkC2 && C.checkC1 && C.checkC0

/- Permutations -/

def genP (i : ℕ) : Equiv.Perm (Fin C.n) :=
  if h : C.n ≤ 128 ∧ okPair C.n (C.gc i) (C.gic i) = true then ofC C.n _ _ h.1 h.2 else 1

def U (l i : ℕ) : Equiv.Perm (Fin C.n) :=
  if h : C.n ≤ 128 ∧ okPair C.n (C.uc l i) (C.uic l i) = true then ofC C.n _ _ h.1 h.2 else 1

def grp : Subgroup (Equiv.Perm (Fin C.n)) :=
  Subgroup.closure (Set.range (fun i : Fin C.ng => C.genP i))

def wordP (w : List ℕ) : Equiv.Perm (Fin C.n) := w.foldr (fun i acc => C.genP i * acc) 1

def e3 (i j k : ℕ) : Equiv.Perm (Fin C.n) := C.U 0 i * (C.U 1 j * C.U 2 k)

noncomputable instance : Fintype C.grp := Fintype.ofFinite _

variable {C}

section valid
variable (hv : C.valid = true)
include hv

theorem hBasic : C.checkBasic = true := by
  unfold valid at hv; simp only [Bool.and_eq_true] at hv; tauto
theorem hn : C.n ≤ 128 := by
  have := hBasic hv; unfold checkBasic at this; simp only [Bool.and_eq_true, decide_eq_true_eq] at this; tauto
theorem hb0 : C.b0 < C.n := by
  have := hBasic hv; unfold checkBasic at this; simp only [Bool.and_eq_true, decide_eq_true_eq] at this; tauto
theorem hb1 : C.b1 < C.n := by
  have := hBasic hv; unfold checkBasic at this; simp only [Bool.and_eq_true, decide_eq_true_eq] at this; tauto
theorem hb2 : C.b2 < C.n := by
  have := hBasic hv; unfold checkBasic at this; simp only [Bool.and_eq_true, decide_eq_true_eq] at this; tauto
theorem hId : C.checkId = true := by
  unfold valid at hv; simp only [Bool.and_eq_true] at hv; tauto
theorem hs0 : 0 < C.s0 := by
  have := hBasic hv; unfold checkBasic at this; simp only [Bool.and_eq_true, decide_eq_true_eq] at this; tauto
theorem hs1 : 0 < C.s1 := by
  have := hBasic hv; unfold checkBasic at this; simp only [Bool.and_eq_true, decide_eq_true_eq] at this; tauto
theorem hs2 : 0 < C.s2 := by
  have := hBasic hv; unfold checkBasic at this; simp only [Bool.and_eq_true, decide_eq_true_eq] at this; tauto
theorem hGens : C.checkGens = true := by
  unfold valid at hv; simp only [Bool.and_eq_true] at hv; tauto
theorem hLevel (l : ℕ) (hl : l < 3) : C.checkLevel l = true := by
  unfold valid at hv; simp only [Bool.and_eq_true] at hv
  interval_cases l <;> tauto
theorem hFix : C.checkFix = true := by
  unfold valid at hv; simp only [Bool.and_eq_true] at hv; tauto
theorem hDist : C.checkDist = true := by
  unfold valid at hv; simp only [Bool.and_eq_true] at hv; tauto
theorem hC2 : C.checkC2 = true := by
  unfold valid at hv; simp only [Bool.and_eq_true] at hv; tauto
theorem hC1 : C.checkC1 = true := by
  unfold valid at hv; simp only [Bool.and_eq_true] at hv; tauto
theorem hC0 : C.checkC0 = true := by
  unfold valid at hv; simp only [Bool.and_eq_true] at hv; tauto

theorem okU {l i : ℕ} (hl : l < 3) (hi : i < C.sz l) : okPair C.n (C.uc l i) (C.uic l i) = true := by
  have := allBelow_spec _ _ (hLevel hv l hl) i hi
  simp only [Bool.and_eq_true] at this
  exact this.1.1

theorem code_U {l i : ℕ} (hl : l < 3) (hi : i < C.sz l) : code (C.U l i) = C.uc l i := by
  unfold U; rw [dif_pos ⟨hn hv, okU hv hl hi⟩, code_ofC]

theorem code_U_inv {l i : ℕ} (hl : l < 3) (hi : i < C.sz l) : code (C.U l i)⁻¹ = C.uic l i := by
  unfold U; rw [dif_pos ⟨hn hv, okU hv hl hi⟩, code_ofC_inv]

theorem okG {i : ℕ} (hi : i < C.ng) : okPair C.n (C.gc i) (C.gic i) = true :=
  allBelow_spec _ _ (hGens hv) i hi

theorem code_genP {i : ℕ} (hi : i < C.ng) : code (C.genP i) = C.gc i := by
  unfold genP; rw [dif_pos ⟨hn hv, okG hv hi⟩, code_ofC]

theorem code_genP_inv {i : ℕ} (hi : i < C.ng) : code (C.genP i)⁻¹ = C.gic i := by
  unfold genP; rw [dif_pos ⟨hn hv, okG hv hi⟩, code_ofC_inv]

theorem U_apply {l i : ℕ} (hl : l < 3) (hi : i < C.sz l) (p : Fin C.n) :
    ((C.U l i p : Fin C.n) : ℕ) = get (C.uc l i) p := by
  rw [← get_code (hn hv) (C.U l i) p, code_U hv hl hi]

theorem code_e3 {i j k : ℕ} (hi : i < C.s0) (hj : j < C.s1) (hk : k < C.s2) :
    code (C.e3 i j k) = C.ec3 i j k := by
  unfold e3 ec3
  rw [code_mul (hn hv), code_mul (hn hv), code_U hv (l := 0) (by norm_num) hi,
    code_U hv (l := 1) (by norm_num) hj, code_U hv (l := 2) (by norm_num) hk]

theorem code_eq {σ τ : Equiv.Perm (Fin C.n)} (h : code σ = code τ) : σ = τ := code_inj (hn hv) h

end valid

theorem wordP_mem (w : List ℕ) (hw : ∀ j ∈ w, j < C.ng) : C.wordP w ∈ C.grp := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons a w ih =>
    show C.genP a * C.wordP w ∈ C.grp
    refine Subgroup.mul_mem _ (Subgroup.subset_closure ⟨⟨a, hw a (by simp)⟩, rfl⟩) ?_
    exact ih (fun j hj => hw j (by simp [hj]))

theorem code_wordP (hv : C.valid = true) (w : List ℕ) (hw : ∀ j ∈ w, j < C.ng) :
    code (C.wordP w) = C.wordc w := by
  induction w with
  | nil => exact code_one (hn hv)
  | cons a w ih =>
    show code (C.genP a * C.wordP w) = comp C.n (C.gc a) (C.wordc w)
    rw [code_mul (hn hv), code_genP hv (hw a (by simp)), ih (fun j hj => hw j (by simp [hj]))]

theorem U_mem (hv : C.valid = true) {l i : ℕ} (hl : l < 3) (hi : i < C.sz l) : C.U l i ∈ C.grp := by
  have h := allBelow_spec _ _ (hLevel hv l hl) i hi
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  have : C.U l i = C.wordP (C.wd l i) :=
    code_eq hv (by rw [code_U hv hl hi, code_wordP hv _ h.2, h.1.2])
  rw [this]; exact wordP_mem _ h.2

theorem e3_mem (hv : C.valid = true) {i j k : ℕ} (hi : i < C.s0) (hj : j < C.s1) (hk : k < C.s2) :
    C.e3 i j k ∈ C.grp :=
  Subgroup.mul_mem _ (U_mem hv (l := 0) (by norm_num) hi)
    (Subgroup.mul_mem _ (U_mem hv (l := 1) (by norm_num) hj) (U_mem hv (l := 2) (by norm_num) hk))

/- closure lemmas -/

theorem lemA (hv : C.valid = true) {v w : ℕ} (hv' : v < C.s2) (hw : w < C.s2) :
    ∃ k, k < C.s2 ∧ C.U 2 v * C.U 2 w = C.U 2 k := by
  have h := allBelow_spec _ _ (allBelow_spec _ _ (hC2 hv) v hv') w hw
  unfold c2ok c2ok' at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  refine ⟨_, h.1, code_eq hv ?_⟩
  rw [code_mul (hn hv), code_U hv (l := 2) (by norm_num) hv', code_U hv (l := 2) (by norm_num) hw,
    code_U hv (l := 2) (by norm_num) h.1, h.2]

def V (C : Chain) (v : ℕ) : Equiv.Perm (Fin C.n) := if v < C.s1 then C.U 1 v else C.U 2 (v - C.s1)

theorem lemB (hv : C.valid = true) {v u : ℕ} (hv' : v < C.s1 + C.s2) (hu : u < C.s1) :
    ∃ j k, j < C.s1 ∧ k < C.s2 ∧ C.V v * C.U 1 u = C.U 1 j * C.U 2 k := by
  have h := allBelow_spec _ _ (allBelow_spec _ _ (hC1 hv) v hv') u hu
  unfold c1ok c1ok' c1ok'' at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨_, _, h1, h2, code_eq hv ?_⟩
  rw [code_mul (hn hv), code_mul (hn hv), code_U hv (l := 1) (by norm_num) hu,
    code_U hv (l := 1) (by norm_num) h1, code_U hv (l := 2) (by norm_num) h2, ← h3]
  congr 1
  unfold V vc
  split_ifs with hs
  · exact code_U hv (l := 1) (by norm_num) hs
  · exact code_U hv (l := 2) (by norm_num) (show v - C.s1 < C.s2 by omega)

theorem lemC (hv : C.valid = true) {x : ℕ} (h : C.c0ok x = true) :
    ∃ i j k, i < C.s0 ∧ j < C.s1 ∧ k < C.s2 ∧ x = code (C.e3 i j k) := by
  unfold c0ok c0a c0b c0c c0d at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨_, _, _, h1, h2, h3, by rw [code_e3 hv h1 h2 h3]; exact h4⟩

def InS1 (C : Chain) (x : Equiv.Perm (Fin C.n)) : Prop := ∃ j k, j < C.s1 ∧ k < C.s2 ∧ x = C.U 1 j * C.U 2 k
def InS0 (C : Chain) (x : Equiv.Perm (Fin C.n)) : Prop :=
  ∃ i j k, i < C.s0 ∧ j < C.s1 ∧ k < C.s2 ∧ x = C.e3 i j k

theorem S1_mul (hv : C.valid = true) {x y : Equiv.Perm (Fin C.n)} (hx : C.InS1 x) (hy : C.InS1 y) :
    C.InS1 (x * y) := by
  obtain ⟨j, k, hj, hk, rfl⟩ := hx
  obtain ⟨j', k', hj', hk', rfl⟩ := hy
  obtain ⟨j2, k2, hj2, hk2, e1⟩ := lemB hv (v := C.s1 + k) (by omega) hj'
  have e1' : C.U 2 k * C.U 1 j' = C.U 1 j2 * C.U 2 k2 := by
    rw [← e1]; unfold V; rw [if_neg (by omega), Nat.add_sub_cancel_left]
  obtain ⟨j3, k3, hj3, hk3, e2⟩ := lemB hv (v := j) (by omega) hj2
  have e2' : C.U 1 j * C.U 1 j2 = C.U 1 j3 * C.U 2 k3 := by
    rw [← e2]; unfold V; rw [if_pos hj]
  obtain ⟨k4, hk4, e3⟩ := lemA hv hk3 hk2
  obtain ⟨k5, hk5, e4⟩ := lemA hv hk4 hk'
  refine ⟨j3, k5, hj3, hk5, ?_⟩
  calc C.U 1 j * C.U 2 k * (C.U 1 j' * C.U 2 k') = C.U 1 j * (C.U 2 k * C.U 1 j') * C.U 2 k' := by
        simp only [mul_assoc]
    _ = C.U 1 j * C.U 1 j2 * C.U 2 k2 * C.U 2 k' := by rw [e1']; simp only [mul_assoc]
    _ = C.U 1 j3 * (C.U 2 k3 * C.U 2 k2) * C.U 2 k' := by rw [e2']; simp only [mul_assoc]
    _ = C.U 1 j3 * C.U 2 k5 := by rw [e3, mul_assoc, e4]

theorem S0_left (hv : C.valid = true) (g : Equiv.Perm (Fin C.n))
    (hg : ∀ u, u < C.s0 → C.c0ok (comp C.n (code g) (C.uc 0 u)) = true)
    {x : Equiv.Perm (Fin C.n)} (hx : C.InS0 x) : C.InS0 (g * x) := by
  obtain ⟨i, j, k, hi, hj, hk, rfl⟩ := hx
  obtain ⟨i', j', k', hi', hj', hk', h⟩ := lemC hv (hg i hi)
  have e : g * C.U 0 i = C.e3 i' j' k' :=
    code_eq hv (by rw [code_mul (hn hv), code_U hv (l := 0) (by norm_num) hi, h])
  obtain ⟨j2, k2, hj2, hk2, e2⟩ := S1_mul hv (x := C.U 1 j' * C.U 2 k') (y := C.U 1 j * C.U 2 k)
    ⟨j', k', hj', hk', rfl⟩ ⟨j, k, hj, hk, rfl⟩
  refine ⟨i', j2, k2, hi', hj2, hk2, ?_⟩
  unfold e3 at e ⊢
  rw [← mul_assoc, e, mul_assoc, e2]

theorem U_zero (hv : C.valid = true) {l : ℕ} (hl : l < 3) : C.U l 0 = 1 := by
  have h := hId hv
  unfold checkId at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  have hl0 : 0 < C.sz l := by
    interval_cases l
    · exact hs0 hv
    · exact hs1 hv
    · exact hs2 hv
  apply code_eq hv
  rw [code_U hv hl hl0, code_one (hn hv)]
  interval_cases l
  · exact h.1.1
  · exact h.1.2
  · exact h.2

theorem closure_sub (hv : C.valid = true) {x : Equiv.Perm (Fin C.n)} (hx : x ∈ C.grp) : C.InS0 x := by
  have hid : C.InS0 1 := ⟨0, 0, 0, hs0 hv, hs1 hv, hs2 hv, by
    unfold e3; rw [U_zero hv (by norm_num), U_zero hv (by norm_num), U_zero hv (by norm_num)]; simp⟩
  induction hx using Subgroup.closure_induction_left with
  | one => exact hid
  | mul_left g hg y _ ih =>
    obtain ⟨⟨i, hi⟩, rfl⟩ := hg
    refine S0_left hv _ (fun u hu => ?_) ih
    have := allBelow_spec _ _ (allBelow_spec _ _ (hC0 hv) i hi) u hu
    rw [code_genP hv hi]
    simp only [Bool.and_eq_true] at this; exact this.1
  | inv_mul_cancel g hg y _ ih =>
    obtain ⟨⟨i, hi⟩, rfl⟩ := hg
    refine S0_left hv _ (fun u hu => ?_) ih
    have := allBelow_spec _ _ (allBelow_spec _ _ (hC0 hv) i hi) u hu
    rw [code_genP_inv hv hi]
    simp only [Bool.and_eq_true] at this; exact this.2

theorem e3_apply_b0 (hv : C.valid = true) {i j k : ℕ} (hi : i < C.s0) (hj : j < C.s1) (hk : k < C.s2) :
    ((C.e3 i j k ⟨C.b0, hb0 hv⟩ : Fin C.n) : ℕ) = get (C.uc 0 i) C.b0 := by
  have hf := hFix hv
  unfold checkFix at hf
  rw [Bool.and_eq_true] at hf
  have h1 := allBelow_spec _ _ hf.1 j hj
  have h2 := allBelow_spec _ _ hf.2 k hk
  simp only [Bool.and_eq_true, beq_iff_eq] at h1 h2
  have q2 : C.U 2 k ⟨C.b0, hb0 hv⟩ = ⟨C.b0, hb0 hv⟩ :=
    Fin.ext (by rw [U_apply hv (l := 2) (by norm_num) hk]; exact h2.1)
  have q1 : C.U 1 j ⟨C.b0, hb0 hv⟩ = ⟨C.b0, hb0 hv⟩ :=
    Fin.ext (by rw [U_apply hv (l := 1) (by norm_num) hj]; exact h1)
  unfold e3
  simp only [Equiv.Perm.mul_apply, q2, q1]
  rw [U_apply hv (l := 0) (by norm_num) hi]

theorem e3_inj (hv : C.valid = true) {i j k i' j' k' : ℕ} (hi : i < C.s0) (hj : j < C.s1) (hk : k < C.s2)
    (hi' : i' < C.s0) (hj' : j' < C.s1) (hk' : k' < C.s2) (h : C.e3 i j k = C.e3 i' j' k') :
    i = i' ∧ j = j' ∧ k = k' := by
  have hd := hDist hv
  unfold checkDist at hd
  simp only [Bool.and_eq_true] at hd
  have d0 := fun i hi => beq_iff_eq.mp (allBelow_spec _ _ hd.1.1 i hi)
  have d1 := fun i hi => beq_iff_eq.mp (allBelow_spec _ _ hd.1.2 i hi)
  have d2 := fun i hi => beq_iff_eq.mp (allBelow_spec _ _ hd.2 i hi)
  have ei : i = i' := by
    have := congrArg (fun σ => ((σ ⟨C.b0, hb0 hv⟩ : Fin C.n) : ℕ)) h
    try dsimp only at this
    rw [e3_apply_b0 hv hi hj hk, e3_apply_b0 hv hi' hj' hk'] at this
    rw [← d0 i hi, ← d0 i' hi', this]
  subst ei
  have h' : C.U 1 j * C.U 2 k = C.U 1 j' * C.U 2 k' := mul_left_cancel h
  have hf := hFix hv
  unfold checkFix at hf
  rw [Bool.and_eq_true] at hf
  have fix2 : ∀ k, k < C.s2 → C.U 2 k ⟨C.b1, hb1 hv⟩ = ⟨C.b1, hb1 hv⟩ := fun k hk => by
    have h2 := allBelow_spec _ _ hf.2 k hk
    simp only [Bool.and_eq_true, beq_iff_eq] at h2
    exact Fin.ext (by rw [U_apply hv (l := 2) (by norm_num) hk]; exact h2.2)
  have ej : j = j' := by
    have := congrArg (fun σ => ((σ ⟨C.b1, hb1 hv⟩ : Fin C.n) : ℕ)) h'
    simp only [Equiv.Perm.mul_apply, fix2 k hk, fix2 k' hk'] at this
    rw [U_apply hv (l := 1) (by norm_num) hj, U_apply hv (l := 1) (by norm_num) hj'] at this
    rw [← d1 j hj, ← d1 j' hj', this]
  subst ej
  have h'' : C.U 2 k = C.U 2 k' := mul_left_cancel h'
  refine ⟨rfl, rfl, ?_⟩
  have := congrArg (fun σ => ((σ ⟨C.b2, hb2 hv⟩ : Fin C.n) : ℕ)) h''
  try dsimp only at this
  rw [U_apply hv (l := 2) (by norm_num) hk, U_apply hv (l := 2) (by norm_num) hk'] at this
  rw [← d2 k hk, ← d2 k' hk', this]

/-- the enumeration map -/
def enum (hv : C.valid = true) (x : Fin C.s0 × Fin C.s1 × Fin C.s2) : C.grp :=
  ⟨C.e3 x.1 x.2.1 x.2.2, e3_mem hv x.1.isLt x.2.1.isLt x.2.2.isLt⟩

theorem enum_bij (hv : C.valid = true) : Function.Bijective (enum hv) := by
  constructor
  · rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ h
    have h' : C.e3 i j k = C.e3 i' j' k' := congrArg Subtype.val h
    obtain ⟨e1, e2, e3⟩ := e3_inj hv i.isLt j.isLt k.isLt i'.isLt j'.isLt k'.isLt h'
    rw [Fin.ext e1, Fin.ext e2, Fin.ext e3]
  · rintro ⟨x, hx⟩
    obtain ⟨i, j, k, hi, hj, hk, rfl⟩ := closure_sub hv hx
    exact ⟨(⟨i, hi⟩, ⟨j, hj⟩, ⟨k, hk⟩), rfl⟩

theorem card_grp (hv : C.valid = true) : Fintype.card C.grp = C.s0 * (C.s1 * C.s2) := by
  rw [← Fintype.card_of_bijective (enum_bij hv)]
  simp

theorem sum_grp (hv : C.valid = true) (F : Equiv.Perm (Fin C.n) → ℕ) :
    ∑ g : C.grp, F g = sumBelow C.s0 (fun i => sumBelow C.s1 (fun j => sumBelow C.s2 (fun k =>
      if h : i < C.s0 ∧ j < C.s1 ∧ k < C.s2 then F (C.e3 i j k) else 0))) := by
  rw [← (enum_bij hv).sum_comp (fun g : C.grp => F g), Fintype.sum_prod_type]
  simp only [sumBelow_eq, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
  rw [dif_pos ⟨i.isLt, j.isLt, k.isLt⟩]
  rfl

end Chain
end OMA1925

namespace OMA1925
open Chain
def PSU : Chain where
  n := 28
  gens := [(21283827150256489070059484581014230434882480517473030373635, 21265247147170884710357824735240861884010183616250744160642), (19739267728871132469168490595154729799086788035938468561798, 11887337116327804000282959348272157913769477773846043067528)]
  s0 := 28
  s1 := 27
  s2 := 8
  b0 := 0
  b1 := 1
  b2 := 4
  T0 := [(21345804202522702370566394586403006236616156700227129081984, 21345804202522702370566394586403006236616156700227129081984), (21327123554587093248615443030115380353457766610782839160833, 21327123554587093248615443030115380353457766610782839160833), (21265247147170884710357824735240861884010183616250744160642, 21283827150256489070059484581014230434882480517473030373635), (21283827150256489070059484581014230434882480517473030373635, 21265247147170884710357824735240861884010183616250744160642), (19689934518952446893728811125324039068250002622439915373188, 7890584977769971117618300734071462430622089532076347230862), (19714169337868660789054923931608719473955444092800048660997, 4776555149563068956647968934538105231400274572665958942996), (19739267728871132469168490595154729799086788035938468561798, 11887337116327804000282959348272157913769477773846043067528), (19764317808476528366449354337444031988128116619571917570823, 18985857592957880017327863296151740301241688741739914953348), (11887337116327804000282959348272157913769477773846043067528, 19739267728871132469168490595154729799086788035938468561798), (11880872651976967538739276097174957869920392340346090210313, 14995093644780007969998825797449770166606942170067991922058), (14995093644780007969998825797449770166606942170067991922058, 11880872651976967538739276097174957869920392340346090210313), (11867884970905006358834805162036636477483692368389994579211, 5517273190190207164563489655872086927637539823178892937624), (5542230128684301562142830563388545453088724240588001920140, 11904525316835879061581475796179368363000645541879443670801), (822623153350457948215918093757069589655712103014206981005, 1644035881951144830970312055382873199245963331761005038983), (7890584977769971117618300734071462430622089532076347230862, 19689934518952446893728811125324039068250002622439915373188), (8680537033273610513567817277570954646197944741700126968975, 11873824884781243122219645138479429066469195066792535541130), (37409280444449176145954333704372512328328833899677713552, 15834757871342309245381638115455756708797114753029907940123), (7063037768980136175100353319457158930142662355822580056209, 19727008468600144019217748004592441754299452968477351264410), (8772057639617481313101312010025373691994634187775003576850, 4812184983981879567899588919399909528984792837785800445071), (7988229959950606120786924161054059941145183254454464646163, 5566886283515229488683560856184732789012653594694004296334), (8705580439660587363240393148747418832044701660132298606868, 7950690197196798164129840549511330306537437801556541262232), (7901934268731794625334653025538113186847112427230716020501, 14981917020776545535845274281386299381145140944051091195016), (1625647028347305278189504033945437090803701695090524456726, 6296694962485878794289052499072764931108865869584666119059), (2501376237216813417625057443226869731143871727402805021079, 1698302130497729352040749643526802249744016362198899213581), (5517273190190207164563489655872086927637539823178892937624, 11867884970905006358834805162036636477483692368389994579211), (8668571152307773621489161649590238931334703744146353719193, 18935517934552004564981058879051681370084460892842545464198), (1717498395890577383052604967388688706187856220721569433882, 15693099372743540732623919391476181829414990162544720005131), (2354009329522747131457804624371195595966649786397698082715, 31374263321352172564166432674886107333861259611778468890)]
  T1 := [(21345804202522702370566394586403006236616156700227129081984, 21345804202522702370566394586403006236616156700227129081984), (15061705583399332734678200700639502325973846471855608742144, 7872146760916800436182610269825169665662628955280956735872), (8668571143608864874067017970905122540483437177141031092608, 18923546076065326455967803140314712647856489724566824861952), (11132965449713851018477606593025107664192058683454407426560, 7153842590349346128534400599269971328961558832618510846208), (11121039590598035615424532966153020498884596577222118326912, 11138420832249870932650079618466750802006296981041672701312), (15074733306642650419962944770196581155341822893743573074688, 20499766773066152436759256362433915260321843319113083340160), (3237687595900592948666079064261066290513002920740846371712, 13357903872732803516082338852277466195132582015346355258624), (10292915088365461410480507466200991123192510090051752051712, 18108830500161017755632729611202127107120127895412370754176), (14197374357114825071674100033338039744629705878047988040832, 1594710210394590137389532170187521762504791410043391183872), (20554989717682047168777447555593011516886279011642791789824, 18998069251320559632236571429668576518478007553178292374144), (19751090300720401018224921042803325961467233746912712787328, 4807203201757964634065364328169196520753495927465038711808), (14914639505177518426993056900646828767667165239208199767552, 8778998001257507409203205712523516656228284059940483616000), (15822546189319764099731448091316398201639301559459875423872, 8686571661684919988714692103450110982992152771581740042240), (3947998513586411550612032401000979467161342557463823959808, 1674446702590103600002806195626537413798459019909153376512), (6437391594857474367399037873240604276288427437075611256704, 17422276592957295358197289041633747769473344085197871926272), (18875269850165574300693807855146496478516387104472755685376, 7889919775778052079121568522787265297015951413849327011968), (3996899154025984019014194773126646810593725449737332721792, 14939342402188793253420006555279719800144291278042261687168), (8772675343672176649283506256131532832709491855455414339840, 3175667941298781121088200994187857995876687210359130704896), (9514699127473298466559138942913860221576372651171193915776, 14148534643205470083914606726073832047393973198884002072448), (7142578989897280228551678939746353413804592692685189843456, 7074583517825476281969159607067732978707533985759474502656), (5523307803938843660682126581254448538541442006198847212160, 17317397227518327902546710973452664882950638937566693509376), (21252941542590926047276811857989171973153808879323600702208, 21252941542590926047276811857989171973153808879323600702208), (3930286554871211154523202753789313712234975963196095351680, 18972392450677082939904964981930872134418641343963711474944), (4807203201757964634065364328169196520753495927465038711808, 19751090300720401018224921042803325961467233746912712787328), (12566803965235305924283023670592826586948894746067010129024, 13363414628184363597281420519233998694904729304168449606528), (18139537272072004450002565468319301117341197278715349945600, 18837871145588006663726163979951371497536901064322952891136), (6314987672691704030041029060227163959913653580717216648576, 853174313288311381565011009103042601295119245105692755968)]
  T2 := [(21345804202522702370566394586403006236616156700227129081984, 21345804202522702370566394586403006236616156700227129081984), (9496066013671375277841874953439994659746792558755665969280, 13437790078073407498480391027737753485219960075171714334848), (13437790078073407498480391027737753485219960075171714334848, 9496066013671375277841874953439994659746792558755665969280), (17403985105437850233166970929767016591513263015506403688576, 17403985105437850233166970929767016591513263015506403688576), (12689495668537323686971707005289769985835501307915030020224, 18120612694235699421779947588802697898046931479928640684160), (10366281426956500600488430755847718848982700728689249796224, 20505319038452209435017597968001640927931041266642817433728), (20505319038452209435017597968001640927931041266642817433728, 10366281426956500600488430755847718848982700728689249796224), (18120612694235699421779947588802697898046931479928640684160, 12689495668537323686971707005289769985835501307915030020224)]
  I0 := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
  I1 := [0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]
  I2 := [0, 0, 0, 0, 0, 1, 2, 3, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 5, 0, 6, 0, 0, 7, 0, 0, 0]
  W0 := [[], [0, 0], [0, 0, 0], [0], [1, 0, 0, 0], [1, 0], [1], [1, 0, 0], [1, 1], [1, 1, 0, 0], [0, 0, 1], [1, 1, 0], [1, 0, 1, 0, 1, 0], [0, 1, 0, 1, 0], [0, 1, 1], [0, 1], [0, 1, 0, 1, 1, 0], [1, 1, 0, 1, 0, 1, 0], [0, 1, 0], [0, 1, 1, 0], [0, 1, 0, 0, 0], [0, 1, 1, 0, 0], [1, 0, 1, 1], [1, 0, 1, 0], [0, 0, 0, 1], [0, 1, 0, 0], [1, 0, 1, 1, 0], [1, 0, 1]]
  W1 := [[], [1, 0, 1, 0, 0, 1, 0, 1, 0], [0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1], [0, 1, 1, 0, 1, 0, 1, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1], [1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1], [0, 1, 0, 1, 1, 0, 1, 0, 1], [0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1], [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0], [1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1], [0, 1, 0, 1, 0, 1, 0, 0], [1, 0, 1, 1, 0, 1, 1, 0], [0, 0, 1, 0, 1, 0, 0, 0, 1], [0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1], [1, 1, 0, 0, 0, 1, 0, 1, 0, 0], [1, 1, 0, 1, 1, 0, 1, 0], [0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0], [1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0], [0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0], [0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0], [1, 0, 0, 0, 1, 0, 1, 1, 0, 0], [0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1], [0, 1, 1, 0, 0, 0, 1, 1, 0, 1, 1, 0], [0, 0, 0, 1, 0, 1, 0, 1, 0, 1], [1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0], [1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1], [1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1]]
  W2 := [[], [1, 0, 0, 1, 0, 1, 0, 0, 1, 0], [1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0], [1, 0, 0, 1, 1, 0, 0, 1], [0, 1, 0, 0, 1], [0, 1, 1, 0, 0, 1, 1], [1, 0, 0, 1, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0]]

def C6c : Chain where
  n := 6
  gens := [(1350615297, 138248470533)]
  s0 := 6
  s1 := 1
  s2 := 1
  b0 := 0
  b1 := 0
  b2 := 0
  T0 := [(172878758016, 172878758016), (1350615297, 138248470533), (34370290050, 103618183812), (68987994627, 68987994627), (103618183812, 34370290050), (138248470533, 1350615297)]
  T1 := [(172878758016, 172878758016)]
  T2 := [(172878758016, 172878758016)]
  I0 := [0, 1, 2, 3, 4, 5]
  I1 := [0, 0, 0, 0, 0, 0]
  I2 := [0, 0, 0, 0, 0, 0]
  W0 := [[], [0], [0, 0], [0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0, 0]]
  W1 := [[]]
  W2 := [[]]

def S4c : Chain where
  n := 4
  gens := [(49409, 4210691), (6324225, 6324225)]
  s0 := 4
  s1 := 3
  s2 := 2
  b0 := 0
  b1 := 1
  b2 := 2
  T0 := [(6324352, 6324352), (49409, 4210691), (2097538, 2097538), (4210691, 49409)]
  T1 := [(6324352, 6324352), (2146560, 4211072), (4211072, 2146560)]
  T2 := [(6324352, 6324352), (4243584, 4243584)]
  I0 := [0, 1, 2, 3]
  I1 := [0, 0, 1, 2]
  I2 := [0, 0, 0, 1]
  W0 := [[], [0], [0, 0], [0, 0, 0]]
  W1 := [[], [1, 0], [1, 0, 1, 0]]
  W2 := [[], [0, 0, 1, 0, 0]]

def Fc : Chain where
  n := 7
  gens := [(207509045505, 22128481026054), (17627892253056, 8935144735360)]
  s0 := 7
  s1 := 6
  s2 := 1
  b0 := 0
  b1 := 1
  b2 := 0
  T0 := [(26561157824640, 26561157824640), (207509045505, 22128481026054), (4399667675522, 17695804228357), (137717908227, 4502467936774), (4570394705924, 13365942485761), (9003056824453, 21990777913475), (13195215454470, 69805818245)]
  T1 := [(26561157824640, 26561157824640), (22093592854784, 13400845337088), (17627892253056, 8935144735360), (13400845337088, 22093592854784), (8935144735360, 17627892253056), (4467579765504, 4467579765504)]
  T2 := [(26561157824640, 26561157824640)]
  I0 := [0, 1, 2, 3, 4, 5, 6]
  I1 := [0, 0, 1, 2, 3, 4, 5]
  I2 := [0, 0, 0, 0, 0, 0, 0]
  W0 := [[], [0], [0, 0], [1, 0], [0, 1, 0], [0, 0, 1, 0], [1, 0, 0]]
  W1 := [[], [1, 1], [1], [1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1]]
  W2 := [[]]

def TBL : ℕ := 263433418887299886757386445913454328768133441868282222971196236738333922440803229012168544606016773864482587290183027557485754609270018541378674112590474277356666106602530898263996090990154874680284164291279689555735509636342916685024429475425776291582761934644595071316527052138472964628938619635399074863491932056606483142473080909072150295351146330108264129243057595934220262422073984555584877158831620607855135289782198543236312343551602397647224222032256885719223603991648939332489460043097441023765272108689366883235087892867289374384403475152508552530264790205494629556180653711654984177351964089308311027110464575956061562510777457438909400907388579757586535783567610164722611616034971743082587594738146513158330725614476660172805142774189712416989876877108104955232578791048418070275986524679296828197001178957409531313295504775579891128109864840553066695768082310018369464244826389169508242180957608256209727330062594608051980717484650983540238976581212349197701183066938893919822866506926420827092804524026275325656484463450016705660277056056545611819903272411431952290188237767117594119112465781781385575370472762989138387206029378178608534496049117835073171632065228007059889167561144424970378268602705560635690529436606323729926356075251671552677555431009815514395890060988046266460506217012208504074147669691146702900881022696489875272058845613026919933942646297843664338924772796339458475646962358913857786364362145760237179670888351481984139702653850328408398071090894113180991927598643902493074569103750096365095205075362322135362919565505578915383472582413885867578769673239509790542192202959177540101593351580777452338209457800291528897588929829036947029973676441888723841069454795155105117807530579995616416737867667944795442039116916255408026187069304534711997006435893362125623651593168117719588910734460045742961430707831982087350268392491123504994154298401607112208204162684121042767925273871140261038372627792307306552985507687014650044364197850389849991904474528029590158168256697972203742762139036309109140860810235505078917744623645123048316391387510187256245979764391401188695988514556661629051271162103911233229913593838325007699759097382093863387419416783628274231602527158415735789522545788880106778482189208408602622303432451966991753996628383377069697381513447183791332362391373836807104243736636321987126838231847392880185500634312201587168988709820944304589692553225968525587821953970380410916536932168030417700743146023526906512559645039785331435515335453123829448508240188168566001582239523744816894366263296768419978233311962249740201717279829842382433798347765413893501890116358122050658502678210177953255284714251621786905222147543586038849926375810991693447193769351999216210692583126083601395309814569167001524242517698871104528936433885366573629261861716616178801911442214383531843412186913445720197791731654639910278275757850469321012232947429446426129159004297902438931084308396871727027603047873002365789514490876160538356010705907535118424179839419036651024105638409360432210648035678748238577210407951632019920611876404644533171424116676250310720029889962231808721131395035883118061161112131175493083782436440696047235124656729406094236876699127149837327334250222011721315916499608096880899451586821646284187037599875475110600236058167958387597108016267919200298949695499547593209296266701723329041010950386290949310539068393091343606134735478438829370646980265876906783796751147260465809151906288438578651634468637349982485991702537681547663559617776884991132990348357259880660266953040549868554012882225844913042750256367828578111170945998770081248475986702668686087059683902347710463529761163296361399560807635640622821775190197769417882959308937127774919551475270644900778659428134103425475077581728175527200263702640663421090997080452383544511085376194941180204881392015943515163127512106240597057576576031232146819900496780592293019982747945484928193594889364367673833119338167633981962664954038452831926699930351104545910103733901799028755078305084354319190434457086649604104163926065871154429396733276133082534323245669437195008519685268109165972564164112999637962553082872304860397558752843164993254191848590970746871532463855329351045694584485010181766551256956320555610139958279704558819022043578713720092397645641187694009309681424070098680935055934110771192152736717570448322206031433823611875068446084339398437969083625607775413215049032650659506621512077410244925733368792442384618124214637379044723496795366628498581341238860790472557483234066984286131903543664823485042123622374628244396170924715009434275905987105324408788822244638275563571029019430767805703997202699915920912717558308966982815997494249820063831203089479027184037727865700722364825253236844527405869234164883668528286915533445149312360788267382515003514040035068587192447950518739757483182792928340081881955801748813796112628314910657171920686661333284738449405413536367623329189404241307358465555911624905548351649650860030352690676398414777104198758702297664376393672506627189187926167886582989483443002823587040122463745055288455925658197942927900157839420170617522496930884811188720479888295733314352803979017635982609644089824852416702145546542035764051481692254241110692274869372152251853492077899306222819293253440270746087549624827013588215224233736940730632044102654373715572448074094703645038115475612910921385028764313854425345319918224737692797889134545109681269376487053592093624150970131935529814961592095276326557153748021029918366921608118699570902361060631050818858841836039296546271220407446736089319619923716184418653546981812765274050887154620844072139709064841800450283679458526224170949640293653420970050231618616569254040275901737081268814711087120258367728372121179101077453628872999867468088517201335969050962535150603943305554462730318629180118847674871628812088168185533411298168943332205229358362571879020973841203500163828004769810260262912937168012212496623515516495961694687956023361039807575902804387907845785122425831616930432744399560857536124485801705861824561224734224904716311854490479040717188333514984131350386634274536128777172511131897184200733537989363405801703611013931131544398963612511543726710583545135961452916385580284205861952926311280820438493064506491785461342298915032496045196858868851628430026600834984006876325510039454863238258930526101516241115508614777905499584079736331972929157213293839909392653598394112413540677065155753991839737334177036033714328764448161893889316269356014834243881084178806126908162501758545761178498055264496571411256133901146998465604897853298624713639666989609203947353170890878071709120992203712578100759761009015953797213685390038198360076894132416289691798190929511833429242030147398512985115888237410222139710612427069047867926362541345730932817617559485461700197918747940027183404412089780758922540102633980276760661743641374048862486279895004938296535088309818433761539512856401503619874300492142066430601284993241585078978327339151623972685608838824888105758579679623853084906414939075824889153623725343490758813984410004614339960908804114029765155953419394473463607436522983976192376161977834867573225200104294277803836884168204793852828337745008723174170491225364594528741266228536697576470315716747904119777899788683008683171521723483138316494550564568441481085025295816991290624666928598028389158436666185381931524698133767077306906400918587972850136631255087118852156452568381313895109744302895072626262496166746495504324119077960815036696084044103724453233989968594934973526631046062745396448606642278324052385848411014094908904297293302105290600072229432165407059126639350296653915287284966334723204504440348552805365975491335392453218394245996933791076456335417997816004853477558465335088216413853930429580909273707534885930205702561573378555850157453822939254711114137277616020741536746856365776271858500547561926920552488398645842126041582288541131090321894881899418332216992514690378544327438480525465803839129478145482701496333130320205639502042148448353674009200016102365546450522471929663272651761504705118336442646911539323997513382009605572408717293416237570725843808191038286697490339514631129820646131398592769768133381306707886750986092632197273579180286292005660117999967567959081017563665953597684524858877648158789044884626533080292400379049219586913091125082547311925287461102995435754395230852210754356865359692883729236256528014853780483027077561578857377362377260498730219534007823782767403318712804984878902923141102196138090434220663429801409635300664053116553766344263122632291851002593184406279648449193854319302227393465844629974021636010993096124697104233173577443082475540189086916998342995993881290707914349862108593627455674048762618865752922997401349447169116606292548177901425398568755102437280816188634171751212530994208625159863497158494294040174821593788836423606586499960382088728441743509173886242746299090582324740607986388039806566429431990109127243773168886562374210859431517963106180093992317240068669596955453761225105567356829194200245931874597464884076752002526704448955277220204918400806058946907647070803337647378440596756064564516917212052107458301269976696277867911064935301261335692192501612007216210034628569960070196051047284339222086991984981293358992892529100126697046533959600659158310770473124227733926328689286005778418768487959241715757215672242694282462905121570453858320355320361061914216625692105661413575316900920122061618400128345080584144022399764975394228379782830192970221833073142363774540225329954405987993216986404094300005159215221345776469749779342082211318396495025831134198278699883712605084011109645336949156356275136110483293204823698917808908430893513894104776807233940078487572172362213708743278639054419807812653975560999839392624520138797464975287359685297571227431246982602522803619109393785719842404656905203761326677772017859287517751309842749422188271714271890443088879060606247121047318251035615910876978676299494648410709945608813811315951190275041825813282680323036016605111891468676571868915165628144999935025370567403249367061608280551459553927353540285857169454686542917884704086299214333906359782733249025671778400470802327535695705212847503109216358224793791304649281682696045246316310758942641075916171563513962142804651201619408329972759067088132252245354938173174071604243034599053757257051048114300071121253475522052173387777309182294355241774913646893582035887924552224274289755583564009247487845097680021959779485738707098735013633710215273707056596712868289058268084797012410067969962432484461055649451864676015245855766876784841043325430525865302028845342420309520161989715341750196586321635568893431760776165506661471084420180221113579314784457231298606368584402742985447272189988898766715201972523591167908082731092951219779799039783395889791606994064355989582508881822032641349714573184731402428095257035413457378314999444839767752012616991776535366175350866529231946459791455866172917334063730516540727238154238722151447313456469920381393056768798202708619341391967599484031395750593116111555069703192320431638191778764016074451122556881249614946192782750234597378811216680299561633831902601460757557710035087088975385960802590856355371123445754118706606840262413303643924258393824358069299239253178455017784485233156071175681902313521603181533977847516854854640777743295555184141588408126353584792915450608310366629746834906298092505345801271301312576461608001067265635963253633423844503322076640051020685252333226920012040830349769940420601817946894618427169979244180336815756395077814388426393058560015836839753122925657117539732615917459528193633524648996151364379470754380861874813468467698158996489549420825687672790437310859777362610134633028517629996809379132643658710504699485219766714818940144019079783744211293378918169284403360006884320030337750459522032806639198716096852772410180397320890142900201252194172528356436376196114145402734136267563320992105802359289754786279310057951791881171891040065469048481006791381541638367382070575134544388991938801857803685703978392181099389810377964857901079277909277948661139314037504960060545227894723311653297686707258674473829841910191033025025139018956932714835475491734968534674200729366171823829812945458577905297543648630626350706316953270740375273270743750397628935406328835021945337460919706601728082489161994701478745133569120129149113320234461121997261897691978753664744615252443438056812335900677989669319323884308007906685679550094688280702009502499294674822804147821160668885466104724801122169322034595648458406366422483595013344414841098591219492895687407918136507413961029214264916446070968554468392664610622979044308917969243670166893975835654744082544312035946105801030395279609354061558288974832202744744763242749890753742030561632540399731200325520249481849530097428754232696000916560113157419183362223855977000702983230486641106073953242749092483658558037675321316180225196326778270601059266806392025555214190279522700134313021964384449081511410030526740614675156098652972303371089245750346783603327790003084126430566214135411049527692919611636035001985411564693431944833654475390584013975778837708191468341998380242125982571745110656482226914947475535207596560118523996659858037415920167776466674795447661663642707558050478809920593632208232836411962948050381555307298793060685226530232288230025142515597743596190191629559182962570155262406651825050283625519277924215786842406078876871246917264247586455757758142577921109695065703541614893552600691239212004942471833617869852993641391826681924584711203355967519929640382036185330265628060867511715494281443466667881616094471591336056876163684029535059522426856291177909169245424229094742586300616391716920331927941735910565669608219937214133757111185639253334832080005461509496609494600575653301670885878814538478615075594672552730700252844671260565712432836685403312593340536684490117040111672902241963703729007745808900117779804079460964228573136831170596417686241432597515416789220326401397847276861391596133938309067985638271456719666424652952223833717496959328286759933981599102875790778205972065092268130500008539635582377444932382473130220089960028896234694052573196928239831343253246309836631670761449675445841621604941272339428356143859785842772217023846681319857722220533483053508851332394379024887352536233354925445868240472225142238610023973497673045718854389265466585549762843001045535236601687606095230074089685743517347493428899443427443835036628473135290394650056500699544891977339421864613812019672910674699280452462967851896118582517889301705323797707466320419570473768055955127500888039760794973631746943426906710691357026924574761988266533675896291659859757964685196790760769192407785074712939049908718173640821718727129178138824882448631902331285672994029514843010169886766153920497177567792032618933449409633889728705958603738471292925795891014464306055315230604392866028126966643112080623419636555507050762562243498963468935331580695402323942815945574049809308318210055139634724278372958545397340482688401453931965463961756033634567249223371104373871424236499840810730107004188944038664495747220145965110145996617562723983334721309081603877848012027817613051884196338473119350324118675162002838273616554849079797970187121091990324116006029172097523235158534378109661832298787542592035333755512757213006969405159171376810354124401812409718864330559794726045409643227281827591160117389268907384633936913328216864845765781798930379341479356082969934951646207780960275203742120705987098902851093310041423545914914169942881413435281229255918618681675500006997699786662401715617129374689799834208659581240917580321585759048204240379383139915723784055370445167433350510495000960673470008901297645555921845953029905359857769301523025418695355874569567463830877957967507778820471511292445478996478161195270734353203067218873398014471120556795360974584617552194993292724319083686952275337861969624221641709128117670888500263473287926966064719027387069937235659208134174135688049508326686760471936269461757349114655829786627143055633398392433939704552160848448479052357864465793355383844254644452850618653005602644984963132307949000110887891807488486924975422101848204336261911836738764414564720547817155464315236696990852533553587719062670895748215874973363454192576461812059312128763159407255965996498913911224924044370640006155133837183468588948373601991721901442592959952296252701551970062503974321344388366581413940105259953129804802425164970836787930804880447888248918422707189135492220534973922810575798042350985670285252370728182590887873692639498018439538957184819723361320171634658416477667706658796313182455075474306620571599410368355165222618120502599358502900183842991232120332048798691385207570134855139576430612756792632505683458064097215023314451623470165987839562936568497336079798821323532847449154426626165473062072669134853130708692648670753883875802074346749159894527983702885017304740664574181965067748715578709709894414903797487084531854264479116080053743130759914567660420334724830239299095362440768453785194477611358709842346978854002674454680989444532008047329052971159107485738998418185515619991883512602407014134462023950820993422769822886453147867480787591659466097311919888925301320359055972030945087415072110419023741754367148682592777264131404245928403208135295147583515355904948436001604208398452605622322715598779442830680386379039192648273875991596850714038895164229096098750758544366300338894391277096065418081363441281530185041260431522934784919977968387443524227485776319092404509729871439311993081427368595647060523596027614123468491847891994079029448165172116351404811326842136256728069978670265415484622235798456226589169284896495676371861680310442602325602546917345005972909169554964499128510918839422505087818525186408841034083920515333864554691914081713268579291451895683236558076990900032013967053821423951254305992434452394793316907751968603535065040356766052405526062337465270385806157792790786543010046783863943432266089657951940980853889462804796089491262072903009768459413568242062263649646932808479138863725157385495445673211824840661839363872545991977657322852622741294360643593590748810901309119379633752126698097817672145142032471115244231417305144929148995067808766993363959203420554863925313473507162438152886468275852967382449170749907831157645528884296264926319581414836061978245980239182334807334819083897203416788429902646840580435238940910545081075760044773889496743431256410013394885891529172200868331451305684133417837861352747618147657426113262787931843164704025163894353253530086859178958584453782293947447153198530316574864416845096482732149872027999969953622634497435024754382707132151364662623577130936692904062504445141927093459570501860180152777344107608111190024925962218551049467329089135556886211942796842005109654584846658371804784046255762039818577605747004839628398801054998453748898438526794158877848940172254609972256635454778096271186173469809295095205662817981878091179615710543844026863474011249982251173091413044389532444214738608870571058364960088769607894131825179095494629299872058469551048056667622207965789803260158289170949137206604472021450583334195704512871708178528124995472053995981880152818081202972464355778799542984191961561594376666627347460742623730874826845774333419043598205998384851385452636729103051347656572946303081134833651834411254310622322479803195869890897785262051278323357504506157939482195973196983828540809989739820762774033948777073657704383579285996599324659718835706834429144004156679296313880415880930082158613199095117477100944309789155171361507375989097488795184722844082956619807636689686202896441341918679079811034743204628400166406735884806676640118899145552984008515034942653470051835290974854874817310361291841126892493990646087859663039620242578992388555195152023138191122178830920175210538889390506983795182467143040724607244896020944975179756279437247587313667338949595750965818033273077228015717076240853221176443488011923437222115425221586958943806550912716335584321925821983027706488595992836501059836461333006690110895816002718848647254247548436861437225493879966768430018853149634428594032337438816579812232111105534769426750425519082888243854159939427854470539108600796398968347844600374970825982899743561155564069827455230991822590212830851611018588164132362814746760371602858658289191538993832944654914392862327579090014378349536417144160796741211826398270393929396010055561042774289811833399122530867487069553084547791175203192042466793853937840409935287470355160002566363004434450143311540839010191348822126276200255691630180831849634714466869177508828953338941566706153781789820126714984084933097472435346228155525733056269439663231257948289570114935823279251204444115492570934804093137226194576121861436397832281331772791404872391952823879024682519753412328837573549082718317483266724377602903405762576495011268382876547582585466711438802441668321393554271769070096288710485317712566844163303235366889936279346341359353562932975228684484799078117833535708900174261625675332781963667176827189331171408163334803020420139790208990808518519918502720802934443367314959261431443821044358674680692195940391273122008435278734793608913021426041447313265480964577059622721924919883957901198678388855332939925434676617019687919214700407035957798692943673189303099267318448886339719661413026656475372138998217796070538313194868486157605488487483846733329997869273208780379268098569472815255225581364273109963221133470834956698588339746415026549558301435629902984748672334902746724795580336191148952083509420533939116242537931904678893245908974795421749941221787778830377873825355250800585890381507918819071084790995602785178307393690252479859640462219492287262836354147979482499686818258453421178073573660193579638951436455166204996312565854612802660083339760284744968548551851379289126776644065351460384136161562861427683441897054208657523862722870453658537329539407435923640612716955766601825172018658929412750188572836656806670922822217450872150171187696455325746141364346137057285516756332058934612227805547790223416800290743238249733189269515058717114475090298554954252741130277746543547050776753121270022187811304886072617857721418873705979263561766815133056988364803920631077417133792134225836435085527264701506374231862541455763534989363405618098197452863913060784029094944902807971915580824567300906383318978744502708567109370808240456055918058433372758483914924505358610983685214544468738674619650842311046941289660995214427699058665978628944544235202671625656207792093546375074807015902223480592627084294617285354160912322485769418968819948446624443679487657437831424349675511769578105262013310012651949479199604603753269980196897441507308498223700980870732721083627694171257507397544434041953418944507118354982011682693680785233488834473332463899336907182280962026107104706336630135023760677566114067299274427023126183825455646805192904495710545369359370781649791080802124789195099253850489945835884951499266928281986442938154644931469576948428616533144927177593135973636749888027404041580017864531492306583452022870682792629050267045442797164912113294029083546293949575148485931210047837223265325597807776378557634245777541563638331495786968223718510170508506358486831714055922016900133387506466657163005306101358033909500979497081428637617105679765315510299763189414327043784696903001508368121863513566163557894907566902141694420116482199841830774251593852184822878895927825661222513026549011457799356119908757324427407813017729405941534317156057460874926872220936681696783118250264871812864311686001583876942881698534657124908207125995354054810004265097624458628717995611968932169617363726102110886619578114787049974827947183288062921053523354484727423187412102371243304513307557300424538365224653398594108860535210258894026313456494063743285089042949402530596032115566283350604710388157177251200958209463479494582151592753244745420358779907847848890205329379463440376572061833622647105621901056083354503262995092259328020448133770124841096136016982518996403607514266834898482366925379612043563634620410160173069498876145464928543543662430865430158479078472154698245332650051309500116020403325018203374487996804660017976825433771723944827266949098807566391001078200889496282714188220222703217823374561521192652642393885737579417991357285399779486110164368235761795466469804951996355662738630577828498652991036767752514143013942899116558065625144469400009143168490394338561447734959942550598166542970798645669437507220888511613556330375630979935594433330703463233284111399532999095776764741063119983565933384447003285586443047985512789473201517391704258475458687702359682713113540080096282536408219270721556899833173939634599943767688931391907555524501830283445893643001399651956007384660043025773014848667188052041998388746106032241698543911620513989487722760658468932357684294891039409367250675518716339053715174679320577290930757244588725891592768068067355196711213538464453113757121107334013007337788736510900927931829022332717389002173500195486386764088678284601747002738461702194678075236893791256693707793448907005999235900798058648243250674918462102507134479766569892182867168371877493255579691260583193045018403461442196257636379411211414748756288537656899726463850696051201954357477797814754280656352647757815849460547907177052918250638904356905715385818985489183973391761624671559347358488780854162616418784818233526449676434351588535011115207745332693185687829611510831001076050184218559156732898910568490429275503810002817075126782581643846242624145215708117541852315720455894834978427077686529901818022801920830857528022389753969569482000054049459899099077693561537253149974027215704018073366695829952314661219432521044715197087064794411148590301854735862315289452768821021339165295370437054940917893757618195421534472311743083124541860050260956695917348331770676861572251747487762312328937110650930938974242433150698727452479841275733622806267357106593246740252325236180073825761632059339263310234547589992645814403967412362518765526136397366995378208824657476124079283083834482824174540047335390344273978297556549432765709159692917884151849410568044182741993766751772261824090083861649648913246986997311717915547724577590594316640414082383697203820045331557119346804611116662423908669682354057342960413214540833395397443391507300804668621552877146305010476022363555911209908315635202463331635038611281391147884944588153872436673494285552975564331622662675316689793306169178218219983548666746326696006126939950723863457545502808174532705444159721468839525529821280288033171414309877617569465174631302433663507795121520400145147100442737260807810272774450322767246289027313601785397867465780475919203924342555744353181532921220153777609670188451887295691242146698741562712586892028773807403419390999095079729182828226618963411278613550013507327808031550934476790401736544212197213910870995497398212200239093732576204929490223084229005153168262056278173463801002325491154842505901454001471882121160682051907556049779527813601228701825237813332929312376483246561839041569452111503780807770268371842644934881855265363892245739263881230228058638375769345803305768868756289020167186942865281688500853089249744360097286551810294642839418679740042852131974459870567627397770735166509695660437985012115117681301200189738151729120983028621193625541967732958755990298326490890521803918328066899763518001823555052419625858595432874122320357344645672873768960611236069751195637074743725829778932632704110350806939513721354767849796823508179882153269991719301430333059719324142315146955562238276915253276260854020009838671959693282109964521121960735777327543504277964119866231837385768351339139624186460600085496889335678598977505522640350108113728166371426450102775375944373842331872708026637402557283449810772420658128768984770220078510767475799470415789653669364508899184372622313608083140950391362054920514423844299524925659081527430441020703476000139484902617994137066052950817889219077286224488147635080103024169600900675271434973459105751686907773895895584538328218462486985131485384647148391656499858431408815559904267264145358600756357595329348678103478162286760414093846505320295904547007143619462591377405765302258366909096581030902541553633246963884879791880361285724887500213436775775971137500950689948256985372051062604577179282213045650187386967622285380385882486930225049227689881324812374594691963582983017220061357195250575365142218364969845250951282520693978550887615057058131275424415831518986938030544740628171674232911457220045057714662659515857895274669484123174811579509249923653896568526181993903071753943868186477065098823968019612247483206055050098763697587005803681428837553895953700226101811172972694223266569035951199367841227235252995562399643240582277254987685045443388243527833250411890153002134249817992205179512634634641013534666908972642917840036117561186050386490824882431920542384130175233703478442280006157930996145878134748399870198197507816443107266013152572616946172340678497169605701353448374362168186013622060917661296113873045846207231337626311044679620311454017156059345870240272645331170936265325888209673260779899861369766174737243729302699112695015506602057232125432923969208146910454397784463891113552347985304491615227491303279614228002376695999425713692108234095805424164246267942450748801068641571475275825159804412305699522284870621442708683156571307707912491193474138771149019119494794708583896610299301519609635855935015545848065953966368457738605977170496304545636845092903939598516573114214546523653892225096507085259498629164620420704296861834730412655611234265000954398110946094503194951824144621503563703902825775396072574152625657361888466786633828719695264500822673742404944091619979496759900484594169496539577122753900160708570477499596203071327466216918022437654491051783195359197639308144832333972868008498290980517568633811807504777939892903554532221614840530765375232181480993473692710237440892854935953931929186353410213260696145909563470780486394484005378254183259302961650629464485835550404069615526450456127259088204092692872708204897022438334389316273999014623524957387059473245338169041910078124614481472074865115295891731642472483239868346955736575506696310265830010912835975502715878392779544301591907140298809346801277519215394566904536539324627383939805641525585133599592562461060780807786027180811083563972140928256264047152689589239079806690205498746834076811235957984940628346432549594016574974817835455905077451995255427347162808290718009879362133304382752382878824611864467176769189174719465077149544591419420490093257375695965606751156435049986264524406890215271490832325617650457861276449212844024372606869288919954455229760905356976089548420398080266610682756776166137946541926476438860783653730664009613887344297163984982217920262630003710975134595571516506408811676541405634511578630891869418597258410664852586277706363519193396188358491674021103401072964323109522916675033666929545650582544149914391391758053693612049234556408312143831768772686016282624
def reps : List ℕ := [0, 1, 2, 3, 4, 6, 8, 9, 10, 11, 25, 217, 242, 272]
def repOrd : List ℕ := [1, 4, 4, 2, 8, 8, 6, 12, 12, 3, 3, 4, 7, 7]
def prods : List (List (List ℕ)) := [[[], []], [[648], [39, 164, 3843]], [[2, 649], [58, 1142, 4437]], [[3, 2974, 5812], [219, 1947]], [[30, 2783], [13, 2161]], [[63, 5706], [35, 2801]], [[117, 3390], [36, 2876]], [[9, 1733, 4552], [609, 1752]], [[97, 1079], [16, 5640]], [[18, 3354, 4521], [18, 669, 3603, 3946]], [[96, 1129], [1296]], [[218, 433], [387, 770]], [[313, 5537], [242, 1231]], [[333, 3566], [277, 2291]]]
end OMA1925

namespace OMA1925

theorem sumBelow_congr : ∀ (k : ℕ) (f g : ℕ → ℕ), (∀ i, i < k → f i = g i) → sumBelow k f = sumBelow k g
  | 0, _, _, _ => rfl
  | k + 1, f, g, h => by
      rw [sumBelow, sumBelow, sumBelow_congr k f g (fun i hi => h i (by omega)), h k (by omega)]

theorem orderOf_conj' {G : Type*} [Group G] (c x : G) : orderOf (c⁻¹ * x * c) = orderOf x := by
  have := orderOf_injective (MulAut.conj c⁻¹).toMonoidHom (MulAut.conj c⁻¹).injective x
  simpa using this

namespace Chain
variable {C : Chain}

def checkOrd (C : Chain) : Bool := allBelow C.s0 (fun i => allBelow C.s1 (fun j => allBelow C.s2 (fun k =>
  ordc C.n (C.ec3 i j k) != 0)))

theorem sum_grp_ord (hv : C.valid = true) (ho : C.checkOrd = true) (F : ℕ → ℕ) :
    ∑ g : C.grp, F (orderOf g) = sumBelow C.s0 (fun i => sumBelow C.s1 (fun j => sumBelow C.s2 (fun k =>
      F (ordc C.n (C.ec3 i j k))))) := by
  have : ∑ g : C.grp, F (orderOf g) = ∑ g : C.grp, (fun σ => F (orderOf σ)) (g : Equiv.Perm (Fin C.n)) := by
    simp only [Subgroup.orderOf_coe]
  refine this.trans ((sum_grp hv (fun σ => F (orderOf σ))).trans ?_)
  refine sumBelow_congr _ _ _ (fun i hi => sumBelow_congr _ _ _ (fun j hj => sumBelow_congr _ _ _ (fun k hk => ?_)))
  rw [dif_pos ⟨hi, hj, hk⟩]
  have h0 := allBelow_spec _ _ (allBelow_spec _ _ (allBelow_spec _ _ ho i hi) j hj) k hk
  simp only [bne_iff_ne, ne_eq] at h0
  rw [← code_e3 hv hi hj hk] at h0 ⊢
  rw [(ordc_spec (hn hv) _ h0).1]

end Chain

open Chain

/- The simple group `PSU(3,3)` on 28 points -/

def tb (t : ℕ) : ℕ := TBL / 131072 ^ t % 131072

def ecT (t : ℕ) : ℕ := PSU.ec3 (t / 216) (t / 8 % 27) (t % 8)

def eT (t : ℕ) : Equiv.Perm (Fin PSU.n) := PSU.e3 (t / 216) (t / 8 % 27) (t % 8)

def ck2 (d x : ℕ) : Bool :=
  decide (d / 16 < 6048) && decide (d % 16 < 14) &&
    comp PSU.n (ecT (d / 16)) x == comp PSU.n (ecT (reps.getD (d % 16) 0)) (ecT (d / 16))

def checkConj : Bool := allBelow 28 (fun i => allBelow 27 (fun j => allBelow 8 (fun k =>
  ck2 (tb (i * 216 + j * 8 + k)) (PSU.ec3 i j k))))

def checkReps : Bool := allBelow 14 (fun r => decide (reps.getD r 0 < 6048) &&
  ordc PSU.n (ecT (reps.getD r 0)) == repOrd.getD r 0 && repOrd.getD r 0 != 0)

def checkProds : Bool := allBelow 14 (fun r => decide (r = 0) || allBelow 2 (fun g =>
  ((prods.getD r []).getD g []).all (fun s => decide (s < 6048) && tb s % 16 == r) &&
  ((prods.getD r []).getD g []).foldr (fun s acc => comp PSU.n (ecT s) acc) (idc PSU.n) == PSU.gc g))

def psiG : ℕ := sumBelow 28 (fun i => sumBelow 27 (fun j => sumBelow 8 (fun k =>
  Nat.totient (repOrd.getD (tb (i * 216 + j * 8 + k) % 16) 0))))

theorem vG : PSU.valid = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem hConj : checkConj = true := by decide +kernel

theorem hReps : checkReps = true := by decide +kernel

theorem hProds : checkProds = true := by decide +kernel

theorem hPsiG : psiG = 23984 := by decide +kernel

theorem psu_ng : PSU.ng = 2 := rfl
theorem psu_s0 : PSU.s0 = 28 := rfl
theorem psu_s1 : PSU.s1 = 27 := rfl
theorem psu_s2 : PSU.s2 = 8 := rfl
theorem psu_n : PSU.n = 28 := rfl

theorem idx_lt {t : ℕ} (ht : t < 6048) : t / 216 < PSU.s0 ∧ t / 8 % 27 < PSU.s1 ∧ t % 8 < PSU.s2 := by
  rw [psu_s0, psu_s1, psu_s2]; omega

theorem code_eT {t : ℕ} (ht : t < 6048) : code (eT t) = ecT t := by
  obtain ⟨h1, h2, h3⟩ := idx_lt ht
  exact code_e3 vG h1 h2 h3

theorem eT_mem {t : ℕ} (ht : t < 6048) : eT t ∈ PSU.grp := by
  obtain ⟨h1, h2, h3⟩ := idx_lt ht
  exact e3_mem vG h1 h2 h3

theorem eT_zero : eT 0 = 1 := by
  rw [show eT 0 = PSU.U 0 0 * (PSU.U 1 0 * PSU.U 2 0) from rfl, U_zero vG (l := 0) (by norm_num),
    U_zero vG (l := 1) (by norm_num), U_zero vG (l := 2) (by norm_num), mul_one, mul_one]

/-- conjugacy certificate: `c * e = r * c` -/
theorem conj_cert {t : ℕ} (ht : t < 6048) :
    tb t / 16 < 6048 ∧ tb t % 16 < 14 ∧ reps.getD (tb t % 16) 0 < 6048 ∧
      eT (tb t / 16) * eT t = eT (reps.getD (tb t % 16) 0) * eT (tb t / 16) := by
  obtain ⟨h1, h2, h3⟩ := idx_lt ht
  simp only [psu_s0, psu_s1, psu_s2] at h1 h2 h3
  have h := allBelow_spec _ _ (allBelow_spec _ _ (allBelow_spec _ _ hConj _ h1) _ h2) _ h3
  have et : t / 216 * 216 + t / 8 % 27 * 8 + t % 8 = t := by omega
  rw [et] at h
  unfold ck2 at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨hc, hr⟩, he⟩ := h
  have hrr := allBelow_spec _ _ hReps _ hr
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hrr
  refine ⟨hc, hr, hrr.1.1, code_eq vG ?_⟩
  rw [code_mul (hn vG), code_mul (hn vG), code_eT hc, code_eT hrr.1.1]
  have : code (eT t) = PSU.ec3 (t / 216) (t / 8 % 27) (t % 8) := code_eT ht
  rw [this]
  exact he

theorem orderOf_eT {t : ℕ} (ht : t < 6048) : orderOf (eT t) = repOrd.getD (tb t % 16) 0 := by
  obtain ⟨hc, hr, hrr, he⟩ := conj_cert ht
  have e1 : eT t = (eT (tb t / 16))⁻¹ * eT (reps.getD (tb t % 16) 0) * eT (tb t / 16) := by
    rw [mul_assoc, ← he]; group
  rw [e1, orderOf_conj']
  have h := allBelow_spec _ _ hReps _ hr
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨_, h2⟩, h3⟩ := h
  have hne : ordc PSU.n (code (eT (reps.getD (tb t % 16) 0))) ≠ 0 := by
    rw [code_eT hrr, h2]; exact h3
  have := (ordc_spec (n := PSU.n) (hn vG) _ hne).1
  rw [this, code_eT hrr, h2]

theorem card_G : Fintype.card PSU.grp = 6048 := by
  rw [card_grp vG]; rfl

theorem psi_G : ∑ g : PSU.grp, Nat.totient (orderOf g) = 23984 := by
  have : ∑ g : PSU.grp, Nat.totient (orderOf g) =
      ∑ g : PSU.grp, (fun σ => Nat.totient (orderOf σ)) (g : Equiv.Perm (Fin PSU.n)) := by
    simp only [Subgroup.orderOf_coe]
  refine this.trans ((sum_grp vG (fun σ => Nat.totient (orderOf σ))).trans ?_)
  rw [← hPsiG]
  unfold psiG
  refine sumBelow_congr _ _ _ (fun i hi => sumBelow_congr _ _ _ (fun j hj => sumBelow_congr _ _ _ (fun k hk => ?_)))
  rw [dif_pos ⟨hi, hj, hk⟩]
  rw [psu_s0] at hi; rw [psu_s1] at hj; rw [psu_s2] at hk
  have ht : i * 216 + j * 8 + k < 6048 := by omega
  have hq : PSU.e3 i j k = eT (i * 216 + j * 8 + k) := by
    unfold eT; congr 1 <;> omega
  rw [hq, orderOf_eT ht]

/-- elements of `PSU.grp` -/
def eG {t : ℕ} (ht : t < 6048) : PSU.grp := ⟨eT t, eT_mem ht⟩

theorem simple_G : IsSimpleGroup PSU.grp := by
  have g0mem : PSU.genP 0 ∈ PSU.grp := Subgroup.subset_closure ⟨⟨0, by rw [psu_ng]; norm_num⟩, rfl⟩
  have g1mem : PSU.genP 1 ∈ PSU.grp := Subgroup.subset_closure ⟨⟨1, by rw [psu_ng]; norm_num⟩, rfl⟩
  haveI : Nontrivial PSU.grp := by
    refine ⟨⟨⟨PSU.genP 0, g0mem⟩, 1, fun h => ?_⟩⟩
    have h' : PSU.genP 0 = 1 := congrArg Subtype.val h
    have := congrArg code h'
    rw [code_genP vG (by rw [psu_ng]; norm_num), code_one (hn vG)] at this
    revert this; decide +kernel
  refine ⟨fun H hH => ?_⟩
  rcases Subgroup.bot_or_exists_ne_one H with hb | ⟨x, hxH, hx1⟩
  · exact Or.inl hb
  right
  -- write x as an enumerated element
  obtain ⟨xv, xmem⟩ := x
  obtain ⟨i, j, k, hi, hj, hk, rfl⟩ := closure_sub vG xmem
  rw [psu_s0] at hi; rw [psu_s1] at hj; rw [psu_s2] at hk
  set t := i * 216 + j * 8 + k with htdef
  have ht : t < 6048 := by omega
  have hq : PSU.e3 i j k = eT t := by unfold eT; congr 1 <;> omega
  -- membership of conjugates
  have conj_in : ∀ (c y : PSU.grp), y ∈ H → c⁻¹ * y * c ∈ H := fun c y hy => by
    have := hH.conj_mem y hy c⁻¹
    simpa using this
  obtain ⟨hc, hr, hrr, he⟩ := conj_cert ht
  set kk := tb t % 16 with hkk
  have hR : eG hrr ∈ H := by
    have e1 : eT (reps.getD kk 0) = eT (tb t / 16) * eT t * (eT (tb t / 16))⁻¹ := by
      rw [he]; group
    have : eG hrr = (eG hc)⁻¹⁻¹ * ⟨PSU.e3 i j k, xmem⟩ * (eG hc)⁻¹ := by
      apply Subtype.ext
      simp only [eG, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
      rw [hq, ← e1]
    rw [this]; exact conj_in _ _ hxH
  -- every element of the class `kk` lies in `H`
  have cls_in : ∀ s (hs : s < 6048), tb s % 16 = kk → eG hs ∈ H := by
    intro s hs hsk
    obtain ⟨hc', hr', hrr', he'⟩ := conj_cert hs
    have : eG hs = (eG hc')⁻¹ * eG hrr * eG hc' := by
      apply Subtype.ext
      simp only [eG, Subgroup.coe_mul, Subgroup.coe_inv]
      have hk' : reps.getD (tb s % 16) 0 = reps.getD kk 0 := by rw [hsk]
      rw [← hk']
      rw [mul_assoc, ← he']; group
    rw [this]; exact conj_in _ _ hR
  -- `kk ≠ 0`
  have hk0 : kk ≠ 0 := by
    intro h0
    apply hx1
    apply Subtype.ext
    have r0 : reps.getD kk 0 = 0 := by rw [h0]; rfl
    have e1 : eT t = (eT (tb t / 16))⁻¹ * eT (reps.getD kk 0) * eT (tb t / 16) := by
      rw [mul_assoc, ← he]; group
    show PSU.e3 i j k = 1
    rw [hq, e1, r0, eT_zero]; group
  -- generators lie in `H`
  have gen_in : ∀ g (hg : g < 2), (⟨PSU.genP g, Subgroup.subset_closure ⟨⟨g, by rw [psu_ng]; omega⟩, rfl⟩⟩ : PSU.grp) ∈ H := by
    intro g hg
    have hp := allBelow_spec _ _ hProds kk hr
    simp only [Bool.or_eq_true, decide_eq_true_eq, hk0, false_or] at hp
    have hp2 := allBelow_spec _ _ hp g hg
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hp2
    obtain ⟨hall, hprod⟩ := hp2
    generalize (prods.getD kk []).getD g [] = L at hall hprod
    -- product of the list
    have key : ∀ L : List ℕ, (∀ s ∈ L, s < 6048 ∧ tb s % 16 = kk) →
        ∃ y : PSU.grp, y ∈ H ∧ code y.1 = L.foldr (fun s acc => comp PSU.n (ecT s) acc) (idc PSU.n) := by
      intro L
      induction L with
      | nil => intro _; exact ⟨1, H.one_mem, code_one (hn vG)⟩
      | cons a L ih =>
        intro hL
        obtain ⟨y, hy, hyc⟩ := ih (fun s hs => hL s (by simp [hs]))
        have ha := hL a (by simp)
        refine ⟨eG ha.1 * y, H.mul_mem (cls_in a ha.1 ha.2) hy, ?_⟩
        simp only [Subgroup.coe_mul, eG, List.foldr_cons]
        rw [code_mul (hn vG), code_eT ha.1, hyc]
    obtain ⟨y, hy, hyc⟩ := key L hall
    have : y = ⟨PSU.genP g, Subgroup.subset_closure ⟨⟨g, by rw [psu_ng]; omega⟩, rfl⟩⟩ := by
      apply Subtype.ext
      apply code_eq vG
      show code y.1 = code (PSU.genP g)
      rw [hyc, hprod, code_genP vG (by rw [psu_ng]; omega)]
    rw [← this]; exact hy
  -- conclude
  rw [eq_top_iff]
  rintro ⟨z, hz⟩ -
  have hle : PSU.grp ≤ H.map PSU.grp.subtype := by
    unfold grp
    rw [Subgroup.closure_le]
    rintro _ ⟨⟨g, hg⟩, rfl⟩
    rw [psu_ng] at hg
    exact ⟨_, gen_in g hg, rfl⟩
  obtain ⟨w, hw, hwz⟩ := hle hz
  have : w = ⟨z, hz⟩ := Subtype.ext hwz
  rw [← this]; exact hw

/- The non-simple group `C₆ × S₄ × (C₇ ⋊ C₆)` -/

theorem vC6 : C6c.valid = true := by decide +kernel
theorem vS4 : S4c.valid = true := by decide +kernel
theorem vF : Fc.valid = true := by decide +kernel
theorem oC6 : C6c.checkOrd = true := by decide +kernel
theorem oS4 : S4c.checkOrd = true := by decide +kernel
theorem oF : Fc.checkOrd = true := by decide +kernel

abbrev HH : Type := C6c.grp × S4c.grp × Fc.grp

theorem card_H : Fintype.card HH = 6048 := by
  simp only [Fintype.card_prod, card_grp vC6, card_grp vS4, card_grp vF]
  rfl

def psiH : ℕ :=
  sumBelow C6c.s0 (fun i => sumBelow C6c.s1 (fun j => sumBelow C6c.s2 (fun k =>
  sumBelow S4c.s0 (fun i' => sumBelow S4c.s1 (fun j' => sumBelow S4c.s2 (fun k' =>
  sumBelow Fc.s0 (fun i'' => sumBelow Fc.s1 (fun j'' => sumBelow Fc.s2 (fun k'' =>
    Nat.totient ((ordc C6c.n (C6c.ec3 i j k)).lcm ((ordc S4c.n (S4c.ec3 i' j' k')).lcm
      (ordc Fc.n (Fc.ec3 i'' j'' k'')))))))))))))

theorem hPsiH : psiH = 23984 := by decide +kernel

theorem psi_H : ∑ h : HH, Nat.totient (orderOf h) = 23984 := by
  rw [← hPsiH]
  simp only [Fintype.sum_prod_type, Prod.orderOf]
  rw [sum_grp_ord vC6 oC6 (fun a => ∑ b : S4c.grp, ∑ c : Fc.grp,
    Nat.totient (a.lcm ((orderOf b).lcm (orderOf c))))]
  unfold psiH
  refine sumBelow_congr _ _ _ (fun i _ => sumBelow_congr _ _ _ (fun j _ => sumBelow_congr _ _ _ (fun k _ => ?_)))
  rw [sum_grp_ord vS4 oS4 (fun b => ∑ c : Fc.grp,
    Nat.totient ((ordc C6c.n (C6c.ec3 i j k)).lcm (b.lcm (orderOf c))))]
  refine sumBelow_congr _ _ _ (fun i' _ => sumBelow_congr _ _ _ (fun j' _ => sumBelow_congr _ _ _ (fun k' _ => ?_)))
  rw [sum_grp_ord vF oF (fun c =>
    Nat.totient ((ordc C6c.n (C6c.ec3 i j k)).lcm ((ordc S4c.n (S4c.ec3 i' j' k')).lcm c)))]

theorem not_simple_H : ¬ IsSimpleGroup HH := by
  intro hs
  have m0 : C6c.genP 0 ∈ C6c.grp := Subgroup.subset_closure ⟨⟨0, by decide⟩, rfl⟩
  have m1 : S4c.genP 0 ∈ S4c.grp := Subgroup.subset_closure ⟨⟨0, by decide⟩, rfl⟩
  have n0 : (⟨C6c.genP 0, m0⟩ : C6c.grp) ≠ 1 := fun h => by
    have := congrArg code (congrArg Subtype.val h)
    rw [Subgroup.coe_one, code_genP vC6 (by decide), code_one (hn vC6)] at this
    revert this; decide +kernel
  have n1 : (⟨S4c.genP 0, m1⟩ : S4c.grp) ≠ 1 := fun h => by
    have := congrArg code (congrArg Subtype.val h)
    rw [Subgroup.coe_one, code_genP vS4 (by decide), code_one (hn vS4)] at this
    revert this; decide +kernel
  let f : HH →* S4c.grp × Fc.grp := MonoidHom.snd _ _
  rcases (MonoidHom.normal_ker f).eq_bot_or_eq_top with h | h
  · have : ((⟨C6c.genP 0, m0⟩, 1) : HH) ∈ f.ker := by
      rw [MonoidHom.mem_ker]; rfl
    rw [h, Subgroup.mem_bot] at this
    exact n0 (congrArg Prod.fst this)
  · have : ((1, ⟨S4c.genP 0, m1⟩, 1) : HH) ∈ f.ker := by rw [h]; exact Subgroup.mem_top _
    rw [MonoidHom.mem_ker] at this
    exact n1 (congrArg Prod.fst this)

end OMA1925

theorem OMA.solution : type_of% @Kourovka.«19.25».kourovka_19_25 := by
  intro h
  have := @h OMA1925.PSU.grp OMA1925.HH _ _ _ _ (OMA1925.card_G.trans OMA1925.card_H.symm)
    (OMA1925.psi_G.trans OMA1925.psi_H.symm) OMA1925.simple_G
  exact OMA1925.not_simple_H this
