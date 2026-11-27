import FormalConjectures.WrittenOnTheWallII.GraphConjecture72

/-! A finite verification of Gebendorfer's graph G(2,24), recorded in
DeLaViña's Written on the Wall II catalogue under conjecture 72.
The 24-vertex clique replaces the left endpoint of a five-vertex path.
Three independent vertices are adjacent to its three internal vertices.
The eccentricity sum is at least 114, local independence is at least four,
and no induced tree has more than five vertices. Thus the expression
inside the ceiling is at least 466/93, strictly greater than five. -/

open SimpleGraph
namespace WOW72Witness

private abbrev V := Fin 31

-- The seven ordinary vertices are the four path vertices and three independent
-- common neighbours. Vertices 7 through 30 form the terminal clique.
private def forward (a b : V) : Prop :=
  (a.val < 3 ∧ b.val = a.val + 1) ∨
  (a.val ≤ 2 ∧ 4 ≤ b.val ∧ b.val ≤ 6) ∨
  (a = 0 ∧ 7 ≤ b.val) ∨ (7 ≤ a.val ∧ a < b)

private def G : SimpleGraph V where
  Adj a b := forward a b ∨ forward b a
  symm := ⟨fun _ _ => Or.symm⟩
  loopless := ⟨by unfold forward; decide⟩

private instance : DecidableRel G.Adj := fun a b => by
  change Decidable (forward a b ∨ forward b a)
  unfold forward
  infer_instance

private theorem conn : G.Connected := by
  apply (connected_iff_exists_forall_reachable _).2
  refine ⟨0, fun v => ?_⟩
  have h1 := (show G.Adj 0 1 by decide).reachable
  have h2 := h1.trans (show G.Adj 1 2 by decide).reachable
  have h3 := h2.trans (show G.Adj 2 3 by decide).reachable
  have h : ∀ w : V, w = 0 ∨ w = 2 ∨ w = 3 ∨ G.Adj 0 w := by decide
  rcases h v with rfl | rfl | rfl | ha
  · exact .rfl
  · exact h2
  · exact h3
  · exact ha.reachable

-- Moving along an edge changes the layer by at most one.
private def layer (v : V) : ℕ :=
  if v.val < 4 then v.val + 1 else if v.val < 7 then 2 else 0

private theorem layer_step : ∀ a b : V, G.Adj a b → layer a ≤ layer b + 1 := by decide

private theorem layer_walk {a b : V} (p : G.Walk a b) : layer a ≤ layer b + p.length := by
  induction p with
  | nil => simp
  | cons hab p ih =>
    have h := layer_step _ _ hab
    simp only [Walk.length_cons]
    omega

private theorem ecc_lower (v : V) :
    max (layer v) (4 - layer v) ≤ (G.eccent v).toNat := by
  have hd (a b : V) : layer a ≤ layer b + G.dist a b := by
    obtain ⟨p,hp⟩ := conn.exists_walk_length_eq_dist a b
    simpa [hp] using layer_walk p
  have he (w : V) : G.dist v w ≤ (G.eccent v).toNat := by
    have h := G.edist_le_eccent (u := v) (v := w)
    rw [← (conn.preconnected v w).coe_dist_eq_edist, G.eccent_eq_computable conn v] at h
    rw [G.eccent_eq_computable conn v]
    exact_mod_cast h
  have hl := hd v 7
  have hr := hd 3 v
  have h7 := he 7
  have h3 := he 3
  rw [G.dist_comm (u := 3) (v := v)] at hr
  have : layer 7 = 0 := rfl
  have : layer 3 = 4 := rfl
  apply max_le <;> omega

private theorem ecc_sum : (114 : ℝ) / 31 ≤ G.averageEccentricity := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset V)) (fun i _ => ecc_lower i)
  have hn : (∑ i : V, max (layer i) (4 - layer i)) = 114 := by decide
  rw [hn] at h
  unfold averageEccentricity
  simp only [Fintype.card_fin, Nat.cast_ofNat]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact_mod_cast h

private theorem local_four : 4 ≤ G.indepNeighborsCard 0 := by
  let a : G.neighborSet 0 := ⟨4, by decide⟩
  let b : G.neighborSet 0 := ⟨5, by decide⟩
  let c : G.neighborSet 0 := ⟨6, by decide⟩
  let d : G.neighborSet 0 := ⟨7, by decide⟩
  let s : Finset (G.neighborSet 0) := {a,b,c,d}
  have hn : s.card = 4 := by decide
  have hi : (G.induce (G.neighborSet 0)).IsIndepSet (s : Set _) := by
    intro x hx y hy hxy
    simp only [s, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl|rfl|rfl|rfl <;> rcases hy with rfl|rfl|rfl|rfl <;>
      first | exact (hxy rfl).elim | change ¬ G.Adj _ _; decide
  exact hn ▸ hi.card_le_indepNum

private theorem no_triangle {A : Type*} {H : SimpleGraph A} (ht : H.IsAcyclic)
    {a b c : A} (hab : H.Adj a b) (hbc : H.Adj b c) (hca : H.Adj c a) : False := by
  let p : H.Walk a c := .cons hab (.cons hbc .nil)
  let q : H.Walk a c := .cons hca.symm .nil
  have hp : p.IsPath := by simp [p, Walk.isPath_def, hab.ne, hbc.ne, hca.ne.symm]
  have hq : q.IsPath := by simp [q, Walk.isPath_def, hca.ne.symm]
  have hh := congrArg (fun t : H.Path a c => t.val.length)
    ((ht.subsingleton_path a c).elim ⟨p,hp⟩ ⟨q,hq⟩)
  simp [p,q] at hh

private theorem no_square {A : Type*} {H : SimpleGraph A} (ht : H.IsAcyclic)
    {a b c d : A} (hac : a ≠ c) (hbd : b ≠ d)
    (hab : H.Adj a b) (hbc : H.Adj b c) (had : H.Adj a d) (hdc : H.Adj d c) : False := by
  let p : H.Walk a c := .cons hab (.cons hbc .nil)
  let q : H.Walk a c := .cons had (.cons hdc .nil)
  have hp : p.IsPath := by simp [p, Walk.isPath_def, hab.ne, hbc.ne, hac]
  have hq : q.IsPath := by simp [q, Walk.isPath_def, had.ne, hdc.ne, hac]
  have hh := congrArg (fun t : H.Path a c => t.val.snd)
    ((ht.subsingleton_path a c).elim ⟨p,hp⟩ ⟨q,hq⟩)
  exact hbd hh

-- A tree of order at least three cannot contain a pair of adjacent vertices
-- with identical neighbours outside the pair: the first edge leaving the
-- pair would complete a triangle.
private theorem twin_exclusion {A : Type*} [Fintype A] [DecidableEq A]
    {H : SimpleGraph A} (ht : H.IsTree) (hn : 2 < Fintype.card A)
    {a b : A} (hab : H.Adj a b)
    (he : ∀ z, z ≠ a → z ≠ b → (H.Adj a z ↔ H.Adj b z)) : False := by
  let pair : Finset A := {a,b}
  have hk : pair.card < (Finset.univ : Finset A).card := by
    have hle : pair.card ≤ 2 := Finset.card_le_two
    simpa using hle.trans_lt hn
  obtain ⟨z, -, hz⟩ := Finset.exists_mem_notMem_of_card_lt_card hk
  obtain ⟨p⟩ := ht.connected.preconnected a z
  obtain ⟨d, -, hu, hv⟩ := p.exists_boundary_dart (pair : Set A) (by simp [pair]) hz
  simp only [pair, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hu hv
  have h := he d.snd (fun hh => hv (Or.inl hh)) (fun hh => hv (Or.inr hh))
  have hadj := d.adj
  rcases hu with hu|hu <;> rw [hu] at hadj
  · exact no_triangle ht.isAcyclic hab (h.mp hadj) hadj.symm
  · exact no_triangle ht.isAcyclic hab hadj (h.mpr hadj).symm

private def label (v : V) : Fin 8 := ⟨min v.val 7, by omega⟩

set_option maxHeartbeats 2000000 in
private lemma one_clique_vertex (s : Finset V) (ht : (G.induce (s : Set V)).IsTree)
    (hn : 2 < s.card) {a b : V} (ha : a ∈ s) (hb : b ∈ s)
    (haq : 7 ≤ a.val) (hbq : 7 ≤ b.val) : a = b := by
  by_contra hab
  let x : (s : Set V) := ⟨a,ha⟩
  let y : (s : Set V) := ⟨b,hb⟩
  have adj : (G.induce (s : Set V)).Adj x y := by
    change forward a b ∨ forward b a
    unfold forward
    rcases lt_or_gt_of_ne hab with h|h
    · exact Or.inl (Or.inr (Or.inr (Or.inr ⟨haq,h⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hbq,h⟩)))
  apply twin_exclusion ht (by simpa using hn) adj
  intro z hzx hzy
  have hx : z.val ≠ a := fun h => hzx (Subtype.ext h)
  have hy : z.val ≠ b := fun h => hzy (Subtype.ext h)
  have twins : ∀ i j k : V, 7 ≤ i.val → 7 ≤ j.val → k ≠ i → k ≠ j →
      (G.Adj i k ↔ G.Adj j k) := by
    decide
  exact twins a b z.val haq hbq hx hy

-- After identifying the clique with vertex 7, only eight labels remain.
-- The two end vertices require their neighbours, and each displayed triple
-- or quadruple forms a cycle.
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 4096 in
private lemma small_bound : ∀ t ∈ (Finset.univ : Finset (Fin 8)).powerset,
    (3 ∈ t → 2 ∈ t) → (7 ∈ t → 0 ∈ t) →
    (∀ i ∈ ({4,5,6} : Finset (Fin 8)), i ∈ t → 0 ∈ t → 1 ∈ t → False) →
    (∀ i ∈ ({4,5,6} : Finset (Fin 8)), i ∈ t → 1 ∈ t → 2 ∈ t → False) →
    (∀ i ∈ ({4,5,6} : Finset (Fin 8)), ∀ j ∈ ({4,5,6} : Finset (Fin 8)),
      i ≠ j → i ∈ t → j ∈ t → 0 ∈ t → 2 ∈ t → False) →
    t.card ≤ 5 := by
  intro t _ h3 h7 h01 h12 h02
  have check : ∀ u ∈ (Finset.univ : Finset (Fin 8)).powerset,
      (3 ∈ u → 2 ∈ u) → (7 ∈ u → 0 ∈ u) →
      ¬ (0 ∈ u ∧ 1 ∈ u ∧ 4 ∈ u) →
      ¬ (0 ∈ u ∧ 1 ∈ u ∧ 5 ∈ u) →
      ¬ (0 ∈ u ∧ 1 ∈ u ∧ 6 ∈ u) →
      ¬ (1 ∈ u ∧ 2 ∈ u ∧ 4 ∈ u) →
      ¬ (1 ∈ u ∧ 2 ∈ u ∧ 5 ∈ u) →
      ¬ (1 ∈ u ∧ 2 ∈ u ∧ 6 ∈ u) →
      ¬ (0 ∈ u ∧ 2 ∈ u ∧ 4 ∈ u ∧ 5 ∈ u) →
      ¬ (0 ∈ u ∧ 2 ∈ u ∧ 4 ∈ u ∧ 6 ∈ u) →
      ¬ (0 ∈ u ∧ 2 ∈ u ∧ 5 ∈ u ∧ 6 ∈ u) →
      u.card ≤ 5 := by decide
  apply check t (Finset.mem_powerset.mpr (Finset.subset_univ _)) h3 h7
  · rintro ⟨ha,hb,hc⟩; exact h01 4 (by decide) hc ha hb
  · rintro ⟨ha,hb,hc⟩; exact h01 5 (by decide) hc ha hb
  · rintro ⟨ha,hb,hc⟩; exact h01 6 (by decide) hc ha hb
  · rintro ⟨ha,hb,hc⟩; exact h12 4 (by decide) hc ha hb
  · rintro ⟨ha,hb,hc⟩; exact h12 5 (by decide) hc ha hb
  · rintro ⟨ha,hb,hc⟩; exact h12 6 (by decide) hc ha hb
  · rintro ⟨ha,hb,hi,hj⟩; exact h02 4 (by decide) 5 (by decide) (by decide) hi hj ha hb
  · rintro ⟨ha,hb,hi,hj⟩; exact h02 4 (by decide) 6 (by decide) (by decide) hi hj ha hb
  · rintro ⟨ha,hb,hi,hj⟩; exact h02 5 (by decide) 6 (by decide) (by decide) hi hj ha hb


private def core (i : Fin 8) : V := ⟨i.val, by omega⟩

private lemma bound_tree (s : Finset V) (ht : (G.induce (s : Set V)).IsTree) :
    s.card ≤ 5 := by
  by_contra! hn
  have hlarge : 2 < s.card := by omega
  let : Nontrivial (s : Set V) := Fintype.one_lt_card_iff_nontrivial.mp (by simpa using (show 1 < s.card by omega))
  let t := s.image label
  have hinj : Set.InjOn label (s : Set V) := by
    intro a ha b hb he
    have he' := congrArg Fin.val he
    change min a.val 7 = min b.val 7 at he'
    by_cases h : a.val < 7
    · apply Fin.ext; omega
    · apply one_clique_vertex s ht hlarge ha hb <;> omega
  have hcard : t.card = s.card := Finset.card_image_of_injOn hinj
  have mem (i : Fin 8) (hi : i.val < 7) : i ∈ t ↔ core i ∈ s := by
    constructor
    · intro h
      obtain ⟨w,hw,hwi⟩ := Finset.mem_image.mp h
      have hh := congrArg Fin.val hwi
      change min w.val 7 = i.val at hh
      have : w = core i := Fin.ext (by change w.val = i.val; omega)
      exact this ▸ hw
    · intro h
      exact Finset.mem_image.mpr ⟨core i,h,Fin.ext (by change min i.val 7 = i.val; omega)⟩
  have leaf3 (h : (3 : Fin 8) ∈ t) : (2 : Fin 8) ∈ t := by
    have h3 := (mem 3 (by decide)).mp h
    obtain ⟨u,hu⟩ := ht.connected.preconnected.exists_adj_of_nontrivial ⟨core 3,h3⟩
    have check : ∀ w : V, G.Adj 3 w → w = 2 := by decide
    have he := check u.val hu
    exact (mem 2 (by decide)).mpr (show (2 : V) ∈ s from he ▸ u.prop)
  have leaf7 (h : (7 : Fin 8) ∈ t) : (0 : Fin 8) ∈ t := by
    obtain ⟨w,hw,he⟩ := Finset.mem_image.mp h
    have hval := congrArg Fin.val he
    change min w.val 7 = 7 at hval
    have hwq : 7 ≤ w.val := by omega
    obtain ⟨u,hu⟩ := ht.connected.preconnected.exists_adj_of_nontrivial ⟨w,hw⟩
    have check : ∀ a b : V, 7 ≤ a.val → G.Adj a b → b = 0 ∨ 7 ≤ b.val := by decide
    rcases check w u.val hwq hu with hz|hq
    · exact (mem 0 (by decide)).mpr (show (0 : V) ∈ s from hz ▸ u.prop)
    · exact (hu.ne (Subtype.ext (one_clique_vertex s ht hlarge hw u.prop hwq hq))).elim
  let leaves : Finset (Fin 8) := {4,5,6}
  have lt7 : ∀ i ∈ leaves, i.val < 7 := by decide
  have edges : ∀ i ∈ leaves, G.Adj 0 (core i) ∧ G.Adj 1 (core i) ∧ G.Adj 2 (core i) := by decide
  have tri {a b c : V} (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s)
      (h1 : G.Adj a b) (h2 : G.Adj b c) (h3 : G.Adj c a) : False :=
    no_triangle ht.isAcyclic (a := ⟨a,ha⟩) (b := ⟨b,hb⟩) (c := ⟨c,hc⟩) h1 h2 h3
  have h := small_bound t (Finset.mem_powerset.mpr (Finset.subset_univ _)) leaf3 leaf7 (by
    intro i hi h h0 h1
    exact tri ((mem 0 (by decide)).mp h0) ((mem 1 (by decide)).mp h1) ((mem i (lt7 i hi)).mp h)
      (by decide) (edges i hi).2.1 (edges i hi).1.symm) (by
    intro i hi h h1 h2
    exact tri ((mem 1 (by decide)).mp h1) ((mem 2 (by decide)).mp h2) ((mem i (lt7 i hi)).mp h)
      (by decide) (edges i hi).2.2 (edges i hi).2.1.symm) (by
    intro i hi j hj hij hI hJ h0 h2
    exact no_square ht.isAcyclic
      (a := ⟨core 0,(mem 0 (by decide)).mp h0⟩)
      (b := ⟨core i,(mem i (lt7 i hi)).mp hI⟩)
      (c := ⟨core 2,(mem 2 (by decide)).mp h2⟩)
      (d := ⟨core j,(mem j (lt7 j hj)).mp hJ⟩)
      (by intro he; exact (by decide : core 0 ≠ core 2) (congrArg Subtype.val he))
      (fun he => hij (Fin.ext (congrArg (fun x : (s : Set V) => x.val.val) he)))
      (edges i hi).1 (edges i hi).2.2.symm (edges j hj).1 (edges j hj).2.2.symm)
  omega

private theorem tree_upper : G.largestInducedTreeSize ≤ 5 := by
  unfold largestInducedTreeSize
  apply csSup_le'
  rintro n ⟨s,rfl,ht⟩
  exact bound_tree s ht

-- Transport lemmas adapted from the repository proofs for WOWII 84 and 133.
section transfer

variable {V W : Type*} {G : SimpleGraph V} {K : SimpleGraph W}

private lemma edist_hom_le (f : G →g K) (u v : V) : K.edist (f u) (f v) ≤ G.edist u v := by
  by_cases h : G.Reachable u v
  · obtain ⟨p, hp⟩ := h.exists_walk_length_eq_edist
    rw [← hp]
    calc K.edist (f u) (f v) ≤ ((p.map f).length : ℕ∞) := SimpleGraph.edist_le _
      _ = (p.length : ℕ∞) := by simp
  · rw [edist_eq_top_of_not_reachable h]
    exact le_top

private lemma edist_iso (e : G ≃g K) (u v : V) : K.edist (e u) (e v) = G.edist u v := by
  apply le_antisymm (edist_hom_le e.toHom u v)
  have := edist_hom_le e.symm.toHom (e u) (e v)
  simpa using this

private lemma eccent_iso (e : G ≃g K) (u : V) : K.eccent (e u) = G.eccent u := by
  rw [eccent_def, eccent_def]
  simp only
  rw [← e.surjective.iSup_comp]
  simp only [edist_iso]

private lemma tree_iso_le [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] (e : G ≃g K) :
    largestInducedTreeSize K ≤ largestInducedTreeSize G := by
  unfold largestInducedTreeSize
  apply csSup_le'
  rintro n ⟨t, rfl, ht⟩
  let s : Finset V := t.map e.symm.toEquiv.toEmbedding
  have hbij : Set.BijOn e (s : Set V) (t : Set W) := by
    refine ⟨?_, e.injective.injOn, ?_⟩
    · intro x hx
      simp only [s, Finset.coe_map, Set.mem_image, Finset.mem_coe] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      simpa using hy
    · intro y hy
      refine ⟨e.symm y, ?_, by simp⟩
      simp only [s, Finset.coe_map, Set.mem_image, Finset.mem_coe]
      exact ⟨y, hy, rfl⟩
  have hs : (G.induce (s : Set V)).IsTree := (Iso.induce e hbij).isTree_iff.mpr ht
  have hcard : s.card = t.card := by simp [s]
  have := card_le_largestInducedTreeSize hs
  unfold largestInducedTreeSize at this
  omega

private lemma avg_iso [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] (e : G ≃g K) :
    K.averageEccentricity = G.averageEccentricity := by
  unfold averageEccentricity
  rw [Fintype.card_congr e.toEquiv]
  congr 1
  rw [← e.toEquiv.sum_comp]
  simp [eccent_iso]

end transfer
section neighbours
variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
  {G : SimpleGraph V} {G' : SimpleGraph W}
omit [DecidableEq V] in
private lemma card_le_indepNeighborsCard (G : SimpleGraph V) (u : V) (S : Finset V)
    (hS : ∀ x ∈ S, G.Adj u x) (hI : G.IsIndepSet (S : Set V)) :
    S.card ≤ indepNeighborsCard G u := by
  classical
  unfold indepNeighborsCard
  let T : Finset (G.neighborSet u) := S.subtype (fun x => x ∈ G.neighborSet u)
  have hT : T.card = S.card := by
    rw [Finset.card_subtype]
    congr 1
    exact Finset.filter_true_of_mem (fun x hx => hS x hx)
  rw [← hT]
  apply IsIndepSet.card_le_indepNum
  intro a ha b hb hab
  rw [Finset.mem_coe, Finset.mem_subtype] at ha hb
  simp only [comap_adj, Function.Embedding.subtype_apply]
  exact hI ha hb (fun h => hab (Subtype.ext h))

omit [Fintype V] [DecidableEq V] in
private lemma exists_indepNeighbors (G : SimpleGraph V) (u : V) :
    ∃ S : Finset V, (∀ x ∈ S, G.Adj u x) ∧ G.IsIndepSet (S : Set V) ∧
      S.card = indepNeighborsCard G u := by
  classical
  obtain ⟨s, hs⟩ := (G.induce (G.neighborSet u)).exists_isNIndepSet_indepNum
  refine ⟨s.map (Function.Embedding.subtype _), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, -, rfl⟩ := Finset.mem_map.mp hx
    exact y.2
  · intro a ha b hb hab
    obtain ⟨a', ha', rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := Finset.mem_map.mp hb
    have := hs.isIndepSet ha' hb' (fun h => hab (by rw [h]))
    simpa [comap_adj] using this
  · rw [Finset.card_map, hs.card_eq]
    rfl

omit [Fintype V] [DecidableEq V] [DecidableEq W] in
private lemma indepNeighborsCard_le_iso (φ : G ≃g G') (u : V) :
    indepNeighborsCard G u ≤ indepNeighborsCard G' (φ u) := by
  obtain ⟨S, hS, hI, hc⟩ := exists_indepNeighbors G u
  rw [← hc, ← Finset.card_map φ.toEquiv.toEmbedding]
  apply card_le_indepNeighborsCard
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    simpa [φ.map_adj_iff] using hS y hy
  · intro a ha b hb hab
    obtain ⟨a', ha', rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := Finset.mem_map.mp hb
    have := hI ha' hb' (fun h => hab (by rw [h]))
    simpa [φ.map_adj_iff] using this

end neighbours

end WOW72Witness

open WOW72Witness in
theorem OMA.disproof : ¬ (type_of% @WrittenOnTheWallII.GraphConjecture72.conjecture72) := by
  intro hall
  let e : V ≃ ULift V := Equiv.ulift.symm
  let K := G.map e.toEmbedding
  let φ : G ≃g K := SimpleGraph.Iso.map e G
  have bad := hall K (φ.connected_iff.mp conn)
  let t := Finset.univ.image (fun v => K.indepNeighborsCard v)
  have hm : K.indepNeighborsCard (φ 0) ≤ t.max' (by simp [t]) :=
    Finset.le_max' _ _ (Finset.mem_image.mpr ⟨φ 0,Finset.mem_univ _,rfl⟩)
  have hl : (4 : ℝ) ≤ (t.max' (by simp [t]) : ℝ) := by exact_mod_cast (local_four.trans (indepNeighborsCard_le_iso φ 0)).trans hm
  have ha := ecc_sum
  rw [← avg_iso φ] at ha
  have hh : K.averageEccentricity + (t.max' (by simp [t]) : ℝ) / 3 ≤
      (⌈K.averageEccentricity + (t.max' (by simp [t]) : ℝ) / 3⌉ : ℝ) := Int.le_ceil _
  have hf : (K.largestInducedTreeSize : ℝ) ≤ 5 := by exact_mod_cast (tree_iso_le φ).trans tree_upper
  change (⌈K.averageEccentricity + (t.max' _ : ℝ) / 3⌉ : ℝ) ≤ _ at bad
  linarith
