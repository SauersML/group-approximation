import GroupApproximation.Manuscript.NonMF.Full.GL06f.Reduction
import GroupApproximation.Manuscript.NonMF.Full.GL03C.PocketListing

/-!
# The fourth junction: the kept darts close up

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  This is infrastructure for `thm:hull` in `non_mf_groups_exist.tex`
(around line 2121).

`junction_listing_of_filter` (module `PocketListing`) lists the kept darts of a pocket boundary as
`s₁ t₁'⁻¹ s₂ t₂'` with three junctions.  This module supplies the fourth junction, from the end of
`t₂'` back to the start of `s₁`, for the kept darts of a region move
(`GL05b.movePred`, `GL06f.flipFaces`).  So the listing is a closed dart walk, which is the
closed-walk clause of `GL06f.RoseRegionMoveSubArcStatement`.

* `chain_countP`: in a walk, counting darts that start at `x`, plus one if the last dart ends
  at `x`, gives the count of darts that end at `x`, plus one if the first dart starts at `x`.
* `boundary_countP_balanced`: the boundary darts of a face set start at a vertex as often as they
  end there.  The boundary successor `FaceSetCircuits.boundaryPerm` matches the two kinds.
* `filter_movePred_countP_balanced`: the same for the kept darts, since they are the boundary
  darts of `flipFaces` (`GL06f.isBoundaryDart_flipFaces_iff`).
* `isClosedDartWalk_of_perm_filter`: a walk re-listing the kept darts closes up.
* `closedWalk_listing_of_filter`: the pocket version, with `s₁`, `s₂` of length at most `ε`.

The proofs are written here: the foreign rose modules were read only for the proof pattern.
-/

namespace GroupApproximation.Full.GL03C

universe u w v

open GroupApproximation.GGT
open GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.Surgery.MapCollapse
open GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides

section Counting

variable {α V : Type*} {s t : α → V}

/-- Counting along a nonempty walk given as `a :: l`: see `chain_countP`. -/
theorem chain_countP_cons [DecidableEq V] (x : V) :
    ∀ (a : α) (l : List α), (a :: l).IsChain (fun a b => t a = s b) →
      (a :: l).countP (fun d => decide (s d = x)) +
          [(a :: l).getLast (List.cons_ne_nil a l)].countP (fun d => decide (t d = x)) =
        (a :: l).countP (fun d => decide (t d = x)) +
          [a].countP (fun d => decide (s d = x)) := by
  intro a l
  induction l generalizing a with
  | nil => intro _; exact Nat.add_comm _ _
  | cons b l ih =>
    intro hchain
    have hab : t a = s b := (List.isChain_cons_cons.mp hchain).1
    have hih := ih b (List.isChain_cons_cons.mp hchain).2
    have hlast : (a :: b :: l).getLast (List.cons_ne_nil a (b :: l)) =
        (b :: l).getLast (List.cons_ne_nil b l) := rfl
    have e1 : (a :: b :: l).countP (fun d => decide (s d = x)) =
        [a].countP (fun d => decide (s d = x)) +
          (b :: l).countP (fun d => decide (s d = x)) :=
      List.countP_append (l₁ := [a]) (l₂ := b :: l)
    have e2 : (a :: b :: l).countP (fun d => decide (t d = x)) =
        [a].countP (fun d => decide (t d = x)) +
          (b :: l).countP (fun d => decide (t d = x)) :=
      List.countP_append (l₁ := [a]) (l₂ := b :: l)
    have hab' : [a].countP (fun d => decide (t d = x)) =
        [b].countP (fun d => decide (s d = x)) := by
      simp only [List.countP_singleton, hab]
    rw [e1, e2, hlast]
    omega

/-- **Counting along a walk** (Osin 9.7(b), infrastructure for `thm:hull`,
`non_mf_groups_exist.tex`).  If every `a` in `l` ends where the next begins (`t a = s b`), then
the darts starting at `x`, plus one if the last dart ends at `x`, are as many as the darts ending
at `x`, plus one if the first dart starts at `x`. -/
theorem chain_countP [DecidableEq V] (x : V) {l : List α} (hne : l ≠ [])
    (hl : l.IsChain (fun a b => t a = s b)) :
    l.countP (fun d => decide (s d = x)) +
        [l.getLast hne].countP (fun d => decide (t d = x)) =
      l.countP (fun d => decide (t d = x)) + [l.head hne].countP (fun d => decide (s d = x)) := by
  obtain ⟨a, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  exact chain_countP_cons (s := s) (t := t) x a rest hl

end Counting

/-- **The boundary darts of a face set are balanced at every vertex** (Osin 9.7(b),
infrastructure for `thm:hull`, `non_mf_groups_exist.tex`).  A duplicate-free list of exactly the
boundary darts of `F` has as many darts starting at `x` as darts ending at `x`: the boundary
successor `FaceSetCircuits.boundaryPerm` starts where its argument ends. -/
theorem boundary_countP_balanced (M : CombMap.{v}) [DecidableEq M.Vertex] (F : Finset M.Face)
    (c : List M.Dart) (hnodup : c.Nodup)
    (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M F d)
    (x : M.Vertex) :
    c.countP (fun d => decide (M.vertexOf d = x)) =
      c.countP (fun d => decide (M.vertexOf (M.alpha d) = x)) := by
  classical
  rw [List.countP_eq_length_filter, List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup (hnodup.filter _),
    ← List.toFinset_card_of_nodup (hnodup.filter _)]
  symm
  refine Finset.card_bij
    (fun d hd => (FaceSetCircuits.boundaryPerm M F
      ⟨d, (hc d).mp (List.mem_filter.mp (List.mem_toFinset.mp hd)).1⟩).1) ?_ ?_ ?_
  · intro a ha
    have ha' := List.mem_filter.mp (List.mem_toFinset.mp ha)
    have hb := FaceSetCircuits.boundaryPerm_walk M F ⟨a, (hc a).mp ha'.1⟩
    refine List.mem_toFinset.mpr (List.mem_filter.mpr
      ⟨(hc _).mpr (FaceSetCircuits.boundaryPerm M F ⟨a, (hc a).mp ha'.1⟩).2, ?_⟩)
    exact decide_eq_true
      ((vertexOf_eq_of_boundaryWalk hb).trans (of_decide_eq_true ha'.2))
  · intro a₁ _ a₂ _ h
    have h' := (FaceSetCircuits.boundaryPerm M F).injective (Subtype.ext h)
    exact congrArg Subtype.val h'
  · intro b hb
    have hb' := List.mem_filter.mp (List.mem_toFinset.mp hb)
    have hbd : Surgery.MapCollapse.IsBoundaryDart M F b := (hc b).mp hb'.1
    have hwalk := vertexOf_eq_of_boundaryWalk
      (FaceSetCircuits.boundaryPerm_walk M F
        ((FaceSetCircuits.boundaryPerm M F).symm ⟨b, hbd⟩))
    rw [Equiv.apply_symm_apply] at hwalk
    refine ⟨((FaceSetCircuits.boundaryPerm M F).symm ⟨b, hbd⟩).1,
      List.mem_toFinset.mpr (List.mem_filter.mpr
        ⟨(hc _).mpr ((FaceSetCircuits.boundaryPerm M F).symm ⟨b, hbd⟩).2,
          decide_eq_true (hwalk.symm.trans (of_decide_eq_true hb'.2))⟩), ?_⟩
    exact congrArg Subtype.val
      (Equiv.apply_symm_apply (FaceSetCircuits.boundaryPerm M F) ⟨b, hbd⟩)

/-- **The kept darts of a region move are balanced at every vertex** (Osin 9.7(b),
infrastructure for `thm:hull`, `non_mf_groups_exist.tex`).  They are the boundary darts of the
moved face set `GL06f.flipFaces faces z`. -/
theorem filter_movePred_countP_balanced {M : CombMap.{v}} [DecidableEq M.Vertex]
    {faces : Finset M.Face} {c : List M.Dart} (hnodup : c.Nodup)
    (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M faces d) {z : M.Dart → Bool}
    (hz : ∀ x y, CombMap.FaceClassStep M (walkKeep M c) x y → z x = z y)
    (hind : ∀ d ∈ c, z d = false ∨ z (M.alpha d) = false) (x : M.Vertex) :
    (c.filter (GL05b.movePred M z)).countP (fun d => decide (M.vertexOf d = x)) =
      (c.filter (GL05b.movePred M z)).countP
        (fun d => decide (M.vertexOf (M.alpha d) = x)) :=
  boundary_countP_balanced M (GL06f.flipFaces M faces z) (c.filter (GL05b.movePred M z))
    (hnodup.filter _)
    (fun d => List.mem_filter.trans (GL06f.isBoundaryDart_flipFaces_iff hc hz hind d).symm) x

/-- **The fourth junction** (Osin 9.7(b), infrastructure for `thm:hull`,
`non_mf_groups_exist.tex`).  A nonempty walk `L` that re-lists the kept darts of a region move
closes up: its last dart ends where its first dart starts.  The kept darts start at the vertex of
the first dart as often as they end there, and a walk that does not close up would start there
once more than it ends there. -/
theorem isClosedDartWalk_of_perm_filter {M : CombMap.{v}} {faces : Finset M.Face}
    {c : List M.Dart} (hnodup : c.Nodup)
    (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M faces d)
    {z : M.Dart → Bool}
    (hz : ∀ x y, CombMap.FaceClassStep M (walkKeep M c) x y → z x = z y)
    (hind : ∀ d ∈ c, z d = false ∨ z (M.alpha d) = false) {L : List M.Dart}
    (hperm : L.Perm (c.filter (GL05b.movePred M z))) (hne : L ≠ [])
    (hchain : L.IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e) :
    IsClosedDartWalk M L := by
  classical
  refine ⟨hne, hchain, ?_⟩
  have hbal := filter_movePred_countP_balanced hnodup hc hz hind (M.vertexOf (L.head hne))
  have hbal' : L.countP (fun d => decide (M.vertexOf d = M.vertexOf (L.head hne))) =
      L.countP (fun d => decide (M.vertexOf (M.alpha d) = M.vertexOf (L.head hne))) :=
    (hperm.countP_eq (fun d => decide (M.vertexOf d = M.vertexOf (L.head hne)))).trans
      (hbal.trans
        (hperm.countP_eq
          (fun d => decide (M.vertexOf (M.alpha d) = M.vertexOf (L.head hne)))).symm)
  have hcount : L.countP (fun d => decide (M.vertexOf d = M.vertexOf (L.head hne))) +
        [L.getLast hne].countP
          (fun d => decide (M.vertexOf (M.alpha d) = M.vertexOf (L.head hne))) =
      L.countP (fun d => decide (M.vertexOf (M.alpha d) = M.vertexOf (L.head hne))) +
        [L.head hne].countP (fun d => decide (M.vertexOf d = M.vertexOf (L.head hne))) :=
    chain_countP (s := M.vertexOf) (t := fun d => M.vertexOf (M.alpha d))
      (M.vertexOf (L.head hne)) hne hchain
  have hhead : [L.head hne].countP
      (fun d => decide (M.vertexOf d = M.vertexOf (L.head hne))) = 1 := by
    simp
  by_contra hlast
  have h0 : [L.getLast hne].countP
      (fun d => decide (M.vertexOf (M.alpha d) = M.vertexOf (L.head hne))) = 0 := by
    simp [hlast]
  omega

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (GGT.RelLetter G Lambda))}

/-- **The kept darts of a pocket boundary as a closed walk `s₁ t₁'⁻¹ s₂ t₂'`** (Osin 9.7(b),
infrastructure for `thm:hull`, `non_mf_groups_exist.tex`).  Let `z` be a colouring constant on the
face classes of the boundary walk that never flips both sides of a boundary edge.  If the kept
darts `GL05b.movePred z` in cycle order form a nonempty walk, and the kept parts of the source and
target arcs are arcs `t₁'`, `t₂'`, then the kept darts are re-listed as the closed walk
`s₁ t₁'⁻¹ s₂ t₂'` with `s₁`, `s₂` of length at most `ε`.  These are the permutation, closed-walk and
side-length clauses of `GL06f.RoseRegionMoveSubArcStatement`. -/
theorem closedWalk_listing_of_filter {D : GGT.RelGenSet G Lambda} {eps lo hi : ℕ}
    {X : DiscDiagram.{u, w, v} W} (K : PocketFaceSet D eps X lo hi)
    {z : X.toCombMap.Dart → Bool}
    (hz : ∀ x y, CombMap.FaceClassStep X.toCombMap
      (walkKeep X.toCombMap K.boundary.cycle) x y → z x = z y)
    (hind : ∀ d ∈ K.boundary.cycle, z d = false ∨ z (X.toCombMap.alpha d) = false)
    {t₁' : CyclicArc (cellDarts X K.source)} {t₂' : CyclicArc (outerDarts X)}
    (hne : K.boundary.cycle.filter (GL05b.movePred X.toCombMap z) ≠ [])
    (hchain : (K.boundary.cycle.filter (GL05b.movePred X.toCombMap z)).IsChain fun d e =>
      X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e)
    (hA : K.sourceArc.darts.filter
      (fun d => GL05b.movePred X.toCombMap z (X.toCombMap.alpha d)) = t₁'.darts)
    (hB : K.targetArc.darts.filter (GL05b.movePred X.toCombMap z) = t₂'.darts) :
    ∃ s₁ s₂ : List X.toCombMap.Dart,
      List.Perm (s₁ ++ invDarts X t₁'.darts ++ s₂ ++ t₂'.darts)
        (K.boundary.cycle.filter (GL05b.movePred X.toCombMap z)) ∧
      IsClosedDartWalk X.toCombMap (s₁ ++ invDarts X t₁'.darts ++ s₂ ++ t₂'.darts) ∧
      s₁.length ≤ eps ∧ s₂.length ≤ eps := by
  have hdec : (K.firstSide ++ invDarts X K.sourceArc.darts ++ K.secondSide ++
      K.targetArc.darts).filter (GL05b.movePred X.toCombMap z) =
      K.boundary.cycle.filter (GL05b.movePred X.toCombMap z) :=
    congrArg (List.filter (GL05b.movePred X.toCombMap z)) K.decomposition.symm
  have hchain' : ((K.firstSide ++ invDarts X K.sourceArc.darts ++ K.secondSide ++
      K.targetArc.darts).filter (GL05b.movePred X.toCombMap z)).IsChain fun d e =>
        X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e := by
    rw [hdec]
    exact hchain
  obtain ⟨s₁, s₂, heq, -, -, -, -, -, hl₁, hl₂⟩ :=
    exists_junction_listing X
      (fun d e => X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e)
      (GL05b.movePred X.toCombMap z) K.firstSide K.secondSide K.sourceArc t₁' K.targetArc t₂'
      hA hB hchain'
  have hL := heq.trans hdec
  have hLne : s₁ ++ invDarts X t₁'.darts ++ s₂ ++ t₂'.darts ≠ [] := by
    rw [hL]
    exact hne
  have hLchain : (s₁ ++ invDarts X t₁'.darts ++ s₂ ++ t₂'.darts).IsChain fun d e =>
      X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e := by
    rw [hL]
    exact hchain
  exact ⟨s₁, s₂, List.Perm.of_eq hL,
    isClosedDartWalk_of_perm_filter K.boundary.cycle_nodup K.boundary.cycle_mem_iff hz hind
      (List.Perm.of_eq hL) hLne hLchain,
    hl₁.trans K.firstSide_length_le, hl₂.trans K.secondSide_length_le⟩

end GroupApproximation.Full.GL03C
