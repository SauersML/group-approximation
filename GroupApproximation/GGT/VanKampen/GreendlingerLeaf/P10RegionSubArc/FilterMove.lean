import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.Live.Reduction
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.FLLists
import GroupApproximation.Meta.AxiomGuard

/-!
# The in-order filter move case of the sub-arc region move

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-87.

Notation: `M = X.toCombMap`, `c = K.boundary.cycle`, `p = movePred M z`.  The conclusion of
`P10Rose.RoseRegionMoveSubArcStatement` for a fixed pocket face set `K` is
`subArc_Goal K`: a region-constant colouring `z` together with a listing
`s₁ ++ t₁⁻¹ ++ s₂ ++ t₂` of the kept darts `c.filter p` (up to `List.Perm`) with all bounds.

`subArc_FilterMove K z` is the **in-order case** for one colouring `z` (any colouring,
not only a lobe colouring): the colour clauses of the goal, the source cell of `K` outside and
some cell inside the moved face set, the kept darts of `K.sourceArc⁻¹` are `t₁⁻¹` for an arc
`t₁` of the source cell, the kept darts of `K.targetArc` are an arc `t₂` inside the old window,
and `c.filter p` is a closed dart walk.

* `subArc_goal_of_filterMove`: the in-order case proves the goal.  The listing is
  `c.filter p` itself, split along `K.decomposition` (the `List.Perm` is an equality), and every
  bound follows from the bound of `K`, because filtering never lengthens a list.
* `subArc_filterMove_of_block`: one sufficient criterion for the in-order case, the
  closed removed block: `c = A ++ B ++ C` with `p` removing exactly the closed walk `B` (or
  keeping exactly the closed walk `B`, the wrap-around form), through
  `P10RoseLobe.roseLobeFL_isClosedDartWalk_filter_of_block`.

Everything in this module is PROVED; the residual is in `P10RegionSubArc.Residual`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionSubArc

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove

/-- Filtering a four-piece list filters each piece. -/
theorem subArc_filter_four {α : Type*} {p : α → Bool} {c a b s t b' t' : List α}
    (hc : c = a ++ b ++ s ++ t) (hb : b.filter p = b') (ht : t.filter p = t') :
    c.filter p = a.filter p ++ b' ++ s.filter p ++ t' := by
  rw [hc, List.filter_append, List.filter_append, List.filter_append, hb, ht]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionSubArc.subArc_filter_four

/-- A filtered list is no longer than the list. -/
theorem subArc_length_le_filter {α : Type*} {p : α → Bool} {l l' : List α}
    (h : l.filter p = l') : l'.length ≤ l.length := by
  rw [← h]
  exact List.length_filter_le p l

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionSubArc.subArc_length_le_filter

/-- The reversed darts of a list have its length. -/
theorem subArc_length_invDarts {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} (X : DiscDiagram.{u, w, v} W)
    (l : List X.toCombMap.Dart) : (invDarts X l).length = l.length := by
  simp only [invDarts, List.length_map, List.length_reverse]

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionSubArc.subArc_length_invDarts

section Pocket

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **The goal of the sub-arc region move for one pocket face set**: the conclusion of
`P10Rose.RoseRegionMoveSubArcStatement`, verbatim. -/
def subArc_Goal (K : PocketFaceSet D eps X lo hi) : Prop :=
  ∃ z : X.toCombMap.Dart → Bool,
    (∀ x y, CombMap.FaceClassStep X.toCombMap
      (walkKeep X.toCombMap K.boundary.cycle) x y → z x = z y) ∧
    (∀ d ∈ K.boundary.cycle, z d = false ∨ z (X.toCombMap.alpha d) = false) ∧
    X.outerFace ∉ flipFaces X.toCombMap K.faces z ∧
    (∃ y ∈ K.boundary.cycle, movePred X.toCombMap z y = false) ∧
    ∃ (source kept : Fin X.rCellCount),
      (cell X source).face ∉ flipFaces X.toCombMap K.faces z ∧
      (cell X kept).face ∈ flipFaces X.toCombMap K.faces z ∧
      ∃ (t₁ : CyclicArc (cellDarts X source)) (t₂ : CyclicArc (outerDarts X))
        (s₁ s₂ : List X.toCombMap.Dart),
        List.Perm (s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts)
          (K.boundary.cycle.filter (movePred X.toCombMap z)) ∧
        IsClosedDartWalk X.toCombMap (s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts) ∧
        s₁.length ≤ eps ∧ s₂.length ≤ eps ∧ lo ≤ t₂.start.1 ∧
        t₂.start.1 + t₂.length ≤ hi ∧
        t₁.length < (cellDarts X source).length ∧ t₂.length < (outerDarts X).length

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionSubArc.subArc_Goal

/-- **The in-order filter move** for a colouring `z` of the darts (see the module docstring). -/
def subArc_FilterMove (K : PocketFaceSet D eps X lo hi)
    (z : X.toCombMap.Dart → Bool) : Prop :=
  (∀ x y, CombMap.FaceClassStep X.toCombMap
      (walkKeep X.toCombMap K.boundary.cycle) x y → z x = z y) ∧
    (∀ d ∈ K.boundary.cycle, z d = false ∨ z (X.toCombMap.alpha d) = false) ∧
    X.outerFace ∉ flipFaces X.toCombMap K.faces z ∧
    (∃ y ∈ K.boundary.cycle, movePred X.toCombMap z y = false) ∧
    (cell X K.source).face ∉ flipFaces X.toCombMap K.faces z ∧
    (∃ kept : Fin X.rCellCount, (cell X kept).face ∈ flipFaces X.toCombMap K.faces z) ∧
    (∃ t₁ : CyclicArc (cellDarts X K.source),
      (invDarts X K.sourceArc.darts).filter (movePred X.toCombMap z) = invDarts X t₁.darts) ∧
    (∃ t₂ : CyclicArc (outerDarts X),
      K.targetArc.darts.filter (movePred X.toCombMap z) = t₂.darts ∧
      K.targetArc.start.1 ≤ t₂.start.1 ∧
      t₂.start.1 + t₂.length ≤ K.targetArc.start.1 + K.targetArc.length) ∧
    IsClosedDartWalk X.toCombMap (K.boundary.cycle.filter (movePred X.toCombMap z))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionSubArc.subArc_FilterMove

/-- **The in-order case proves the goal.**  The sides are the kept darts of the old sides, the
listing is `c.filter p` split along `K.decomposition`, and each bound follows from the old one. -/
theorem subArc_goal_of_filterMove (K : PocketFaceSet D eps X lo hi)
    (hsrc : K.sourceArc.length < (cellDarts X K.source).length)
    (htgt : K.targetArc.length < (outerDarts X).length)
    {z : X.toCombMap.Dart → Bool} (hm : subArc_FilterMove K z) :
    subArc_Goal K := by
  obtain ⟨hz, hind, hout, hy, hsource, ⟨kept, hkept⟩, ⟨t₁, ht₁⟩, ⟨t₂, ht₂, hst, hend⟩,
    hwalk⟩ := hm
  have hfilt := subArc_filter_four K.decomposition ht₁ ht₂
  have h₁ := subArc_length_le_filter ht₁
  have h₂ := subArc_length_le_filter ht₂
  simp only [subArc_length_invDarts, CyclicArc.darts_length] at h₁ h₂
  rw [hfilt] at hwalk
  unfold subArc_Goal
  exact ⟨z, hz, hind, hout, hy, K.source, kept, hsource, hkept, t₁, t₂, _, _,
    List.Perm.of_eq hfilt.symm, hwalk, (List.length_filter_le _ _).trans K.firstSide_length_le,
    (List.length_filter_le _ _).trans K.secondSide_length_le, K.lo_le.trans hst,
    hend.trans K.le_hi, h₁.trans_lt hsrc, h₂.trans_lt htgt⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionSubArc.subArc_goal_of_filterMove

/-- A dart of `B` is a dart of `A ++ B ++ C`. -/
theorem subArc_mem_of_mem_B {α : Type*} {c A B C : List α} (hc : c = A ++ B ++ C) {d : α}
    (hd : d ∈ B) : d ∈ c := by
  rw [hc]
  exact List.mem_append_left C (List.mem_append_right A hd)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionSubArc.subArc_mem_of_mem_B

/-- A dart of `A ++ C` is a dart of `A ++ B ++ C`. -/
theorem subArc_mem_of_mem_AC {α : Type*} {c A B C : List α} (hc : c = A ++ B ++ C) {d : α}
    (hd : d ∈ A ++ C) : d ∈ c := by
  rw [hc]
  rcases List.mem_append.mp hd with hd | hd
  · exact List.mem_append_left C (List.mem_append_left B hd)
  · exact List.mem_append_right (A ++ B) hd

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionSubArc.subArc_mem_of_mem_AC

/-- A nonempty list that a filter empties has an element the filter removes. -/
theorem subArc_exists_false_of_nil {α : Type*} {p : α → Bool} {L : List α} (hL : L ≠ [])
    (h : L.filter p = []) : ∃ y ∈ L, p y = false := by
  obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil L hL
  exact ⟨y, hy, Bool.eq_false_iff.mpr (List.filter_eq_nil_iff.mp h y hy)⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionSubArc.subArc_exists_false_of_nil

/-- **The closed removed block gives the in-order case.**  With the colour clauses and the two
arc placements, if `c = A ++ B ++ C` where the move removes all of the closed walk `B` and keeps
all of `A ++ C ≠ []`, or keeps all of the closed walk `B` and removes all of `A ++ C ≠ []`, then
`z` is an in-order filter move: the kept walk closes up by excising `B`
(`P10RoseLobe.roseLobeFL_isClosedDartWalk_filter_of_block`). -/
theorem subArc_filterMove_of_block (K : PocketFaceSet D eps X lo hi) (hK : K.ClosedWalk)
    {z : X.toCombMap.Dart → Bool}
    (hz : ∀ x y, CombMap.FaceClassStep X.toCombMap
      (walkKeep X.toCombMap K.boundary.cycle) x y → z x = z y)
    (hind : ∀ d ∈ K.boundary.cycle, z d = false ∨ z (X.toCombMap.alpha d) = false)
    (hout : X.outerFace ∉ flipFaces X.toCombMap K.faces z)
    (hsource : (cell X K.source).face ∉ flipFaces X.toCombMap K.faces z)
    {kept : Fin X.rCellCount} (hkept : (cell X kept).face ∈ flipFaces X.toCombMap K.faces z)
    {A B C : List X.toCombMap.Dart} (hc : K.boundary.cycle = A ++ B ++ C)
    (hblk : (B.filter (movePred X.toCombMap z) = [] ∧
        (A ++ C).filter (movePred X.toCombMap z) = A ++ C ∧ A ++ C ≠ [] ∧
        IsClosedDartWalk X.toCombMap B) ∨
      (B.filter (movePred X.toCombMap z) = B ∧
        (A ++ C).filter (movePred X.toCombMap z) = [] ∧ A ++ C ≠ [] ∧
        IsClosedDartWalk X.toCombMap B))
    (ht₁ : ∃ t₁ : CyclicArc (cellDarts X K.source),
      (invDarts X K.sourceArc.darts).filter (movePred X.toCombMap z) = invDarts X t₁.darts)
    (ht₂ : ∃ t₂ : CyclicArc (outerDarts X),
      K.targetArc.darts.filter (movePred X.toCombMap z) = t₂.darts ∧
      K.targetArc.start.1 ≤ t₂.start.1 ∧
      t₂.start.1 + t₂.length ≤ K.targetArc.start.1 + K.targetArc.length) :
    subArc_FilterMove K z := by
  have hw : IsClosedDartWalk X.toCombMap K.boundary.cycle :=
    ⟨K.boundary.cycle_nonempty, hK.1, hK.2⟩
  have hwalk := P10RoseLobe.roseLobeFL_isClosedDartWalk_filter_of_block
    (p := movePred X.toCombMap z) hw hc
    (hblk.imp (fun h => ⟨h.1, h.2.1, h.2.2.1, Or.inr h.2.2.2⟩)
      (fun h => ⟨h.1, h.2.1, h.2.2.2⟩))
  have hy : ∃ y ∈ K.boundary.cycle, movePred X.toCombMap z y = false := by
    rcases hblk with ⟨hB, -, -, hBw⟩ | ⟨-, hAC, hne, -⟩
    · obtain ⟨hBne, -, -⟩ := hBw
      obtain ⟨y, hy, hpy⟩ := subArc_exists_false_of_nil hBne hB
      exact ⟨y, subArc_mem_of_mem_B hc hy, hpy⟩
    · obtain ⟨y, hy, hpy⟩ := subArc_exists_false_of_nil hne hAC
      exact ⟨y, subArc_mem_of_mem_AC hc hy, hpy⟩
  unfold subArc_FilterMove
  exact ⟨hz, hind, hout, hy, hsource, ⟨kept, hkept⟩, ht₁, ht₂, hwalk⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionSubArc.subArc_filterMove_of_block

end Pocket

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionSubArc
