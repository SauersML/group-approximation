import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketWalkCopyNoncrossing
import Mathlib.Data.List.Cycle
import Mathlib.Data.List.Rotate
import GroupApproximation.Meta.AxiomGuard

/-!
# The decomposition walk of a two-gon is noncrossing under the edge conditions

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): "Let us consider the subdiagram `Γ_1` of
`Δ` such that: (i) `∂Γ_1 = s_1 t_1 s_2 t_2`, where `s_1, s_2` are side arcs of some of `Γ_{i,1}`'s
and `t_1, t_2` are subpaths of `∂Π` and the section `q_1` of `∂Δ`, respectively".

C6′ of Lemma 9.3 reads the pocket of two exterior regions `a`, `b` of a cell `Π_i` to one section,
the target arc of `a` first, as the walk `source.reverseDarts ++ a.rightSide ++ target.darts ++
b.leftSide` (`TwoGonEitherFollowsPocketInput`, `Estimating/OsinAppendixEulerTwoGonEitherFollows`).
`PocketWalk.exists_of_le` gives the pocket walk `K.walk = b.leftSide ++ invDarts source ++
a.rightSide ++ target` of the same two regions, and `PocketWalk.isNoncrossingClosedWalk_of_copyClean`
(`Estimating/OsinPocketWalkCopyNoncrossing`) makes it noncrossing at least area under the edge
conditions `PocketWalk.CopyClean`.  The decomposition walk is a rotation of `K.walk`.

* `IsNoncrossingClosedWalk.vertexOf_alpha_eq_next`, `IsNoncrossingClosedWalk.of_next`: a
  noncrossing closed walk through cyclic successors.
* `IsNoncrossingClosedWalk.rotate`, `IsNoncrossingClosedWalk.append_comm`: a cyclic permutation of a
  noncrossing closed walk is a noncrossing closed walk.
* `PocketWalk.CopyCleanAt`: the edge conditions with the source cell given by its index, so that a
  producer need not name the pocket walk; `PocketWalk.copyClean_of_copyCleanAt` gives
  `PocketWalk.CopyClean` for every pocket walk from that cell.
* `PocketWalk.exists_noncrossing_decomposition_of_copyCleanAt`: the decomposition walk of two
  ordered exterior regions is noncrossing at least area under the edge conditions, with the arc
  bounds of `TwoGonEitherFollowsPocketInput`.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`), through Osin's Lemma 9.7;
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded SimpleClosedWalkSides

namespace IsNoncrossingClosedWalk

variable {M : CombMap.{u}} {walk : List M.Dart}

/-- Each dart of a noncrossing closed walk ends where its cyclic successor starts. -/
theorem vertexOf_alpha_eq_next [DecidableEq M.Dart] (hw : IsNoncrossingClosedWalk M walk)
    {d : M.Dart} (hd : d ∈ walk) : M.vertexOf (M.alpha d) = M.vertexOf (walk.next d hd) := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hd
  rw [List.next_getElem walk hw.nodup i hi]
  by_cases hlast : i + 1 < walk.length
  · simp only [Nat.mod_eq_of_lt hlast]
    exact List.isChain_iff_getElem.mp hw.chain i (by omega)
  · have h := hw.closes
    simp only [List.getLast_eq_getElem, List.head_eq_getElem] at h
    simp only [show i + 1 = walk.length by omega, Nat.mod_self]
    obtain rfl : i = walk.length - 1 := by omega
    exact h

/-- **A noncrossing closed walk from cyclic successors.**  A nonempty duplicate-free list of darts,
each ending where its cyclic successor starts, using no edge in both directions, whose first dart
met on an edge of the walk when rotating from the reversal of a walk dart is a walk dart, is a
noncrossing closed walk. -/
theorem of_next [DecidableEq M.Dart] (hne : walk ≠ []) (hnd : walk.Nodup)
    (hnext : ∀ d (hd : d ∈ walk), M.vertexOf (M.alpha d) = M.vertexOf (walk.next d hd))
    (halpha : ∀ d ∈ walk, M.alpha d ∉ walk)
    (hturn : ∀ d ∈ walk, ∀ m : ℕ, 0 < m → walkKeep M walk ((M.sigma ^ m) (M.alpha d)) →
      (∀ k, 0 < k → k < m → ¬ walkKeep M walk ((M.sigma ^ k) (M.alpha d))) →
      (M.sigma ^ m) (M.alpha d) ∈ walk) :
    IsNoncrossingClosedWalk M walk where
  ne_nil := hne
  nodup := hnd
  chain := by
    refine List.isChain_iff_getElem.mpr fun i hi => ?_
    have hi' : i + 1 < walk.length := by omega
    have h := hnext _ (List.getElem_mem (Nat.lt_of_succ_lt hi'))
    rw [List.next_getElem walk hnd i (Nat.lt_of_succ_lt hi')] at h
    simp only [Nat.mod_eq_of_lt hi'] at h
    exact h
  closes := by
    have h := hnext _ (List.getLast_mem hne)
    rw [List.next_getLast_eq_head walk hne hnd] at h
    exact h
  alpha_not_mem := halpha
  turn_mem := hturn

/-- The edges of a rotated walk are the edges of the walk. -/
theorem walkKeep_rotate_iff (k : ℕ) (z : M.Dart) :
    walkKeep M (walk.rotate k) z ↔ walkKeep M walk z := by
  unfold SimpleClosedWalkSides.walkKeep
  rw [List.mem_rotate, List.mem_rotate]

/-- **A cyclic permutation of a noncrossing closed walk is a noncrossing closed walk.** -/
theorem rotate (hw : IsNoncrossingClosedWalk M walk) (k : ℕ) :
    IsNoncrossingClosedWalk M (walk.rotate k) := by
  classical
  have hrot : walk ~r walk.rotate k := ⟨k, rfl⟩
  refine of_next (List.rotate_eq_nil_iff.not.mpr hw.ne_nil) (List.nodup_rotate.mpr hw.nodup)
    (fun d hd => ?_)
    (fun d hd hmem => hw.alpha_not_mem d (List.mem_rotate.mp hd) (List.mem_rotate.mp hmem)) ?_
  · have hd' : d ∈ walk := List.mem_rotate.mp hd
    exact (hw.vertexOf_alpha_eq_next hd').trans
      (congrArg M.vertexOf (List.isRotated_next_eq hrot hw.nodup hd'))
  · intro d hd m hm hkeep hfirst
    exact List.mem_rotate.mpr (hw.turn_mem d (List.mem_rotate.mp hd) m hm
      ((walkKeep_rotate_iff k _).mp hkeep)
      (fun t ht htm htkeep => hfirst t ht htm ((walkKeep_rotate_iff k _).mpr htkeep)))

/-- **Swapping the two halves of a noncrossing closed walk** gives a noncrossing closed walk. -/
theorem append_comm {l₁ l₂ : List M.Dart} (hw : IsNoncrossingClosedWalk M (l₁ ++ l₂)) :
    IsNoncrossingClosedWalk M (l₂ ++ l₁) := by
  have h := hw.rotate l₁.length
  rwa [List.rotate_append_length_eq] at h

end IsNoncrossingClosedWalk

namespace PocketWalk

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ}

/-- **The edge conditions for the pocket of `x` and `y` from the cell `i`**: the fields of
`PocketWalk.CopyClean`, with the source cell given by its index.  No edge has the exterior face on
both sides, no edge has `Π_i` on both sides, no edge joins `Π_i` to the exterior face, no edge
joins a face of `x` to a face of `y`, and no dart of the left side of `y` or the right side of `x`
has `Π_i` or the exterior face across it. -/
structure CopyCleanAt (X : DiscDiagram.{u, w, v} W) (i : Fin X.rCellCount)
    (x y : RegionCandidate D eps X) : Prop where
  spur : ∀ d, X.toCombMap.faceOf d = X.outerFace →
    X.toCombMap.faceOf (X.toCombMap.alpha d) ≠ X.outerFace
  cell_self : ∀ d, X.toCombMap.faceOf d = (cell X i).face →
    X.toCombMap.faceOf (X.toCombMap.alpha d) ≠ (cell X i).face
  cell_outer : ∀ d, X.toCombMap.faceOf d = (cell X i).face →
    X.toCombMap.faceOf (X.toCombMap.alpha d) ≠ X.outerFace
  regions : ∀ d, X.toCombMap.faceOf d ∈ x.1 → X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ y.1
  side_cell : ∀ d ∈ y.2.leftSide ++ x.2.rightSide,
    X.toCombMap.faceOf (X.toCombMap.alpha d) ≠ (cell X i).face
  side_outer : ∀ d ∈ y.2.leftSide ++ x.2.rightSide,
    X.toCombMap.faceOf (X.toCombMap.alpha d) ≠ X.outerFace

/-- The edge conditions from the cell `i` are the edge conditions of every pocket walk from `i`. -/
theorem copyClean_of_copyCleanAt {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}
    {i : Fin X.rCellCount} {x y : RegionCandidate D eps X} (K : PocketWalk D eps X lo hi)
    (hsource : K.source = i) (h : CopyCleanAt X i x y) : K.CopyClean x y where
  spur := h.spur
  cell_self := by
    rw [hsource]
    exact h.cell_self
  cell_outer := by
    rw [hsource]
    exact h.cell_outer
  regions := h.regions
  side_cell := by
    rw [hsource]
    exact h.side_cell
  side_outer := h.side_outer

variable {lambda c : ℝ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **The decomposition walk of two ordered exterior regions is noncrossing under the edge
conditions.**  Let `a ≠ b` be exterior regions of the cell `i` to the section `j`, with the target
arc of `a` ending before that of `b` starts.  If the diagram has least area and satisfies the edge
conditions for `a` and `b` from `i`, there are a source arc on `Π_i` and a target arc on the
oriented outer boundary such that `source.reverseDarts ++ a.rightSide ++ target.darts ++
b.leftSide` is a noncrossing closed walk, the source arc is at least as long as the source arcs of
`a` and `b` together, the target arc runs from the start of the target arc of `a` to the end of
that of `b`, and it is at least as long as both target arcs together. -/
theorem exists_noncrossing_decomposition_of_copyCleanAt
    (S : RealizedSectionFamily D lambda c eps Delta cuts)
    {i : Fin S.diagram.rCellCount} {j : Fin cuts.count} {a b : RegionCandidate D eps S.diagram}
    (ha : a ∈ RegionCandidate.exteriorAt S.family i)
    (hb : b ∈ RegionCandidate.exteriorAt S.family i) (hab : a ≠ b)
    (hja : RegionCandidate.TargetsSectionIndex cuts j a)
    (hjb : RegionCandidate.TargetsSectionIndex cuts j b)
    (horder : a.2.targetArc.start.1 + a.2.targetArc.length ≤ b.2.targetArc.start.1)
    (hlea : S.diagram.LeastArea) (hclean : CopyCleanAt S.diagram i a b) :
    ∃ (source : CyclicArc (cellDarts S.diagram i))
      (target : CyclicArc (targetDarts S.diagram none)),
      IsNoncrossingClosedWalk S.diagram.toCombMap
          (source.reverseDarts ++ a.2.rightSide ++ target.darts ++ b.2.leftSide) ∧
        a.2.sourceArc.length + b.2.sourceArc.length ≤ source.length ∧
        target.start.1 = a.2.targetArc.start.1 ∧
        target.start.1 + target.length = b.2.targetArc.start.1 + b.2.targetArc.length ∧
        a.2.targetArc.length + b.2.targetArc.length ≤ target.length := by
  obtain ⟨K, hsource, hfirst, hsecond, ⟨Gap, hsrc⟩, hstart, hend⟩ :=
    exists_of_le S ha hb hab hja hjb (by omega)
  have hw := isNoncrossingClosedWalk_of_copyClean S ha hb hab hjb K hsource hfirst hsecond
    ⟨Gap, hsrc⟩ hstart hend hlea (copyClean_of_copyCleanAt K hsource hclean)
  rcases K with ⟨src, sArc, tArc, fs, ss, _, _, _, _, _, _, _, _⟩
  dsimp only at hsource hfirst hsecond hsrc hstart hend hw
  subst hsource hfirst hsecond
  refine ⟨sArc, tArc, ?_, ?_, hstart, hend, by omega⟩
  · have hrot : IsNoncrossingClosedWalk S.diagram.toCombMap
        (b.2.leftSide ++ (invDarts S.diagram sArc.darts ++ a.2.rightSide ++ tArc.darts)) := by
      simpa only [PocketWalk.walk, List.append_assoc] using hw
    exact hrot.append_comm
  · have hl := congrArg List.length hsrc
    simp only [List.length_append, CyclicArc.darts_length] at hl
    omega

end PocketWalk

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.vertexOf_alpha_eq_next
#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.of_next
#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.walkKeep_rotate_iff
#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.rotate
#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.append_comm
#audit_axioms GroupApproximation.GGT.VanKampen.PocketWalk.copyClean_of_copyCleanAt
#audit_axioms GroupApproximation.GGT.VanKampen.PocketWalk.exists_noncrossing_decomposition_of_copyCleanAt
