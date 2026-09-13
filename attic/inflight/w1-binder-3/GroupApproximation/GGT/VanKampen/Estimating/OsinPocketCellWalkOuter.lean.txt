import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketMultipleEdgeCopy
import GroupApproximation.Meta.AxiomGuard

/-!
# The exterior face against the pocket walk between two cells

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): two distinct selected regions `a`, `b`
joining the same two distinct cells `Π_i` and `Π_j` bound a subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.

The pocket walk `CellPocketWalk.walk` of `CellPocketWalk.exists_of_joinsCells` reads the side of `b`
leaving `Π_j`, the arc `t_1` of `Π_i` backwards, the side of `a` leaving `Π_i`, and the arc `t_2` of
`Π_j` backwards.  The arc `t_1` spans the arc of `a`, the gap of `Π_i` after it in carrier order, and
the arc of `b`.  The walk darts along `t_1` and `t_2` reverse darts of the cells, so their own faces
are the faces across the cells: the regions along the region arcs, and the faces across the gaps.
Every face across a gap dart is therefore on the side of the walk.

This is why the exterior face need not be off the side.  If `Π_i` touches `∂Δ` along the gap of
`t_1`, the exterior face is on the side of the walk of `(a, b)`.  Swapping `a` and `b` replaces that
gap by the other gap of `Π_i`.  The hypotheses of `CellPocketWalkOuterOffSideStatement`
(`Estimating/OsinPocketMultipleEdgeCopy.lean`) fix the order `(a, b)` and constrain only the sides
and the cells (`CellPocketWalk.CopyClean`), so that statement forces the exterior face across no dart
of `t_1` or `t_2`.  No least-area diagram with such a gap is built here.

* `CellPocketWalk.faceOf_alpha_mem_sideFaces_of_mem_arc`: the face across a dart of `t_1` or `t_2`
  is on the side of the walk.
* `CellPocketWalk.outerFace_mem_sideFaces_of_mem_arc`: in particular, if it is the exterior face,
  the exterior face is on the side.
* `CellPocketWalk.not_outerFace_across_arc_of_outerOffSide`: `CellPocketWalkOuterOffSideStatement`
  implies that no dart of `t_1` or `t_2` has the exterior face across it.
* `CellPocketWalk.two_le_length_cellDarts_first` and `_second`: both carriers have at least two
  darts, so the monogon cell of `OsinPocketMultipleEdgeLakeModel` does not carry a pocket walk.
  The lake obstructs following outer cycles, not the exterior face.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121 at origin/main 68481e4d7,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`), through Osin's Lemma 9.7(b);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded SimpleClosedWalkSides

namespace CellPocketWalk

section Arc

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **The faces across the arcs are on the side of the walk.**  A dart `x` of `t_1` or `t_2` gives
the walk dart `alpha x`, whose own face is the face across `x`. -/
theorem faceOf_alpha_mem_sideFaces_of_mem_arc (K : CellPocketWalk D eps X i j)
    {x : X.toCombMap.Dart} (hx : x ∈ K.firstArc.darts ++ K.secondArc.darts) :
    X.toCombMap.faceOf (X.toCombMap.alpha x) ∈ sideFaces X.toCombMap K.walk := by
  have hinv : ∀ {l : List X.toCombMap.Dart}, x ∈ l → X.toCombMap.alpha x ∈ invDarts X l := by
    intro l hl
    show X.toCombMap.alpha x ∈ l.reverse.map X.toCombMap.alpha
    exact List.mem_map.mpr ⟨x, List.mem_reverse.mpr hl, rfl⟩
  have hmem : X.toCombMap.alpha x ∈ K.walk := by
    show X.toCombMap.alpha x ∈
      K.firstSide ++ invDarts X K.firstArc.darts ++ K.secondSide ++ invDarts X K.secondArc.darts
    rcases List.mem_append.mp hx with h | h
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (hinv h)))
    · exact List.mem_append_right _ (hinv h)
  exact (mem_sideFaces_iff X.toCombMap K.walk (X.toCombMap.alpha x)).mpr
    ⟨X.toCombMap.alpha x, hmem, .refl _⟩

/-- **The exterior face across an arc dart is on the side of the walk.** -/
theorem outerFace_mem_sideFaces_of_mem_arc (K : CellPocketWalk D eps X i j)
    {x : X.toCombMap.Dart} (hx : x ∈ K.firstArc.darts ++ K.secondArc.darts)
    (hxout : X.toCombMap.faceOf (X.toCombMap.alpha x) = X.outerFace) :
    X.outerFace ∈ sideFaces X.toCombMap K.walk := by
  rw [← hxout]
  exact K.faceOf_alpha_mem_sideFaces_of_mem_arc hx

end Arc

/-- **What `CellPocketWalkOuterOffSideStatement` asks.**  Under its hypotheses, no dart of the arcs
`t_1` and `t_2` of the walk has the exterior face across it.  So the statement excludes that `Π_i`
touches `∂Δ` along the gap between the arcs of `a` and `b` in carrier order, and likewise for `Π_j`.
Its hypotheses fix the order `(a, b)`; the walk of `(b, a)` spans the other gaps. -/
theorem not_outerFace_across_arc_of_outerOffSide
    (hout : CellPocketWalkOuterOffSideStatement.{u, w, v})
    {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {eps : ℕ} {lambda c : ℝ} {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord} (hlea : Delta.LeastArea)
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    {i j : Fin S.diagram.rCellCount} {a b : RegionCandidate D eps S.diagram}
    (ha : a ∈ S.family) (hb : b ∈ S.family) (hab : a ≠ b) (hij : i ≠ j)
    (hai : a.JoinsCells i j) (hbi : b.JoinsCells i j) (hclean : CellPocketWalk.CopyClean a b i j)
    (K : CellPocketWalk D eps S.diagram i j) (hfirst : K.firstSide = b.sideFrom j)
    (hsecond : K.secondSide = a.sideFrom i)
    (h₁ : ∃ G₁ : CyclicArc (cellDarts S.diagram i),
      K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i)
    (h₂ : ∃ G₂ : CyclicArc (cellDarts S.diagram j),
      K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j)
    (hne : K.walk ≠ [])
    (hchain : K.walk.IsChain fun d e => S.diagram.toCombMap.vertexOf
      (S.diagram.toCombMap.alpha d) = S.diagram.toCombMap.vertexOf e)
    (hcloses : S.diagram.toCombMap.vertexOf (S.diagram.toCombMap.alpha (K.walk.getLast hne)) =
      S.diagram.toCombMap.vertexOf (K.walk.head hne))
    (hnodup : K.walk.Nodup) (halpha : ∀ d ∈ K.walk, S.diagram.toCombMap.alpha d ∉ K.walk) :
    ∀ x ∈ K.firstArc.darts ++ K.secondArc.darts,
      S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha x) ≠ S.diagram.outerFace := by
  intro x hx hxout
  exact hout hlea S ha hb hab hij hai hbi hclean K hfirst hsecond h₁ h₂ hne hchain hcloses hnodup
    halpha (K.outerFace_mem_sideFaces_of_mem_arc hx hxout)

/-- **The carrier of `Π_i` has at least two darts**: the arc `t_1` of a pocket walk spans the
nonempty arcs of `a` and `b` on `Π_i`. -/
theorem two_le_length_cellDarts_first {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda} {eps : ℕ} {lambda c : ℝ}
    {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (S : RealizedSectionFamily D lambda c eps Delta cuts)
    {i j : Fin S.diagram.rCellCount} {a b : RegionCandidate D eps S.diagram}
    (ha : a ∈ S.family) (hb : b ∈ S.family) (K : CellPocketWalk D eps S.diagram i j)
    (h₁ : ∃ G₁ : CyclicArc (cellDarts S.diagram i),
      K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i) :
    2 ≤ (cellDarts S.diagram i).length := by
  obtain ⟨G₁, hG₁⟩ := h₁
  have ha' := RegionCandidate.cellArcList_length_pos (S.nondegenerate a ha) i
  have hb' := RegionCandidate.cellArcList_length_pos (S.nondegenerate b hb) i
  have hlen : K.firstArc.darts.length = K.firstArc.length := K.firstArc.darts_length
  rw [hG₁, List.length_append, List.length_append] at hlen
  have hle := K.firstArc.length_le
  omega

/-- **The carrier of `Π_j` has at least two darts**: the arc `t_2` of a pocket walk spans the
nonempty arcs of `b` and `a` on `Π_j`. -/
theorem two_le_length_cellDarts_second {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda} {eps : ℕ} {lambda c : ℝ}
    {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (S : RealizedSectionFamily D lambda c eps Delta cuts)
    {i j : Fin S.diagram.rCellCount} {a b : RegionCandidate D eps S.diagram}
    (ha : a ∈ S.family) (hb : b ∈ S.family) (K : CellPocketWalk D eps S.diagram i j)
    (h₂ : ∃ G₂ : CyclicArc (cellDarts S.diagram j),
      K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j) :
    2 ≤ (cellDarts S.diagram j).length := by
  obtain ⟨G₂, hG₂⟩ := h₂
  have ha' := RegionCandidate.cellArcList_length_pos (S.nondegenerate a ha) j
  have hb' := RegionCandidate.cellArcList_length_pos (S.nondegenerate b hb) j
  have hlen : K.secondArc.darts.length = K.secondArc.length := K.secondArc.darts_length
  rw [hG₂, List.length_append, List.length_append] at hlen
  have hle := K.secondArc.length_le
  omega

end CellPocketWalk

end GroupApproximation.GGT.VanKampen

#audit_axioms
  GroupApproximation.GGT.VanKampen.CellPocketWalk.faceOf_alpha_mem_sideFaces_of_mem_arc
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketWalk.outerFace_mem_sideFaces_of_mem_arc
#audit_axioms
  GroupApproximation.GGT.VanKampen.CellPocketWalk.not_outerFace_across_arc_of_outerOffSide
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketWalk.two_le_length_cellDarts_first
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketWalk.two_le_length_cellDarts_second
