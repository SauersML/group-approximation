import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.RegionTouchMembership
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, inner pocket: region cycles touch the pocket walk, unless degenerate

Infrastructure for `P07LakeExclusion.InnerPocketEnclosedTwoArcStatement`
(`GreendlingerLeaf/P07LakeExclusion/InnerTwoArcLong.lean`), Osin, arXiv:math/0411039v3, §9, proof of
Lemma 9.7(b), lane gl-p07-02 (touching half).

## Truth check: the lane statement is FALSE in a degenerate case

The lane asked for `∃ d ∈ a.2.boundary.cycle, ∃ e ∈ K.walk, vertexOf d = vertexOf e` under the
hypotheses of `InnerPocketEnclosedTwoArcStatement`.  This fails when
`a.cellArcList i = []`, `a.sideFrom i = []` and `a.cellArcList j = []`.
* A `RegionCandidate` (`ContiguityGeometry`) with empty source and target arcs has no
  positional link between its arcs and its face set: its boundary cycle is just
  `rightSide ++ leftSide`, and here it equals `a.sideFrom j`.
* So take any diagram satisfying the hypotheses for `b` and `K`.  Let `a` be the singleton face
  set of a `G`-cell `f` sharing no vertex with `K`, with source `i`, target `some j`, both arcs of
  length `0`, `rightSide = []`, and `leftSide` its boundary cycle (`eps ≥ |∂f|`).
* Every hypothesis involving `a` then holds: `JoinsCells`, disjointness from `b`,
  `K.secondSide = a.sideFrom i = []`, the splittings `h₁`/`h₂` with empty contact pieces, and
  `C.face ∉ a.1`.  But the cycle of `a` shares no vertex with `K`.
* The symmetric failure for `b` is `b.cellArcList i = b.cellArcList j = b.sideFrom j = []`.

**Corrected true statements.**  `regionTouch_a`/`regionTouch_b` prove "touches OR degenerate".
`regionTouch_a_of_pos`/`regionTouch_b_of_pos` prove touching under the nondegeneracy that
`RealizedSectionFamily.nondegenerate` supplies upstream (`cellArcList_length_pos`).

## The mathematical proof

For `a`, recall `a.cycle ∼ ā_i ++ a.sideFrom i ++ ā_j ++ a.sideFrom j` and
`K.walk = b.sideFrom j ++ t̄₁ ++ a.sideFrom i ++ t̄₂`, with `a.cellArcList i ⊆ t₁` and
`a.cellArcList j ⊆ t₂`.
* If `a.cellArcList i` has a dart `x`, then `α x` is on the cycle and on `t̄₁ ⊆ K.walk`.
* Otherwise, if `a.sideFrom i` has a dart `x`, then `x` is on the cycle and on `K.secondSide`.
* Otherwise, if `a.cellArcList j` has a dart `x`, then `α x` is on the cycle and on `t̄₂`.
* Otherwise we are in the degenerate case.
In each touching case one dart is shared, so its vertex is shared.  The proof for `b` is the same,
using `b.cellArcList i ⊆ t₁`, `K.firstSide = b.sideFrom j` and `b.cellArcList j ⊆ t₂`.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W}

/-- **The cycle of `a` touches the pocket walk, unless `a` is degenerate on the pocket side.** -/
theorem regionTouch_a {a b : RegionCandidate D eps X} {i j : Fin X.rCellCount}
    {K : CellPocketWalk D eps X i j} (hij : i ≠ j) (hai : a.JoinsCells i j)
    (hsecond : K.secondSide = a.sideFrom i)
    (h₁ : ∃ G₁ : CyclicArc (cellDarts X i),
      K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i)
    (h₂ : ∃ G₂ : CyclicArc (cellDarts X j),
      K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j) :
    (∃ d ∈ a.2.boundary.cycle, ∃ e ∈ K.walk, X.toCombMap.vertexOf d = X.toCombMap.vertexOf e) ∨
      (a.cellArcList i = [] ∧ a.sideFrom i = [] ∧ a.cellArcList j = []) := by
  have hsub₁ := (regionTouch_firstArc_subset h₁).1
  have hsub₂ := (regionTouch_secondArc_subset h₂).2
  by_cases hci : a.cellArcList i = []
  · by_cases hsi : a.sideFrom i = []
    · by_cases hcj : a.cellArcList j = []
      · exact Or.inr ⟨hci, hsi, hcj⟩
      · obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hcj
        refine Or.inl ⟨X.toCombMap.alpha x, ?_, X.toCombMap.alpha x, ?_, rfl⟩
        · exact (regionTouch_mem_cycle_iff hij hai _).mpr
            (Or.inr (Or.inr (Or.inl (regionTouch_mem_invDarts hx))))
        · exact regionTouch_mem_walk_of_mem_invSecondArc K
            (regionTouch_invDarts_subset hsub₂ (regionTouch_mem_invDarts hx))
    · obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hsi
      refine Or.inl ⟨x, ?_, x, ?_, rfl⟩
      · exact (regionTouch_mem_cycle_iff hij hai _).mpr (Or.inr (Or.inl hx))
      · exact regionTouch_mem_walk_of_mem_secondSide K (by rw [hsecond]; exact hx)
  · obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hci
    refine Or.inl ⟨X.toCombMap.alpha x, ?_, X.toCombMap.alpha x, ?_, rfl⟩
    · exact (regionTouch_mem_cycle_iff hij hai _).mpr (Or.inl (regionTouch_mem_invDarts hx))
    · exact regionTouch_mem_walk_of_mem_invFirstArc K
        (regionTouch_invDarts_subset hsub₁ (regionTouch_mem_invDarts hx))

/-- **The cycle of `b` touches the pocket walk, unless `b` is degenerate on the pocket side.** -/
theorem regionTouch_b {a b : RegionCandidate D eps X} {i j : Fin X.rCellCount}
    {K : CellPocketWalk D eps X i j} (hij : i ≠ j) (hbi : b.JoinsCells i j)
    (hfirst : K.firstSide = b.sideFrom j)
    (h₁ : ∃ G₁ : CyclicArc (cellDarts X i),
      K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i)
    (h₂ : ∃ G₂ : CyclicArc (cellDarts X j),
      K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j) :
    (∃ d ∈ b.2.boundary.cycle, ∃ e ∈ K.walk, X.toCombMap.vertexOf d = X.toCombMap.vertexOf e) ∨
      (b.cellArcList i = [] ∧ b.cellArcList j = [] ∧ b.sideFrom j = []) := by
  have hsub₁ := (regionTouch_firstArc_subset h₁).2
  have hsub₂ := (regionTouch_secondArc_subset h₂).1
  by_cases hci : b.cellArcList i = []
  · by_cases hcj : b.cellArcList j = []
    · by_cases hsj : b.sideFrom j = []
      · exact Or.inr ⟨hci, hcj, hsj⟩
      · obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hsj
        refine Or.inl ⟨x, ?_, x, ?_, rfl⟩
        · exact (regionTouch_mem_cycle_iff hij hbi _).mpr (Or.inr (Or.inr (Or.inr hx)))
        · exact regionTouch_mem_walk_of_mem_firstSide K (by rw [hfirst]; exact hx)
    · obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hcj
      refine Or.inl ⟨X.toCombMap.alpha x, ?_, X.toCombMap.alpha x, ?_, rfl⟩
      · exact (regionTouch_mem_cycle_iff hij hbi _).mpr
          (Or.inr (Or.inr (Or.inl (regionTouch_mem_invDarts hx))))
      · exact regionTouch_mem_walk_of_mem_invSecondArc K
          (regionTouch_invDarts_subset hsub₂ (regionTouch_mem_invDarts hx))
  · obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hci
    refine Or.inl ⟨X.toCombMap.alpha x, ?_, X.toCombMap.alpha x, ?_, rfl⟩
    · exact (regionTouch_mem_cycle_iff hij hbi _).mpr (Or.inl (regionTouch_mem_invDarts hx))
    · exact regionTouch_mem_walk_of_mem_invFirstArc K
        (regionTouch_invDarts_subset hsub₁ (regionTouch_mem_invDarts hx))

/-- **Touching for `a` with a nonempty contact on `Π_i`.** -/
theorem regionTouch_a_of_pos {a b : RegionCandidate D eps X} {i j : Fin X.rCellCount}
    {K : CellPocketWalk D eps X i j} (hij : i ≠ j) (hai : a.JoinsCells i j)
    (hsecond : K.secondSide = a.sideFrom i)
    (h₁ : ∃ G₁ : CyclicArc (cellDarts X i),
      K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i)
    (h₂ : ∃ G₂ : CyclicArc (cellDarts X j),
      K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j)
    (hpos : 0 < (a.cellArcList i).length) :
    ∃ d ∈ a.2.boundary.cycle, ∃ e ∈ K.walk, X.toCombMap.vertexOf d = X.toCombMap.vertexOf e :=
  (regionTouch_a hij hai hsecond h₁ h₂).resolve_right fun h => by
    simp [h.1] at hpos

/-- **Touching for `b` with a nonempty contact on `Π_j`.** -/
theorem regionTouch_b_of_pos {a b : RegionCandidate D eps X} {i j : Fin X.rCellCount}
    {K : CellPocketWalk D eps X i j} (hij : i ≠ j) (hbi : b.JoinsCells i j)
    (hfirst : K.firstSide = b.sideFrom j)
    (h₁ : ∃ G₁ : CyclicArc (cellDarts X i),
      K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i)
    (h₂ : ∃ G₂ : CyclicArc (cellDarts X j),
      K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j)
    (hpos : 0 < (b.cellArcList j).length) :
    ∃ d ∈ b.2.boundary.cycle, ∃ e ∈ K.walk, X.toCombMap.vertexOf d = X.toCombMap.vertexOf e :=
  (regionTouch_b hij hbi hfirst h₁ h₂).resolve_right fun h => by
    simp [h.2.1] at hpos

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.regionTouch_a
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.regionTouch_b
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.regionTouch_a_of_pos
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.regionTouch_b_of_pos
