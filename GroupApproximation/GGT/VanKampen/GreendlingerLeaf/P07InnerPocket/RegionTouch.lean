import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.RegionTouchChain
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.RegionTouchCases
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, inner pocket: region cycles are vertex chains touching the pocket walk

Lane gl-p07-02, endpoint `regionCycleTouch : RegionCycleTouchStatement`.  This is infrastructure
for `P07LakeExclusion.InnerPocketEnclosedTwoArcStatement`
(`GreendlingerLeaf/P07LakeExclusion/InnerTwoArcLong.lean`), Osin, arXiv:math/0411039v3, §9, proof of
Lemma 9.7(b).  It supplies the inputs `hch₂`, `hch₃`, `h₂`, `h₃` of lane gl-p07-01
(`keepUnion_connected`) for `c₁ = K.walk`, `c₂ = a.2.boundary.cycle` and
`c₃ = b.2.boundary.cycle`.  `hch₁` is `hw.chain` of the hypothesis
`hw : IsNoncrossingClosedWalk X.toCombMap K.walk`.  It also supplies the membership facts for
lane gl-p07-08.

## Hypotheses

The statement assumes only the part of the hypothesis block of `InnerPocketEnclosedTwoArcStatement`
that is used:
`i ≠ j`, `a.JoinsCells i j`, `b.JoinsCells i j`, `K.firstSide = b.sideFrom j`,
`K.secondSide = a.sideFrom i`, and the splittings `h₁`, `h₂`.  Fewer hypotheses make the statement
stronger, and it still applies inside that block.

## Correction (LOUD)

The touching clause as the lane printed it is **FALSE** when a region is degenerate on the pocket
side; see the model in `RegionTouchCases.lean`.  The statement below therefore gives touching **or**
the degenerate case:
* for `a`: `a.cellArcList i = [] ∧ a.sideFrom i = [] ∧ a.cellArcList j = []`;
* for `b`: `b.cellArcList i = [] ∧ b.cellArcList j = [] ∧ b.sideFrom j = []`.

With nonempty contact arcs (`RealizedSectionFamily.nondegenerate`), use `regionTouch_a_of_pos` and
`regionTouch_b_of_pos`.  The `Hyp` block of `InnerPocketEnclosedTwoArcStatement` does not contain
this nondegeneracy.  So lane gl-p07-15 must either handle a degenerate region, whose cycle is then
a single far side, or add the nondegeneracy hypotheses upstream.

## The mathematical proof

The chain and closing clauses: `RegionTouchChain.lean`, where boundary steps are vertex steps.
The touching and membership clauses: `RegionTouchCases.lean` and `RegionTouchMembership.lean`,
where one dart is shared.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded

/-- **Region cycles are vertex chains touching the pocket walk** (lane gl-p07-02, corrected with
the degenerate disjuncts).  For regions `a`, `b` joining the distinct cells `i`, `j` and a pocket
walk `K` with sides `b.sideFrom j`, `a.sideFrom i` and arcs split by the contact arcs:
* both boundary cycles chain and close at vertices;
* each cycle shares a vertex with `K.walk`, or its region is degenerate on the pocket side;
* the contact arcs lie on the arcs of `K`, and the near sides lie on `K.walk`. -/
def RegionCycleTouchStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W)
    {i j : Fin X.rCellCount} (a b : RegionCandidate D eps X) (K : CellPocketWalk D eps X i j),
    i ≠ j → a.JoinsCells i j → b.JoinsCells i j →
    K.firstSide = b.sideFrom j → K.secondSide = a.sideFrom i →
    (∃ G₁ : CyclicArc (cellDarts X i),
      K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i) →
    (∃ G₂ : CyclicArc (cellDarts X j),
      K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j) →
      (a.2.boundary.cycle.IsChain fun d e =>
          X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e) ∧
      X.toCombMap.vertexOf
          (X.toCombMap.alpha (a.2.boundary.cycle.getLast a.2.boundary.cycle_nonempty)) =
        X.toCombMap.vertexOf (a.2.boundary.cycle.head a.2.boundary.cycle_nonempty) ∧
      (b.2.boundary.cycle.IsChain fun d e =>
          X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e) ∧
      X.toCombMap.vertexOf
          (X.toCombMap.alpha (b.2.boundary.cycle.getLast b.2.boundary.cycle_nonempty)) =
        X.toCombMap.vertexOf (b.2.boundary.cycle.head b.2.boundary.cycle_nonempty) ∧
      ((∃ d ∈ a.2.boundary.cycle, ∃ e ∈ K.walk,
          X.toCombMap.vertexOf d = X.toCombMap.vertexOf e) ∨
        (a.cellArcList i = [] ∧ a.sideFrom i = [] ∧ a.cellArcList j = [])) ∧
      ((∃ d ∈ b.2.boundary.cycle, ∃ e ∈ K.walk,
          X.toCombMap.vertexOf d = X.toCombMap.vertexOf e) ∨
        (b.cellArcList i = [] ∧ b.cellArcList j = [] ∧ b.sideFrom j = [])) ∧
      a.cellArcList i ⊆ K.firstArc.darts ∧ b.cellArcList i ⊆ K.firstArc.darts ∧
      b.cellArcList j ⊆ K.secondArc.darts ∧ a.cellArcList j ⊆ K.secondArc.darts ∧
      (∀ d ∈ a.sideFrom i, d ∈ K.walk) ∧ (∀ d ∈ b.sideFrom j, d ∈ K.walk)

/-- **Lane gl-p07-02 endpoint.** -/
theorem regionCycleTouch : RegionCycleTouchStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hfirst hsecond h₁ h₂
  exact ⟨regionTouch_cycle_isChain a.2.boundary, regionTouch_cycle_closes a.2.boundary,
    regionTouch_cycle_isChain b.2.boundary, regionTouch_cycle_closes b.2.boundary,
    regionTouch_a hij hai hsecond h₁ h₂, regionTouch_b hij hbi hfirst h₁ h₂,
    (regionTouch_firstArc_subset h₁).1, (regionTouch_firstArc_subset h₁).2,
    (regionTouch_secondArc_subset h₂).1, (regionTouch_secondArc_subset h₂).2,
    fun _ hd => regionTouch_mem_walk_of_mem_secondSide K (by rw [hsecond]; exact hd),
    fun _ hd => regionTouch_mem_walk_of_mem_firstSide K (by rw [hfirst]; exact hd)⟩

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.RegionCycleTouchStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.regionCycleTouch
