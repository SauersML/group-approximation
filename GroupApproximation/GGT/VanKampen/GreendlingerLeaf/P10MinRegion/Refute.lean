import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseJunctionRefute.Refute
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalRegion
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalWrapBlock
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalWrapCore
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalBlockNoWrap
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalBlock
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalBlockUniform
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalMinimal
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalClass
import GroupApproximation.Meta.AxiomGuard

/-!
# The Piece10Live extremal-region statement is false

Lane gl-p10-89.

LOUD: `P10ExtremalRegion.RoseExtremalRegionStatement` (`Piece10Live/ExtremalRegion`) is FALSE
(at universes `0, 0, 0`).  It is not a weakening of its refuted twin
`P10RoseExtremal.RoseExtremalRegionStatement` (`P10RoseExtremal/Reduction`): the extra premise
`hi ≤ |outerDarts X|` does not save it, because the 24-dart counterexample
`roseJunctionRefute_pK` of lane gl-p10-51 has `hi = 5 ≤ 6 = |outerDarts X|`
(`p10MinRegion_hwrap`).

Proof route, through proved reductions only:
* `P10ExtremalRegion.blockNoWrap_of_extremalRegion`,
  `P10ExtremalWrap.contigResidualNoWrap_of_blockNoWrap`,
  `P10ExtremalWrap.extremalCoreNoWrap_of_contigResidualNoWrap` take the target to
  `P10ExtremalWrap.RoseExtremalCoreNoWrapStatement`;
* that statement has the clauses of `P10RoseExtremalTrim.RoseExtremalJunctionStatement` minus
  the clause `∃ y ∈ cycle, ...`, which the refutation never used, plus the premise `hwrap`;
* `roseJunctionRefute_noWitness` closes it on the pocket, as in `roseJunctionRefute_not_junction`.

Also FALSE by the same chain: `RoseExtremalBlockNoWrapStatement`,
`RoseExtremalBlockNoWrapCoreStatement`, `RoseExtremalContigResidualNoWrapStatement`,
`RoseExtremalCoreNoWrapStatement`, `P10ExtremalResidual.RoseExtremalBlockStatement`,
`P10ExtremalBlock.RoseExtremalBlockCoreStatement`,
`P10ExtremalResidual.ExtremalBlockUniformStatement` and
`P10ExtremalRegion.ExtremalMinimalUniformStatement`.

Manuscript status: counterexample/infrastructure for thm:hull.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf

open OsinPocketPinchedTwoGonModel (D)

/-- **No wrap on the counterexample**: `hi = 5` is at most the length `6` of the outer cycle. -/
theorem p10MinRegion_hwrap : 5 ≤ (Embedded.outerDarts roseJunctionRefute_X).length :=
  (by decide : (5 : ℕ) ≤ 6).trans_eq (congrArg List.length roseJunctionRefute_outerDarts).symm

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.p10MinRegion_hwrap

/-- **`RoseExtremalCoreNoWrapStatement` is false**, on the 24-dart pocket `roseJunctionRefute_pK`
(the argument of `roseJunctionRefute_not_junction`, with the premise `p10MinRegion_hwrap`). -/
theorem p10MinRegion_not_coreNoWrap :
    ¬P10ExtremalWrap.RoseExtremalCoreNoWrapStatement.{0, 0, 0} := by
  intro h
  obtain ⟨r, hrout, source, kept, hsource, hkept, t₁, t₂, s₁, s₂, hperm, _, hs₁c, hs₂c, hj₁,
    hj₂, hj₃, hs₁, hs₂, _, hhi, ht₁, _⟩ := h D 1 roseJunctionRefute_X 0 5 p10MinRegion_hwrap
      roseJunctionRefute_leastArea roseJunctionRefute_letters roseJunctionRefute_pK
      roseJunctionRefute_closedWalk roseJunctionRefute_notFirst roseJunctionRefute_srcLt
      roseJunctionRefute_tgtLt roseJunctionRefute_notUnpinched roseJunctionRefute_allCrossed
  exact roseJunctionRefute_noWitness r hrout source kept hsource hkept t₁ t₂ s₁ s₂ hperm
    (P10RoseExtremalTrim.isChain_listing_of_junctions t₁ t₂ hs₁c hs₂c hj₁ hj₂ hj₃) hj₂ hj₃
    hs₁ hs₂ hhi ht₁

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.p10MinRegion_not_coreNoWrap

/-- **`RoseExtremalContigResidualNoWrapStatement` is false.** -/
theorem p10MinRegion_not_contigResidualNoWrap :
    ¬P10ExtremalWrap.RoseExtremalContigResidualNoWrapStatement.{0, 0, 0} := fun h =>
  p10MinRegion_not_coreNoWrap (P10ExtremalWrap.extremalCoreNoWrap_of_contigResidualNoWrap h)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.p10MinRegion_not_contigResidualNoWrap

/-- **`RoseExtremalBlockNoWrapStatement` is false.** -/
theorem p10MinRegion_not_blockNoWrap :
    ¬P10ExtremalWrap.RoseExtremalBlockNoWrapStatement.{0, 0, 0} := fun h =>
  p10MinRegion_not_contigResidualNoWrap (P10ExtremalWrap.contigResidualNoWrap_of_blockNoWrap h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.p10MinRegion_not_blockNoWrap

/-- **`RoseExtremalBlockNoWrapCoreStatement` is false.** -/
theorem p10MinRegion_not_noWrapCore :
    ¬P10ExtremalBlock.RoseExtremalBlockNoWrapCoreStatement.{0, 0, 0} := fun h =>
  p10MinRegion_not_blockNoWrap (P10ExtremalBlock.blockNoWrap_of_noWrapCore h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.p10MinRegion_not_noWrapCore

/-- **LOUD: the Piece10Live `RoseExtremalRegionStatement` is false**, although it carries the
premise `hi ≤ |outerDarts X|` that its refuted twin `P10RoseExtremal.RoseExtremalRegionStatement`
lacks. -/
theorem p10MinRegion_not_extremalRegion :
    ¬P10ExtremalRegion.RoseExtremalRegionStatement.{0, 0, 0} := fun h =>
  p10MinRegion_not_blockNoWrap (P10ExtremalRegion.blockNoWrap_of_extremalRegion h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.p10MinRegion_not_extremalRegion

/-- **`RoseExtremalBlockStatement` is false** (it has no wrap premise, so it implies the no-wrap
block statement). -/
theorem p10MinRegion_not_block : ¬P10ExtremalResidual.RoseExtremalBlockStatement.{0, 0, 0} :=
  fun h => p10MinRegion_not_blockNoWrap (P10ExtremalWrap.blockNoWrap_of_block h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.p10MinRegion_not_block

/-- **`RoseExtremalBlockCoreStatement` is false.** -/
theorem p10MinRegion_not_blockCore :
    ¬P10ExtremalBlock.RoseExtremalBlockCoreStatement.{0, 0, 0} := fun h =>
  p10MinRegion_not_block (P10ExtremalBlock.roseExtremalBlock_of_core h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.p10MinRegion_not_blockCore

/-- **`ExtremalBlockUniformStatement` is false** (route (b) of the frontier is dead). -/
theorem p10MinRegion_not_blockUniform :
    ¬P10ExtremalResidual.ExtremalBlockUniformStatement.{0, 0, 0} := fun h =>
  p10MinRegion_not_block (P10ExtremalResidual.roseExtremalBlock_of_extremalBlockUniform h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.p10MinRegion_not_blockUniform

/-- **`ExtremalMinimalUniformStatement` is false** (route (c) of the frontier is dead). -/
theorem p10MinRegion_not_minimalUniform :
    ¬P10ExtremalRegion.ExtremalMinimalUniformStatement.{0, 0, 0} := fun h =>
  p10MinRegion_not_extremalRegion (P10ExtremalRegion.roseExtremalRegion_of_extremalClass
    (P10ExtremalRegion.roseExtremalClass_of_extremalMinimalUniform h))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.p10MinRegion_not_minimalUniform

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf
