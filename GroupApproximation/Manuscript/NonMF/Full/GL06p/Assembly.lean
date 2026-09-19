import GroupApproximation.Manuscript.NonMF.Full.GL06p.NearestPath
import GroupApproximation.Manuscript.NonMF.Full.GL06h4.NearestShortPocket
import GroupApproximation.Meta.AxiomGuard

/-!
# GL06p: the all-cells residual from the slit pocket of a nearest path

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b), the all-cells case.  Infrastructure for
`thm:hull` (non_mf_groups_exist.tex ~2121, Hull's small cancellation theorem, through Osin's
Lemma 9.7).  Step 5 of lane nm-gl06e's construction.

GL06h4's residual `gl06h4Nearest_shortPocketStatement` asks for the slit pocket
`gl06h4Nearest_Pocket` from scratch.  Osin builds it in two moves: first choose a nearest cell
`Π` and a minimal path `p` from `∂Δ` to `∂Π`, then cut `Δ` along `p` and around `Π`.  The first
move is proved (`GL06p.exists_nearestCellPath`).  The residual here,
`slitPocketOfNearestPathStatement`, is the second move alone: it receives the nearest cell and
the minimal path as an input.

* `slitPocketOfNearestPathStatement`: the cut, given the nearest path (steps 2 to 4).
* `shortPocket_of_slitPocketOfNearestPath`: GL06h4's residual follows, by
  `exists_nearestCellPath`.
* `allCellsShort_of_slitPocketOfNearestPath`: and so GL06e's residual
  `AllCellsShortEnclosedRefutedBelowSectionStatement`.

## Strength

`slitPocketOfNearestPathStatement` is implied by GL06h4's residual (ignore the input).  The
converse is `shortPocket_of_slitPocketOfNearestPath`.  So the two are equivalent.  This module
only removes the choice of `Π` and `p` from what remains to be proved.

## Manuscript status

Infrastructure for `thm:hull` (non_mf_groups_exist.tex ~2121); certifies no printed sentence on
its own.  `slitPocketOfNearestPathStatement` is a combinatorial clause of Osin's proof, not a
literature statement.
-/

namespace GroupApproximation.Full.GL06p

universe u w v

open GroupApproximation.GGT
open GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.WordMetric

/-- **The slit pocket of a nearest path** (Osin, proof of Lemma 9.7(b); `thm:hull`,
non_mf_groups_exist.tex ~2121): cutting `Δ` along a minimal path to a nearest cell gives the slit
pocket of GL06h4. -/
def slitPocketOfNearestPathStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) (Delta : DiscDiagram.{u, w, v} W),
    Delta.LeastArea → (∀ d, (symmetricLabelAlphabet D).IsLetter (Delta.label d)) →
      (∀ word ∈ W, 1 < word.length) → 2 ≤ Delta.rCellCount →
        Delta.boundaryWord.length ≤ eps + eps →
          NearestCellPath Delta →
            Nonempty (GL06h4.gl06h4Nearest_Pocket D eps Delta)

#audit_axioms GroupApproximation.Full.GL06p.slitPocketOfNearestPathStatement

/-- **GL06h4's residual from the slit pocket of a nearest path** (Osin, proof of Lemma 9.7(b);
`thm:hull`, non_mf_groups_exist.tex ~2121): a nearest cell and a minimal path always exist. -/
theorem shortPocket_of_slitPocketOfNearestPath
    (h : slitPocketOfNearestPathStatement.{u, w, v}) :
    GL06h4.gl06h4Nearest_shortPocketStatement.{u, w, v} := by
  intro _G _ _Lambda D eps W Delta hlea hletters hW hcells hboundary
  exact h D eps W Delta hlea hletters hW hcells hboundary
    (exists_nearestCellPath Delta (by omega)).some

#audit_axioms GroupApproximation.Full.GL06p.shortPocket_of_slitPocketOfNearestPath

/-- **GL06e's all-cells residual from the slit pocket of a nearest path** (Osin, proof of
Lemma 9.7(b); `thm:hull`, non_mf_groups_exist.tex ~2121). -/
theorem allCellsShort_of_slitPocketOfNearestPath
    (h : slitPocketOfNearestPathStatement.{u, w, v}) :
    GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement.{u, w, v} :=
  GL06h4.gl06h4Nearest_allCellsShort_of_shortPocket (shortPocket_of_slitPocketOfNearestPath h)

#audit_axioms GroupApproximation.Full.GL06p.allCellsShort_of_slitPocketOfNearestPath

end GroupApproximation.Full.GL06p
