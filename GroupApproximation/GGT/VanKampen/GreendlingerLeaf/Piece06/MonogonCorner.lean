import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.MonogonCornerInner
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.MonogonCornerOuter
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CornerRefineAssemble
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 06: the monogon corner, and gap 5

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  When `σ z = α z` the corner face of `z`
is a monogon.  If it is an inner face, doubling its dart gives the corner digon
(`cornerDigon_inner`).  If it is the exterior, doubling the outer dart gives it too
(`cornerDigon_outer`).  So `MonogonCornerStatement` holds (`monogonCorner`), and with
`CornerRefine.badCornerRefinement_of_monogonCorner` so does `BadCornerRefinementStatement`
(`badCornerRefinement`).

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.MonogonCorner

universe u w v

/-- **The monogon corner.** -/
theorem monogonCorner : CornerRefine.MonogonCornerStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j K z hinv hs _ hσα
  by_cases hfo : X.toCombMap.faceOf (X.toCombMap.alpha z) = X.outerFace
  · exact cornerDigon_outer X K z hinv hfo hσα
  · exact cornerDigon_inner X _ K z hinv rfl hfo hs hσα

/-- **Gap 5: bad corner refinement.** -/
theorem badCornerRefinement : BadCornerRefinementStatement.{u, w, v} :=
  CornerRefine.badCornerRefinement_of_monogonCorner monogonCorner

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.MonogonCorner

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.MonogonCorner.monogonCorner
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.MonogonCorner.badCornerRefinement
