import GroupApproximation.Manuscript.NonMF.IntroCarto09NFQD
import GroupApproximation.Manuscript.NonMF.IntroCarto10BKQDReduction
import GroupApproximation.Manuscript.NonMF.IntroCarto12NFInclusions
import GroupApproximation.Meta.AxiomGuard

/-!
# NF ⇒ quasidiagonal: the two intro interfaces, closed

Lane `nm-intro-13`, `non_mf_groups_exist.tex` L310--316 (Related work,
Blackadar--Kirchberg). Two in-flight interfaces record the direction
"NF algebras are quasidiagonal":

* `IntroCarto10.NFQuasidiagonalStatement` (`IntroCarto10BKQDReduction`),
* `IntroCarto12.NFImpliesQuasidiagonalStatement` (`IntroCarto12NFInclusions`).

## They are the same proposition

Both unfold to

  `∀ (A : Type u) [CStarAlgebra A], IsNFAlgebra A →
      RelatedTWW.IsQuasidiagonalCStarAlgebra A`,

with `IsNFAlgebra` the finite-local CPC predicate of `Analysis/NFAlgebra.lean`
(the only definition of that name in the repo) and
`RelatedTWW.IsQuasidiagonalCStarAlgebra` the separable-plus-matrix-model
predicate of `RelatedTWW/Definitions.lean`. `IntroCarto12` refers to the latter
unqualified under `open ...RelatedTWW`; the other definition of that name,
`Full.TWWCore.IsQuasidiagonalCStarAlgebra`, lives in a namespace that file does
not open. So `nfqd_statements_iff` is `Iff.rfl`.

## Both are proved

Lane `nm-intro-09` is on disk: `IntroCarto09.nfQuasidiagonal` proves exactly this
universally quantified statement, with no hypotheses. It combines the reduction
`IntroCarto09.isQuasidiagonalCStarAlgebra_of_isNFAlgebra_of_cpBridge` (down maps
of the NF sequence model are the quasidiagonal models) with the proved CP bridge
`IntroCarto09.completelyPositiveOnMatricesBridge`. This module states both
interfaces as closed theorems. There is no remaining gap.

## Truth check

`IsNFAlgebra A` is separability together with, for each finite `F` and `ε > 0`,
CP contractions `down : A → M_Y` and `up : M_Y → A` (with `Y` nonempty) that
recover `F` to within `ε` and make `down` `ε`-multiplicative on `F`.
`IsQuasidiagonalCStarAlgebra A` is separability together with CP contractions
`φₙ : A → M_{kₙ}` that respect `star`, are asymptotically multiplicative and
satisfy `limsup ‖φₙ a‖ = ‖a‖`. Diagonalizing along a dense sequence gives the
`φₙ`, and `‖a‖ - ‖up (down a) - a‖ ≤ ‖down a‖ ≤ ‖a‖` gives norm recovery. The
zero algebra is covered because `Y` is only required to be nonempty and the
maps are contractions, not unital maps. The statement is true.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace IntroCarto13

universe u

/-- **The two NF ⇒ QD interfaces are the same proposition.** Both unfold to
`∀ A, IsNFAlgebra A → RelatedTWW.IsQuasidiagonalCStarAlgebra A`. -/
theorem nfqd_statements_iff :
    IntroCarto10.NFQuasidiagonalStatement.{u} ↔
      IntroCarto12.NFImpliesQuasidiagonalStatement.{u} :=
  Iff.rfl

#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto13.nfqd_statements_iff

/-- **NF ⇒ quasidiagonal, the `IntroCarto10` interface**, closed. It is lane
nm-intro-09's `IntroCarto09.nfQuasidiagonal`. -/
theorem nfqdQuasidiagonalStatement : IntroCarto10.NFQuasidiagonalStatement.{u} :=
  IntroCarto09.nfQuasidiagonal

#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto13.nfqdQuasidiagonalStatement

/-- **NF ⇒ quasidiagonal, the `IntroCarto12` interface**, closed via
`nfqd_statements_iff`. -/
theorem nfqdImpliesQuasidiagonalStatement :
    IntroCarto12.NFImpliesQuasidiagonalStatement.{u} :=
  nfqd_statements_iff.mp nfqdQuasidiagonalStatement

#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto13.nfqdImpliesQuasidiagonalStatement

end IntroCarto13
end NonMF
end Manuscript
end GroupApproximation
