import GroupApproximation.Manuscript.NonMF.IntroCarto09NFQDBridge
import GroupApproximation.Meta.AxiomGuard

/-!
# NF ⇒ quasidiagonal (Blackadar--Kirchberg), unconditional

Lane `nm-intro-09`, `non_mf_groups_exist.tex` L310: every NF algebra, in the
finite-local CPC sense of `Analysis/NFAlgebra.lean`, is quasidiagonal in the
sense of `RelatedTWW.IsQuasidiagonalCStarAlgebra`.

## Proof route

`IntroCarto09.isQuasidiagonalCStarAlgebra_of_isNFAlgebra_of_cpBridge`
(`IntroCarto09NFQDReduction`) builds the quasidiagonal models from the down
maps of the NF sequence model and needs only the CP bridge. The bridge is
proved as `IntroCarto09.completelyPositiveOnMatricesBridge`
(`IntroCarto09NFQDBridge`). Combining the two closes the target with no
hypotheses.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace IntroCarto09

universe u

/-- **NF ⇒ quasidiagonal** (Blackadar--Kirchberg). A separable C⋆-algebra with
finite-local completely positive contractive factorizations through matrix
blocks, with asymptotically multiplicative down maps, is quasidiagonal. -/
theorem isQuasidiagonalCStarAlgebra_of_isNFAlgebra {A : Type u} [CStarAlgebra A]
    (hA : IsNFAlgebra A) : RelatedTWW.IsQuasidiagonalCStarAlgebra A :=
  isQuasidiagonalCStarAlgebra_of_isNFAlgebra_of_cpBridge
    completelyPositiveOnMatricesBridge hA

#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto09.isQuasidiagonalCStarAlgebra_of_isNFAlgebra

/-- **NF ⇒ quasidiagonal**, for all C⋆-algebras in a universe. This is the shape
of `IntroCarto10.NFQuasidiagonalStatement` and
`IntroCarto12.NFImpliesQuasidiagonalStatement`. -/
theorem nfQuasidiagonal :
    ∀ (A : Type u) [CStarAlgebra A], IsNFAlgebra A →
      RelatedTWW.IsQuasidiagonalCStarAlgebra A :=
  fun _ _ hA ↦ isQuasidiagonalCStarAlgebra_of_isNFAlgebra hA

#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto09.nfQuasidiagonal

end IntroCarto09
end NonMF
end Manuscript
end GroupApproximation
