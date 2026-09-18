import GroupApproximation.Manuscript.NonMF.RelatedBK.ConverseReduction
import GroupApproximation.Manuscript.NonMF.RelatedTWW.Elementary
import GroupApproximation.Analysis.NFAlgebra
import GroupApproximation.Meta.AxiomGuard

/-!
# Blackadar--Kirchberg: nuclear and MF gives quasidiagonal, and NF means nuclear and QD

`non_mf_groups_exist.tex`, Related work, tex 312--316:

> Their 1997 paper developed these notions and proved that a separable
> $C^*$-algebra is NF if and only if it is nuclear and MF~\cite{BK}.  It also
> asked whether every separable nuclear stably finite $C^*$-algebra is
> quasidiagonal; ...

For a separable nuclear algebra, "quasidiagonal" and "MF" are the same thing
(Blackadar--Kirchberg 1997, Thm 5.2.2). This module proves the downstream
corollaries of the NF characterization in reduction form:

* `isNFAlgebra_of_isNuclearCStarAlgebra_of_isQuasidiagonalCStarAlgebra_of_localization`:
  nuclear and QD imply NF. QD implies MF (`isMFAlgebra_of_isQuasidiagonalCStarAlgebra`),
  and nuclear and MF imply NF
  (`isNFAlgebra_of_isNuclearCStarAlgebra_of_isMFAlgebra_of_coronaUCPFiniteCoordinateLocalization`).
* `isQuasidiagonalCStarAlgebra_of_nuclear_of_mf_of_localization_of_nfQuasidiagonal`:
  nuclear and MF imply NF, and NF implies QD.
* `isNFAlgebra_iff_nuclear_and_quasidiagonal_of_localization_of_nfQuasidiagonal`:
  NF ⇔ nuclear ∧ QD. The forward half is `IsNFAlgebra.isNuclearCStarAlgebra`
  together with NF ⇒ QD. The backward half is the first bullet.
* `nuclear_and_mf_iff_nuclear_and_quasidiagonal_of_localization_of_nfQuasidiagonal`.

## Upstream interface

NF ⇒ QD is the target of lane nm-intro-09 (`isQuasidiagonalCStarAlgebra_of_isNFAlgebra`),
which runs in parallel and is not on disk yet. It is recorded here as
`NFQuasidiagonalStatement`, a universally quantified form of that target. It is TRUE:
the local NF approximations along a dense sequence give completely positive
contractions into matrices that are asymptotically multiplicative, and they recover
norms because the up maps are contractive. Every theorem that uses it has the
suffix `_of_nfQuasidiagonal`.

The localization gap `RelatedBK.CoronaUCPFiniteCoordinateLocalizationStatement` is
already closed in the corpus (`RelatedBK.coronaUCPFiniteCoordinateLocalization`).
The closed corollaries are in `IntroCarto10BKQDClosed`, so a renamed in-flight
theorem only touches that file.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace IntroCarto10

open GroupApproximation.CStarExactness

universe u

/-- **Upstream interface (lane nm-intro-09): NF algebras are quasidiagonal.**
A unital C⋆-algebra that is NF in the finite-local CPC sense is quasidiagonal in
Voiculescu's abstract sense. This is Blackadar--Kirchberg's NF ⇒ QD. It is true,
and lane nm-intro-09 proves it as `isQuasidiagonalCStarAlgebra_of_isNFAlgebra`. -/
def NFQuasidiagonalStatement : Prop :=
  ∀ (A : Type u) [CStarAlgebra A], IsNFAlgebra A →
    RelatedTWW.IsQuasidiagonalCStarAlgebra A

/-- **Nuclear and quasidiagonal implies NF, modulo localization.** Quasidiagonal
algebras are MF, and nuclear MF algebras are NF. -/
theorem isNFAlgebra_of_isNuclearCStarAlgebra_of_isQuasidiagonalCStarAlgebra_of_localization
    (hloc : RelatedBK.CoronaUCPFiniteCoordinateLocalizationStatement)
    {A : Type u} [CStarAlgebra A]
    (hnuc : IsNuclearCStarAlgebra A) (hQD : RelatedTWW.IsQuasidiagonalCStarAlgebra A) :
    IsNFAlgebra A :=
  RelatedBK.isNFAlgebra_of_isNuclearCStarAlgebra_of_isMFAlgebra_of_coronaUCPFiniteCoordinateLocalization
    hloc hnuc (RelatedTWW.isMFAlgebra_of_isQuasidiagonalCStarAlgebra hQD)

/-- **Nuclear and MF implies quasidiagonal**, modulo localization and NF ⇒ QD.
Nuclear MF algebras are NF, and NF algebras are quasidiagonal. -/
theorem isQuasidiagonalCStarAlgebra_of_nuclear_of_mf_of_localization_of_nfQuasidiagonal
    (hNFQD : NFQuasidiagonalStatement.{u})
    (hloc : RelatedBK.CoronaUCPFiniteCoordinateLocalizationStatement)
    {A : Type u} [CStarAlgebra A]
    (hnuc : IsNuclearCStarAlgebra A) (hMF : IsMFAlgebra A) :
    RelatedTWW.IsQuasidiagonalCStarAlgebra A :=
  hNFQD A
    (RelatedBK.isNFAlgebra_of_isNuclearCStarAlgebra_of_isMFAlgebra_of_coronaUCPFiniteCoordinateLocalization
      hloc hnuc hMF)

/-- **NF means nuclear and quasidiagonal**, modulo localization and NF ⇒ QD. -/
theorem isNFAlgebra_iff_nuclear_and_quasidiagonal_of_localization_of_nfQuasidiagonal
    (hNFQD : NFQuasidiagonalStatement.{u})
    (hloc : RelatedBK.CoronaUCPFiniteCoordinateLocalizationStatement)
    {A : Type u} [CStarAlgebra A] :
    IsNFAlgebra A ↔
      IsNuclearCStarAlgebra A ∧ RelatedTWW.IsQuasidiagonalCStarAlgebra A := by
  constructor
  · intro hA
    exact ⟨hA.isNuclearCStarAlgebra, hNFQD A hA⟩
  · rintro ⟨hnuc, hQD⟩
    exact
      isNFAlgebra_of_isNuclearCStarAlgebra_of_isQuasidiagonalCStarAlgebra_of_localization
        hloc hnuc hQD

/-- **For nuclear algebras, MF and quasidiagonal coincide**, modulo localization
and NF ⇒ QD. -/
theorem nuclear_and_mf_iff_nuclear_and_quasidiagonal_of_localization_of_nfQuasidiagonal
    (hNFQD : NFQuasidiagonalStatement.{u})
    (hloc : RelatedBK.CoronaUCPFiniteCoordinateLocalizationStatement)
    {A : Type u} [CStarAlgebra A] :
    IsNuclearCStarAlgebra A ∧ IsMFAlgebra A ↔
      IsNuclearCStarAlgebra A ∧ RelatedTWW.IsQuasidiagonalCStarAlgebra A := by
  constructor
  · rintro ⟨hnuc, hMF⟩
    exact ⟨hnuc,
      isQuasidiagonalCStarAlgebra_of_nuclear_of_mf_of_localization_of_nfQuasidiagonal
        hNFQD hloc hnuc hMF⟩
  · rintro ⟨hnuc, hQD⟩
    exact ⟨hnuc, RelatedTWW.isMFAlgebra_of_isQuasidiagonalCStarAlgebra hQD⟩

end IntroCarto10
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto10.NFQuasidiagonalStatement
#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto10.isNFAlgebra_of_isNuclearCStarAlgebra_of_isQuasidiagonalCStarAlgebra_of_localization
#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto10.isQuasidiagonalCStarAlgebra_of_nuclear_of_mf_of_localization_of_nfQuasidiagonal
#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto10.isNFAlgebra_iff_nuclear_and_quasidiagonal_of_localization_of_nfQuasidiagonal
#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto10.nuclear_and_mf_iff_nuclear_and_quasidiagonal_of_localization_of_nfQuasidiagonal
