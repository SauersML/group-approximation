import GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.FournierFacioQuotient
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Assembly
import GroupApproximation.Meta.AxiomGuard

/-!
# Fournier-Facio's `G₀` as Hull's Corollary 7.4 common quotient, closed

`non_mf_groups_exist.tex`, lines 2160–2170:

> Fournier-Facio constructs a finitely presented torsion-free group `G₀` with property (T), a
> subgroup `Γ ≤ G₀` with property (T), an element `t ∈ G₀` with `tΓt⁻¹ ≤ Γ`, and a subgroup
> `J ≤ G₀` isomorphic to a finitely presented infinite simple group, such that `[Γ, J] = 1` and
> `tJt⁻¹ ≤ Γ` [FFF, §2].  The group `G₀` is obtained there as a common quotient of two finitely
> generated acylindrically hyperbolic groups by Hull's theorem [Hull, Corollary 7.4], which allows
> the quotient to be chosen acylindrically hyperbolic; we take `G₀` to be such a quotient.

Census rows `8097c371f35d` (Fournier-Facio constructs `G₀`) and `dab2f2bfe084` (`G₀` as Hull's
Corollary 7.4 common quotient).  Lane nm-torsionfree-03.

## Route

`TorsionFreeClosed.FournierFacioQuotient` proves each form over the single binder
`hgreendlinger : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}`
(the other walls, Osin's Lemma 5.1 embedded, Kotowski–Ollivier and Hyde–Lodha's `Q₂`, are already
discharged there by closed producers).  Every endpoint here applies the matching `_of_greendlinger`
theorem to the binder-free, universe-polymorphic leaf closer

  `GGT.VanKampen.GreendlingerLeaf.relativeGreendlingerQuasiGeodesicLeastArea`

(`GreendlingerLeaf/Assembly.lean`), instantiated at `.{0, 0, 0}`, the universes the reductions fix.

## Manuscript status

Every endpoint is a closed proposition audited with `#audit_closed_axioms`.  The rows are closed
once `GreendlingerLeaf/Assembly.lean` and its `Piece<NN>/Proof` imports build.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreeClosed

/-- **Hull's Corollary 7.4, in the form the Fournier-Facio paragraph uses** (lines 2165–2169). -/
theorem manuscriptSentence_hullCommonQuotient : TheoremC.HullCommonQuotientStatement :=
  manuscriptSentence_hullCommonQuotient_of_greendlinger
    GGT.VanKampen.GreendlingerLeaf.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

/-- **The small cancellation quotient of the Fournier-Facio construction** (lines 2160–2169). -/
theorem manuscriptSentence_fournierFacioQuotient : TheoremC.FournierFacioQuotientStatement :=
  manuscriptSentence_fournierFacioQuotient_of_greendlinger
    GGT.VanKampen.GreendlingerLeaf.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

/-- **The Fournier-Facio paragraph, as printed** (lines 2160–2165). -/
theorem manuscriptSentence_fournierFacioParagraph : TorsionFreePrinted.FournierFacioParagraph :=
  manuscriptSentence_fournierFacioParagraph_of_greendlinger
    GGT.VanKampen.GreendlingerLeaf.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

/-- **The configuration of the Fournier-Facio paragraph** (lines 2160–2170): `G₀` taken as an
acylindrically hyperbolic common quotient. -/
theorem theoremC_configuration : Nonempty TheoremC.Configuration :=
  theoremC_configuration_of_greendlinger
    GGT.VanKampen.GreendlingerLeaf.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

/-- **The literature inputs of the Fournier-Facio paragraph**, `TheoremC.LiteratureInputs`. -/
theorem theoremC_literatureInputs : TheoremC.LiteratureInputs :=
  theoremC_literatureInputs_of_greendlinger
    GGT.VanKampen.GreendlingerLeaf.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

/-- **The Fournier-Facio rows, bundled** (census rows `8097c371f35d`, `dab2f2bfe084`). -/
theorem fournierFacioRows : FournierFacioRows :=
  fournierFacioRows_of_greendlinger
    GGT.VanKampen.GreendlingerLeaf.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

end TorsionFreeClosed
end NonMF
end Manuscript
end GroupApproximation

#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.manuscriptSentence_hullCommonQuotient
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.manuscriptSentence_fournierFacioQuotient
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.manuscriptSentence_fournierFacioParagraph
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.theoremC_configuration
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.theoremC_literatureInputs
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.fournierFacioRows
