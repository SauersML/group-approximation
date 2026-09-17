import GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf
import GroupApproximation.Meta.AxiomGuard

/-!
# `lem:saturation` and the Fournier-Facio paragraph over the least-area Greendlinger leaf

Lane gl-assembly-06.  `non_mf_groups_exist.tex`, lines 2136–2141:

> **Lemma (saturation).** Let `G` be finitely presented, torsion-free, and acylindrically
> hyperbolic, and let `N ⊴ G` be nontrivial.  Then there is a surjective homomorphism
> `φ : G → Q` such that `Q` is two-generated, finitely presented, torsion-free, and
> acylindrically hyperbolic, and `φ(N) = Q`.

and lines 2160–2170:

> Fournier-Facio constructs a finitely presented torsion-free group `G₀` with property (T), a
> subgroup `Γ ≤ G₀` with property (T), an element `t ∈ G₀` with `tΓt⁻¹ ≤ Γ`, and a subgroup
> `J ≤ G₀` isomorphic to a finitely presented infinite simple group, such that `[Γ,J] = 1` and
> `tJt⁻¹ ≤ Γ` [FFF, §2].  The group `G₀` is obtained there as a common quotient of two finitely
> generated acylindrically hyperbolic groups by Hull's theorem [Hull, Corollary 7.4], which allows
> the quotient to be chosen acylindrically hyperbolic; we take `G₀` to be such a quotient.

## Route

The lane's closed endpoints apply `TorsionFreeGreendlingerLeaf.*_of_greendlinger` to the
unconditional leaf `GGT.VanKampen.GreendlingerLeaf.AsmClose.relativeGreendlingerQuasiGeodesicLeastAreaClosed.{0,0,0}`
(lane gl-assembly-04).  That theorem is **not yet on disk**, so the interface is taken as the
existing Statement `GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}`
(Osin, math/0411039, Lemma 4.4 at least-area van Kampen diagrams; TRUE, the standard relative
Greendlinger lemma).  Every endpoint below is an `_of_greendlinger` reduction with that single
binder.  All other walls (the embedded bridge, Kotowski–Ollivier, Hyde–Lodha) are applied closed
inside `TorsionFreeGreendlingerLeaf`.

`SaturationCarriersStatement` bundles the eight carrier conclusions, and
`saturationCarriers_of_greendlinger` proves it from the leaf, so that once lane gl-assembly-04 lands
each closed endpoint is the projection of
`saturationCarriers_of_greendlinger AsmClose.relativeGreendlingerQuasiGeodesicLeastAreaClosed.{0,0,0}`.

## Manuscript status

Partial on `hgreendlinger` only.
-/

namespace GroupApproximation.Manuscript.NonMF.GreendlingerClosedSaturation

/-- **`lem:saturation` as printed** (tex line 2136), over the least-area Greendlinger leaf. -/
theorem manuscriptSentence_saturation_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TorsionFreePrinted.PrintedSaturationNoOmega.{0} :=
  TorsionFreeGreendlingerLeaf.printedSaturation_of_greendlinger hgreendlinger

#audit_axioms GroupApproximation.Manuscript.NonMF.GreendlingerClosedSaturation.manuscriptSentence_saturation_of_greendlinger

/-- **`lem:saturation` at Osin's notion** (tex line 2136), over the least-area Greendlinger leaf. -/
theorem manuscriptSentence_saturationOsin_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TorsionFreeOsinNotion.PrintedSaturationOsin :=
  TorsionFreeGreendlingerLeaf.printedSaturationOsin_of_greendlinger hgreendlinger

#audit_axioms GroupApproximation.Manuscript.NonMF.GreendlingerClosedSaturation.manuscriptSentence_saturationOsin_of_greendlinger

/-- **`lem:saturation` at the limit-set notion** (tex line 2136), over the least-area Greendlinger
leaf. -/
theorem manuscriptSentence_saturationLimitSet_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TorsionFreeLimitSetNotion.PrintedSaturationLimitSet :=
  TorsionFreeGreendlingerLeaf.printedSaturationLimitSet_of_greendlinger hgreendlinger

#audit_axioms GroupApproximation.Manuscript.NonMF.GreendlingerClosedSaturation.manuscriptSentence_saturationLimitSet_of_greendlinger

/-- **Hull's Corollary 7.4 in the form the Fournier-Facio paragraph uses** (tex line 2165), over
the least-area Greendlinger leaf. -/
theorem manuscriptSentence_hullCommonQuotient_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TheoremC.HullCommonQuotientStatement :=
  TorsionFreeGreendlingerLeaf.hullCommonQuotient_of_greendlinger hgreendlinger

#audit_axioms GroupApproximation.Manuscript.NonMF.GreendlingerClosedSaturation.manuscriptSentence_hullCommonQuotient_of_greendlinger

/-- **The small cancellation quotient of the Fournier-Facio construction** (tex line 2165), over
the least-area Greendlinger leaf. -/
theorem manuscriptSentence_fournierFacioQuotient_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TheoremC.FournierFacioQuotientStatement :=
  TorsionFreeGreendlingerLeaf.fournierFacioQuotient_of_greendlinger hgreendlinger

#audit_axioms GroupApproximation.Manuscript.NonMF.GreendlingerClosedSaturation.manuscriptSentence_fournierFacioQuotient_of_greendlinger

/-- **The literature inputs of the Fournier-Facio paragraph** (tex lines 2160–2170), over the
least-area Greendlinger leaf. -/
theorem manuscriptSentence_literatureInputs_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TheoremC.LiteratureInputs :=
  TorsionFreeGreendlingerLeaf.literatureInputs_of_greendlinger hgreendlinger

#audit_axioms GroupApproximation.Manuscript.NonMF.GreendlingerClosedSaturation.manuscriptSentence_literatureInputs_of_greendlinger

/-- **The configuration of the Fournier-Facio paragraph** (tex lines 2160–2170), over the
least-area Greendlinger leaf. -/
theorem manuscriptSentence_configuration_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    Nonempty TheoremC.Configuration :=
  TorsionFreeGreendlingerLeaf.configuration_of_greendlinger hgreendlinger

#audit_axioms GroupApproximation.Manuscript.NonMF.GreendlingerClosedSaturation.manuscriptSentence_configuration_of_greendlinger

/-- **The Fournier-Facio paragraph, as printed** (tex line 2160), over the least-area Greendlinger
leaf. -/
theorem manuscriptSentence_fournierFacioParagraph_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TorsionFreePrinted.FournierFacioParagraph :=
  TorsionFreeGreendlingerLeaf.fournierFacioParagraph_of_greendlinger hgreendlinger

#audit_axioms GroupApproximation.Manuscript.NonMF.GreendlingerClosedSaturation.manuscriptSentence_fournierFacioParagraph_of_greendlinger

/-- The eight carrier conclusions of lane gl-assembly-06 in one proposition: `lem:saturation` at
the three notions, Hull's Corollary 7.4, the Fournier-Facio quotient, the literature inputs, the
configuration and the printed Fournier-Facio paragraph. -/
def SaturationCarriersStatement : Prop :=
  TorsionFreePrinted.PrintedSaturationNoOmega.{0} ∧
    TorsionFreeOsinNotion.PrintedSaturationOsin ∧
      TorsionFreeLimitSetNotion.PrintedSaturationLimitSet ∧
        TheoremC.HullCommonQuotientStatement ∧
          TheoremC.FournierFacioQuotientStatement ∧
            TheoremC.LiteratureInputs ∧
              Nonempty TheoremC.Configuration ∧
                TorsionFreePrinted.FournierFacioParagraph

/-- **All eight carriers from the least-area Greendlinger leaf.** -/
theorem saturationCarriers_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    SaturationCarriersStatement :=
  ⟨manuscriptSentence_saturation_of_greendlinger hgreendlinger,
    manuscriptSentence_saturationOsin_of_greendlinger hgreendlinger,
    manuscriptSentence_saturationLimitSet_of_greendlinger hgreendlinger,
    manuscriptSentence_hullCommonQuotient_of_greendlinger hgreendlinger,
    manuscriptSentence_fournierFacioQuotient_of_greendlinger hgreendlinger,
    manuscriptSentence_literatureInputs_of_greendlinger hgreendlinger,
    manuscriptSentence_configuration_of_greendlinger hgreendlinger,
    manuscriptSentence_fournierFacioParagraph_of_greendlinger hgreendlinger⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.GreendlingerClosedSaturation.saturationCarriers_of_greendlinger

end GroupApproximation.Manuscript.NonMF.GreendlingerClosedSaturation
