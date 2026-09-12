import GroupApproximation.GGT.DGOProposition414General
import GroupApproximation.GGT.DGOLemma421FromUniform414
import GroupApproximation.GGT.HullYiCyclicProductClosure
import GroupApproximation.GGT.HullYiFiniteFamilyInduction
import GroupApproximation.GGT.HullSCLemma44QuasiGeodesicBridge
import GroupApproximation.GGT.HullSCRelativeGreendlingerQuasiGeodesicSpelling
import GroupApproximation.GGT.HullSCRelativeGreendlingerSpelling
import GroupApproximation.GGT.HullSCRelativeExteriorArcConversion
import GroupApproximation.GGT.HullSCLemma49PowerDiagramFromComponents
import GroupApproximation.GGT.HullSCLemma49PowerDiagram
import GroupApproximation.GGT.HullSCCanonicalQuotientPublished
import GroupApproximation.GGT.HullSCFillingSelectionTheorem316
import GroupApproximation.GGT.HullSCAuxiliaryRelatorPublished
import GroupApproximation.Manuscript.NonMF.TorsionFreeSaturationFromCorrected
import GroupApproximation.Manuscript.NonMF.RegularNonMFAlgebra
import GroupApproximation.Manuscript.NonMF.OsinTheorem12NonDegenerate
import GroupApproximation.Meta.AxiomGuard

/-!
# `sec:torsion-free`, assembled over its named open leaves

`non_mf_groups_exist.tex`, Section `sec:torsion-free` (tex lines 1621–1737):
`thm:hull`, `lem:saturation`, the proof of `thm:torsion-free`, and
`cor:regular-nonmf-algebra`.

This module runs the section along its printed route, with every open input a
**named statement taken as a hypothesis of an intermediate lemma**, never a
literature package bound at an endpoint and never an admission.  It does not
import `TheoremCAssembly`, whose admissions are `sorry`s; the derivations below
spell out the chain over hypotheses instead.

## The leaves

* `GGT.VanKampen.RelativeGreendlingerQuasiGeodesicStatement` — Osin's §9
  relative Greendlinger lemma at quasi-geodesic boundaries.  It replaces the two
  estimating admissions of `TheoremCAssembly` (`estimatingSelectionConstruction`,
  `estimatingUnboundOutput`): both were only ever spent through it, by the waists
  `HullSC.relativeGreendlingerQuasiGeodesicSpellingStatement_of_greendlinger` and
  `HullSC.hullLemma49ShortestGeodesicPowerDiagramStatement_of_greendlinger`.
* `HullSC.RelativeIsoperimetricBridgeQuasiGeodesicStatement` — Osin's Lemma 5.1
  at its own boundary hypothesis.  This spelling is the one the landed Lemma 4.4
  chain consumes.  Its conclusion `RelativeIsoperimetricControl` asks for more
  than any consumer reads (only `control.embedded` is used), and the refinement
  to a bounded Lemma 4.4 input with an embedded-family conclusion is in
  progress; the leaf is re-spelled here once that chain lands.
* `TorsionFreePrinted.FournierFacioParagraph` — the paragraph of tex lines
  1675–1685: `G₀`, `Γ`, `t`, `J` with the printed relations, `G₀`
  acylindrically hyperbolic.
* `TorsionFreePrinted.SimpleUniqueTraceAtHypEmbedded` — Dahmani–Guirardel–Osin,
  Theorem 2.35, `(a) ⇒ (d) ∧ (e)`, at its source hypothesis (a non-degenerate
  hyperbolically embedded subgroup).  Osin's Theorem 1.2, the printed bridge to
  it, is proved (`TorsionFreePrinted.exists_isNonDegenerate_isHypEmbedded`).
* `TorsionFreePrinted.GerasimovaOsinTheorem11Printed` — Gerasimova–Osin,
  Theorem 1.1.

Hull's Theorem 7.1, and with it `thm:hull` and `lem:saturation`, needs only the
first two: the canonical Lemma 4.4 comes from the certificate and the bridge
(`HullSC.hullLemma44CanonicalQuotientStatement_of_quasiGeodesic`), with no §6
re-spelling, which survives only on the Fournier-Facio side.

Everything between these and the printed conclusions is proved here or already
on main.  When producers of the leaves land, the endpoints below become closed
one-line corollaries.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreeLeafAssembly

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted
open GroupApproximation.ReducedGroupCStarTrace
open GroupApproximation.GroupVonNeumann

/-! ## Hull's Theorem 7.1 at one target, from the two Hull leaves -/

/-- **Hull's Corollary 5.7 in its all-`m` form, closed.**  DGO Proposition 4.14
with the uniform constant gives Lemma 4.21(b), which gives the local
finite-avoidance producer, and the proved finite induction gives the family. -/
theorem hullYiSuitableFiniteFamily_closed : HullSC.YiSuitableFiniteFamily.{0} :=
  HullSC.yiSuitableFiniteFamily_iff_pairAvoidingFiniteOneSided.mpr
    (HullSC.yiSuitablePairAvoidingFiniteOneSided_of_dgoLemma421b
      (GGT.OsinComponents.dgoLemma421b_of_uniform414
        GGT.OsinComponents.dgoProposition414Uniform))

/-- **Osin's Lemma 4.4 in certificate form at quasi-geodesic spellings**, from
the Greendlinger leaf; the realization at a supplied spelling and the one-cell
exterior-arc conversion are theorems. -/
theorem relativeGreendlingerQuasiGeodesicSpelling_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicStatement.{0, 0, 0}) :
    HullSC.RelativeGreendlingerQuasiGeodesicSpellingStatement.{0, 0} :=
  HullSC.relativeGreendlingerQuasiGeodesicSpellingStatement_of_greendlinger
    hgreendlinger HullSC.relativeDiscRealizationSpellingStatement
    HullSC.relativeExteriorArcConversionAtWordRotatedStatement

/-- **Hull's Lemma 4.4 for the selected family**, from the certificate and
Osin's Lemma 5.1, with no §6 re-spelling. -/
theorem hullLemma44Canonical_of_leaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicStatement.{0, 0, 0}) :
    HullSC.HullLemma44CanonicalQuotientStatement.{0} :=
  HullSC.hullLemma44CanonicalQuotientStatement_of_quasiGeodesic
    (relativeGreendlingerQuasiGeodesicSpelling_of_greendlinger hgreendlinger) hbridge

/-- **Hull's Lemma 4.9, kernel-power correction**, from the Greendlinger leaf
alone. -/
theorem hullLemma49KernelPower_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicStatement.{0, 0, 0}) :
    HullSC.HullLemma49KernelPowerStatement.{0, 0} :=
  HullSC.hullLemma49KernelPowerStatement_of_geodesicPowerDiagram
    (HullSC.hullLemma49ShortestGeodesicPowerDiagramStatement_of_greendlinger
      hgreendlinger HullSC.relativeDiscRealizationSpellingStatement
      HullSC.relativeExteriorArcConversionAtWordRotatedStatement)

/-- **Hull's Theorem 7.1 for one target element**, over a torsion-free group,
from the two Hull leaves: the canonical quotient `G ⧸ ⟨⟨W⟩⟩` of Lemmas 4.4 and
4.9, with Hull's §6 relator transported into the selected auxiliary family.
This is `TheoremCAssembly.TorsionFree.hullOneStep` with its admissions replaced
by the two named leaves. -/
theorem hullOneStep_of_leaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicStatement.{0, 0, 0}) :
    HullSC.HullOneStepStatement.{0} :=
  HullSC.AuxiliaryPeripheralFamily.hullOneStep_of_canonicalQuotient
    (HullSC.torsionFreeHullCanonicalQuotientStatement_of_lemma44_of_lemma49
      (HullSC.simultaneousAuxiliaryPeripheralSelection_of_finiteYi_theorem316
        hullYiSuitableFiniteFamily_closed)
      (hullLemma44Canonical_of_leaves hgreendlinger hbridge)
      (hullLemma49KernelPower_of_greendlinger hgreendlinger))

/-! ## `thm:hull` and `lem:saturation`, over the leaves -/

/-- **`thm:hull` as printed, at a torsion-free ambient group**, from the two
Hull leaves, through the induction on `m` (`HullSC.hullBallFormNG_of_oneStep`). -/
theorem hullSmallCancellationTorsionFreePrinted_of_leaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicStatement.{0, 0, 0}) :
    HullSmallCancellationTorsionFreePrinted.{0} :=
  hullSmallCancellationTorsionFreePrinted_of_oneStep
    (hullOneStep_of_leaves hgreendlinger hbridge)

/-- **`lem:saturation` as printed** (tex line 1650), from the two Hull leaves;
Osin's Lemma 7.1 and Hull's Corollary 5.7 with Lemma 5.8 are theorems. -/
theorem printedSaturationNoOmega_of_leaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicStatement.{0, 0, 0}) :
    PrintedSaturationNoOmega.{0} :=
  manuscriptSaturationNoOmega_of_torsionFreePrinted
    (hullSmallCancellationTorsionFreePrinted_of_leaves hgreendlinger hbridge)

/-! ## `thm:torsion-free`, over the leaves -/

/-- **`thm:torsion-free`, exactly as printed** (tex line 284), along the printed
proof, from the Fournier-Facio paragraph and the two Hull leaves. -/
theorem manuscriptTorsionFreeTheorem_of_leaves (hFFF : FournierFacioParagraph)
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicStatement.{0, 0, 0}) :
    PrintedTorsionFreeTheorem :=
  manuscriptTorsionFreeTheorem_of_torsionFreePrinted hFFF
    (hullSmallCancellationTorsionFreePrinted_of_leaves hgreendlinger hbridge)

/-- **`thm:torsion-free` in the radical form**, from the same three. -/
theorem manuscriptTorsionFreeFullMFRadical_of_leaves (hFFF : FournierFacioParagraph)
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicStatement.{0, 0, 0}) :
    TheoremC.PrintedTorsionFreeFullMFRadical :=
  manuscriptTorsionFreeFullMFRadical_of_torsionFreePrinted hFFF
    (hullSmallCancellationTorsionFreePrinted_of_leaves hgreendlinger hbridge)

/-! ## `cor:regular-nonmf-algebra`, over the printed saturation lemma -/

/-- **`cor:regular-nonmf-algebra`, from `lem:saturation` as printed.**

> The algebra `C*_r(Q)` is separable, unital, simple, and generated by two
> unitaries.  It has a unique tracial state and stable rank one, and it is
> stably finite but not MF.

and its proof (tex lines 1724–1736):

> The group `Q` is countable, torsion-free, and acylindrically hyperbolic, so it
> contains a non-degenerate hyperbolically embedded subgroup [Osin, Theorem 1.2]
> and has no nontrivial finite normal subgroup.  Dahmani, Guirardel, and Osin
> give simplicity and uniqueness of the trace [DGO, Theorem 2.35], and
> Gerasimova and Osin give density of the invertible elements, which is stable
> rank one [GO, Theorem 1.1].  The algebra is separable and generated by the
> canonical unitaries of the two generators; its canonical trace is faithful, so
> it is stably finite; and it is not MF by Lemma `prop:mf-residual-calculus`,
> since `Q` is not MF (Theorem `thm:torsion-free`).

This is `TorsionFreePrinted.manuscriptRegularNonMFAlgebra` with the printed
citation bundle for Hull replaced by the saturation lemma it was only used to
produce, and with Dahmani–Guirardel–Osin taken at their own hypothesis: Osin's
Theorem 1.2 is applied, as printed, through
`dgoTheorem235Printed_of_hypEmbedded`. -/
theorem manuscriptRegularNonMFAlgebra_of_saturationNoOmega
    (hFFF : FournierFacioParagraph) (hsat : PrintedSaturationNoOmega.{0})
    (hDGO : SimpleUniqueTraceAtHypEmbedded)
    (hGO : GerasimovaOsinTheorem11Printed) : PrintedRegularNonMFAlgebra := by
  obtain ⟨Q, instQ, hgen, -, htfQ, hacylQ, -, hcountQ, hmain⟩ :=
    exists_saturatedQuotient_of_saturationNoOmega hFFF hsat
  letI := instQ
  haveI := hcountQ
  haveI := hacylQ
  haveI : Nontrivial Q := nontrivial_of_acylHyperbolic Q
  -- "…and has no nontrivial finite normal subgroup."
  have hrad : HasTrivialFiniteRadical Q :=
    hasTrivialFiniteRadical_of_torsionFree htfQ
  -- "…since `Q` is not MF (Theorem `thm:torsion-free`)."
  have hQtop : manuscriptCoronaMFResidual Q = ⊤ :=
    hmain Q instQ (MonoidHom.id Q) Function.surjective_id
  have hnotMF : ¬ IsCDEOperatorMF Q := by
    intro hMF
    have hbot : manuscriptCoronaMFResidual Q = ⊥ :=
      isCDEOperatorMF_iff_manuscriptCoronaMFResidual_eq_bot.mp hMF
    obtain ⟨x, hx⟩ := exists_ne (1 : Q)
    apply hx
    have hmem : x ∈ manuscriptCoronaMFResidual Q := by
      rw [hQtop]
      exact Subgroup.mem_top x
    rw [hbot] at hmem
    simpa using hmem
  -- "The algebra is separable…; its canonical trace is faithful, so it is
  -- stably finite; and it is not MF…"
  obtain ⟨hsep, hsf, hnotMFalg⟩ :=
    reducedGroupCStar_separable_stablyFinite_not_isMFAlgebra Q hnotMF
  -- "…so it contains a non-degenerate hyperbolically embedded subgroup [Osin,
  -- Theorem 1.2]…  Dahmani, Guirardel, and Osin give simplicity and uniqueness
  -- of the trace."
  obtain ⟨hsimple, huniq⟩ := dgoTheorem235Printed_of_hypEmbedded hDGO Q hrad
  -- "…and Gerasimova and Osin give density of the invertible elements."
  have hsr : IsStableRankOne (ReducedGroupCStar Q) := hGO Q hrad
  obtain ⟨g₁, g₂, hg₁₂⟩ := hgen
  refine ⟨Q, instQ, hcountQ, htfQ, hacylQ, ⟨g₁, g₂, hg₁₂⟩, hsep, ?_,
    ⟨g₁, g₂, hg₁₂, unitary_leftRegularOperator Q g₁,
      unitary_leftRegularOperator Q g₂, topologicalClosure_adjoin_pair hg₁₂⟩,
    hsimple, huniq, hsr, hsf, hnotMFalg⟩
  -- "unital": the unit of the algebra is not zero.
  intro hone
  obtain ⟨a, b, hab⟩ := exists_pair_ne (ReducedGroupCStar Q)
  apply hab
  have hzero : ∀ x : ReducedGroupCStar Q, x = 0 := by
    intro x
    calc x = x * 1 := (mul_one x).symm
      _ = x * 0 := by rw [hone]
      _ = 0 := mul_zero x
  rw [hzero a, hzero b]

/-- **`cor:regular-nonmf-algebra`, along the printed proof**, from the
Fournier-Facio paragraph, the two Hull leaves, Dahmani–Guirardel–Osin's Theorem
2.35 at its source hypothesis, and Gerasimova–Osin's Theorem 1.1. -/
theorem manuscriptRegularNonMFAlgebra_of_leaves (hFFF : FournierFacioParagraph)
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicStatement.{0, 0, 0})
    (hDGO : SimpleUniqueTraceAtHypEmbedded)
    (hGO : GerasimovaOsinTheorem11Printed) : PrintedRegularNonMFAlgebra :=
  manuscriptRegularNonMFAlgebra_of_saturationNoOmega hFFF
    (printedSaturationNoOmega_of_leaves hgreendlinger hbridge) hDGO hGO

end TorsionFreeLeafAssembly
end NonMF
end Manuscript
end GroupApproximation

#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeLeafAssembly.hullYiSuitableFiniteFamily_closed
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeLeafAssembly.relativeGreendlingerQuasiGeodesicSpelling_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeLeafAssembly.hullLemma44Canonical_of_leaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeLeafAssembly.hullLemma49KernelPower_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeLeafAssembly.hullOneStep_of_leaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeLeafAssembly.hullSmallCancellationTorsionFreePrinted_of_leaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeLeafAssembly.printedSaturationNoOmega_of_leaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeLeafAssembly.manuscriptTorsionFreeTheorem_of_leaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeLeafAssembly.manuscriptTorsionFreeFullMFRadical_of_leaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeLeafAssembly.manuscriptRegularNonMFAlgebra_of_saturationNoOmega
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeLeafAssembly.manuscriptRegularNonMFAlgebra_of_leaves
