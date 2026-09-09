import GroupApproximation.GGT.OsinLemma71Printed
import GroupApproximation.Manuscript.NonMF.TorsionFreePrintedTheorem
import GroupApproximation.Manuscript.NonMF.FournierFacioParagraphFromSimpleFactor
import GroupApproximation.GGT.HullSC
import GroupApproximation.Meta.AxiomGuard

/-!
# `sec:torsion-free` off Hull's Theorem 7.1 as this repository reaches it

`GGT/OsinLemma71PrintedReduction.lean` took the section's endpoints down to one
literature input, `TorsionFreePrinted.HullSmallCancellationPrinted`.  That
statement **cannot be reached from anything in this repository**, and not for
lack of work on the leaves: `thm:hull` as the manuscript prints it carries *no*
torsion-freeness hypothesis, while every form of Hull's theorem the repository
builds carries one —

* `HullSC.HullOneStepStatement` (`GGT/HullSC.lean`),
* `HullSC.HullTowerStatement` (same file),
* `HullSC.TorsionFreeHullCanonicalQuotientStatement`
  (`GGT/HullSCCanonicalQuotientPublished.lean`),
* `TheoremCAssembly`'s `TorsionFree.hullTheorem71`.

So closing all four §5/§6 leaves of Hull's Theorem 7.1 would still leave
`thm:torsion-free` standing on a literature package.  The header of
`Manuscript/NonMF/HullPrintedInputs.lean` records the asymmetry, and
`Manuscript/NonMF/TorsionFreeSectionCitations.lean` names the repair — *"the
section could be run off `HullOneStepStatement` together with
`OsinLemma71Printed` alone … but only after `exists_saturatedQuotient` and the
four statements below are restated over `HullInputsCorrected`"* — and does not
make it, because it would be a change to landed statements.

This module makes it **additively**.  Nothing landed is edited: the printed
statements are re-derived here from a weaker hypothesis, and the existing
theorems keep their types.

## Why nothing is lost

`HullPrintedInputs` reaches the section's proofs through exactly one door,
`HullPrintedInputs.toCorrected`, and the corrected bundle is used at exactly one
group, the `G₀` of the Fournier-Facio paragraph, which is torsion-free
(`FournierFacioParagraph` supplies `IsPowerTorsionFree G₀`).  The extra
hypothesis the printed statement drops is therefore never exercised.  That is
why `PrintedSaturation` — whose own statement already binds
`IsPowerTorsionFree G` — is the right hinge: it is implied by the corrected
bundle directly, with no printed statement in between.

The proofs below are `exists_saturatedQuotient`,
`manuscriptTorsionFreeTheorem` and `manuscriptTorsionFreeFullMFRadicalFromParagraph`
with `hHull` replaced by `hsat : PrintedSaturation` and the single call
`manuscriptSaturation hHull` replaced by `hsat`.  They are duplicated rather
than reused because the originals bind the printed bundle in their types, and
the point of this module is precisely that they do not have to.

## What the section rests on after this module

`thm:torsion-free`, in both printed forms, from the Fournier-Facio paragraph
together with `HullSC.HullOneStepStatement` — Hull's Theorem 7.1 in the
one-relator construction form, which `TheoremCAssembly.TorsionFree.hullOneStep`
already proves modulo the four §5/§6 admissions.  No `HullSmallCancellationPrinted`
and no `OsinLemma71Printed` occur in any hypothesis below: the latter is a
theorem (`GGT.OsinPrinted.osinLemma71Printed`) and is applied here.

`HullSmallCancellationPrinted` stays where it is, as the record of what the
paper cites.  What it stops being is a hypothesis of the section's endpoints.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreePrinted

open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Manuscript.NonMF.TheoremC

universe u

/-! ## The corrected bundle gives `lem:saturation` -/

/-- **`lem:saturation` from the corrected bundle, with no printed statement in
between.**

`manuscriptSaturation` takes `HullPrintedInputs` and immediately forgets it
through `toCorrected`; this is the same theorem at the bundle that call
produces.  The torsion-freeness hypothesis `HullSmallCancellationPrinted` omits
is bound by `PrintedSaturation` itself, so nothing is assumed here that the
printed statement of `lem:saturation` does not already assume. -/
theorem manuscriptSaturation_of_corrected
    (hHull : HullCorrectedInputs.HullInputsCorrected.{u}) :
    PrintedSaturation.{u} := by
  intro G _ _ _ hG N _ hN Ω hΩ
  exact saturation hHull hG N hN hΩ

/-- **Hull's one-relator construction gives the corrected bundle.**

The small-cancellation field is `TheoremCAssembly.TorsionFree.hullTheorem71`'s
own route — the induction on `m` of `HullSC.hullBallFormNG_of_oneStep` followed
by `HullCorrectedInputs.smallCancellation_of_ballFormNG`.  The Osin field needs
no input at all: `GGT.OsinPrinted.osinLemma71Printed` is a theorem. -/
def hullInputsCorrected_of_oneStep (hOne : HullSC.HullOneStepStatement.{0}) :
    HullCorrectedInputs.HullInputsCorrected.{0} where
  smallCancellation :=
    HullCorrectedInputs.smallCancellation_of_ballFormNG
      (HullSC.hullBallFormNG_of_oneStep hOne)
  osinNonElementary :=
    osinNonElementary_of_printed GGT.OsinPrinted.osinLemma71Printed

/-- **`lem:saturation` from Hull's Theorem 7.1 in the form this repository
proves it.** -/
theorem manuscriptSaturation_of_oneStep (hOne : HullSC.HullOneStepStatement.{0}) :
    PrintedSaturation.{0} :=
  manuscriptSaturation_of_corrected (hullInputsCorrected_of_oneStep hOne)

/-! ## The body of the printed proof, over `lem:saturation` -/

/-- **The two middle paragraphs of the printed proof of `thm:torsion-free`**,
over the saturation lemma rather than over the printed citation bundle.

This is `exists_saturatedQuotient` with its literature hypothesis replaced by
the statement that hypothesis was only ever used to produce.  The proof is the
printed one, unchanged. -/
theorem exists_saturatedQuotient_of_saturation (hFFF : FournierFacioParagraph)
    (hsat : PrintedSaturation.{0}) :
    ∃ (Q : Type) (_ : Group Q), IsTwoGenerated Q ∧
      Group.IsFinitelyPresented Q ∧ IsPowerTorsionFree Q ∧
        IsAcylindricallyHyperbolic Q ∧ HasKazhdanPropertyT.{0, 0} Q ∧
          Countable Q ∧
            ∀ (L : Type) (_ : Group L) (r : Q →* L), Function.Surjective r →
              manuscriptCoronaMFResidual L = ⊤ := by
  obtain ⟨G₀, instG₀, hfp, htf, hT, hacyl, F, hΓT, -, -⟩ := hFFF
  letI := instG₀
  haveI := hfp
  haveI := hacyl
  haveI : Countable G₀ := ChiodoBelegradek.countable_of_isFinitelyPresented G₀
  -- "Put `S = tJt⁻¹`. …  Let `N` be the normal closure of `S` in `G₀`; it is
  -- nontrivial because `S` is."
  have hNne : Subgroup.normalClosure (F.conjFactor : Set G₀) ≠ ⊥ :=
    normalClosure_conjFactor_ne_bot F
  -- "By Lemma `lem:saturation` applied to `G₀`, `N`, and `Ω = ∅` …"
  obtain ⟨SQ⟩ := hsat G₀ htf
    (Subgroup.normalClosure (F.conjFactor : Set G₀)) hNne
    (Ω := (∅ : Set G₀)) Set.finite_empty
  haveI : Countable SQ.Q := SQ.surjective.countable
  -- "…and it has property (T) as a quotient of `G₀`."
  have hQT : HasKazhdanPropertyT.{0, 0} SQ.Q :=
    HasKazhdanPropertyT.of_surjective SQ.q SQ.surjective hT
  refine ⟨SQ.Q, inferInstance,
    ⟨SQ.generatorOne, SQ.generatorTwo, SQ.twoGenerated⟩, inferInstance,
    SQ.torsionFree, inferInstance, hQT, inferInstance, ?_⟩
  intro L instL r hr
  letI := instL
  refine coronaMFResidual_eq_top_of_map_normalClosure_eq_top F hΓT hT
    (r.comp SQ.q) (hr.comp SQ.surjective) ?_
  rw [← Subgroup.map_map, SQ.map_eq_top]
  exact Subgroup.map_top_of_surjective r hr

/-! ## The printed theorem, over `lem:saturation` -/

/-- **`thm:torsion-free`, from the Fournier-Facio paragraph and the saturation
lemma.**  The printed proof, with the printed citation bundle removed from the
hypotheses. -/
theorem manuscriptTorsionFreeTheorem_of_saturation
    (hFFF : FournierFacioParagraph) (hsat : PrintedSaturation.{0}) :
    PrintedTorsionFreeTheorem := by
  obtain ⟨Q, instQ, hgen, hfp, htf, hacyl, hQT, hcount, hmain⟩ :=
    exists_saturatedQuotient_of_saturation hFFF hsat
  letI := instQ
  haveI := hcount
  have hQtop : manuscriptCoronaMFResidual Q = ⊤ :=
    hmain Q instQ (MonoidHom.id Q) Function.surjective_id
  have hkill : ∀ (M : Type) (_ : Group M), IsOperatorMF M →
      ∀ (f : Q →* M) (x : Q), f x = 1 := by
    intro M instM hM f x
    letI := instM
    exact OneSidedMFRadical.manuscriptFullRadicalKillsMFTargets Q M hQtop hM f x
  refine ⟨Q, instQ, hgen, hfp, htf, hacyl, hQT, hkill, ?_⟩
  intro L instL r hr hne hMF
  letI := instL
  haveI := hne
  obtain ⟨y, hy⟩ := exists_ne (1 : L)
  obtain ⟨x, rfl⟩ := hr y
  exact hy (hkill L instL hMF r x)

/-- **`thm:torsion-free` in the radical form**, from the same two. -/
theorem manuscriptTorsionFreeFullMFRadical_of_saturation
    (hFFF : FournierFacioParagraph) (hsat : PrintedSaturation.{0}) :
    TheoremC.PrintedTorsionFreeFullMFRadical := by
  obtain ⟨Q, instQ, hgen, hfp, htf, hacyl, hQT, hcount, hmain⟩ :=
    exists_saturatedQuotient_of_saturation hFFF hsat
  letI := instQ
  haveI := hcount
  have hQtop : manuscriptCoronaMFResidual Q = ⊤ :=
    hmain Q instQ (MonoidHom.id Q) Function.surjective_id
  refine ⟨Q, instQ, hgen, hfp, htf, hacyl, hQT, hQtop, ?_, ?_⟩
  · intro L instL r hr _
    exact hmain L instL r hr
  · intro L instL r hr hne hMF
    letI := instL
    haveI := hne
    haveI : Countable L := hr.countable
    have htop := hmain L instL r hr
    have hbot : manuscriptCoronaMFResidual L = ⊥ :=
      isCDEOperatorMF_iff_manuscriptCoronaMFResidual_eq_bot.mp
        ((isCDEOperatorMF_iff_isOperatorMF L).mpr hMF)
    obtain ⟨x, hx⟩ := exists_ne (1 : L)
    apply hx
    have hmem : x ∈ manuscriptCoronaMFResidual L := by
      rw [htop]
      exact Subgroup.mem_top x
    rw [hbot] at hmem
    simpa using hmem

/-! ## The section over Hull's one-relator theorem -/

/-- **`thm:torsion-free` from the Fournier-Facio paragraph and Hull's Theorem
7.1 in the one-relator construction form.**

This is the statement the campaign needs: its Hull input is the one
`TheoremCAssembly.TorsionFree.hullOneStep` proves, so the four §5/§6
admissions are the whole of the open debt.  `HullSmallCancellationPrinted` does
not occur. -/
theorem manuscriptTorsionFreeTheorem_of_oneStep
    (hFFF : FournierFacioParagraph) (hOne : HullSC.HullOneStepStatement.{0}) :
    PrintedTorsionFreeTheorem :=
  manuscriptTorsionFreeTheorem_of_saturation hFFF
    (manuscriptSaturation_of_oneStep hOne)

/-- **`thm:torsion-free` in the radical form, from the same two.** -/
theorem manuscriptTorsionFreeFullMFRadical_of_oneStep
    (hFFF : FournierFacioParagraph) (hOne : HullSC.HullOneStepStatement.{0}) :
    TheoremC.PrintedTorsionFreeFullMFRadical :=
  manuscriptTorsionFreeFullMFRadical_of_saturation hFFF
    (manuscriptSaturation_of_oneStep hOne)

/-- **`thm:torsion-free` over the printed citations of the construction of
`G₀`**, with `thm:hull` traded for the one-relator form.  This is
`manuscriptTorsionFreeTheorem_of_citations_of_smallCancellation`
(`GGT/OsinLemma71PrintedReduction.lean`) with the literature package replaced by
a statement the repository proves. -/
theorem manuscriptTorsionFreeTheorem_of_citations_of_oneStep
    (I : LiteratureInputs) (hW : FinitelyPresentedInfiniteSimpleStatement)
    (hOne : HullSC.HullOneStepStatement.{0}) : PrintedTorsionFreeTheorem :=
  manuscriptTorsionFreeTheorem_of_oneStep
    (fournierFacioParagraph_of_literatureInputs I hW) hOne

/-- **`thm:torsion-free` in the radical form over the printed citations**, from
the same three. -/
theorem manuscriptTorsionFreeFullMFRadical_of_citations_of_oneStep
    (I : LiteratureInputs) (hW : FinitelyPresentedInfiniteSimpleStatement)
    (hOne : HullSC.HullOneStepStatement.{0}) :
    TheoremC.PrintedTorsionFreeFullMFRadical :=
  manuscriptTorsionFreeFullMFRadical_of_oneStep
    (fournierFacioParagraph_of_literatureInputs I hW) hOne

end TorsionFreePrinted
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrinted.manuscriptSaturation_of_corrected
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrinted.hullInputsCorrected_of_oneStep
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrinted.manuscriptSaturation_of_oneStep
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrinted.exists_saturatedQuotient_of_saturation
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrinted.manuscriptTorsionFreeTheorem_of_saturation
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrinted.manuscriptTorsionFreeFullMFRadical_of_saturation
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrinted.manuscriptTorsionFreeTheorem_of_oneStep
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrinted.manuscriptTorsionFreeFullMFRadical_of_oneStep
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrinted.manuscriptTorsionFreeTheorem_of_citations_of_oneStep
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrinted.manuscriptTorsionFreeFullMFRadical_of_citations_of_oneStep
