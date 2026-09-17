import GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf
import GroupApproximation.Manuscript.NonMF.TorsionFreeAlgebraSentencesClosed
import GroupApproximation.Manuscript.NonMF.RegularNonMFAlgebra
import GroupApproximation.Sofic.ChiodoBelegradekTheorem
import GroupApproximation.Analysis.ReducedGroupCStarMFAlgebra
import GroupApproximation.Sofic.CDEOperatorMF
import GroupApproximation.Meta.AxiomGuard

/-!
# The torsion-free endpoints of `non_mf_groups_exist.tex`, reduced to Greendlinger

Lane GL07.  This module covers the torsion-free endpoints of `non_mf_groups_exist.tex`:

* abstract, tex 78–79: *"... and a finitely presented torsion-free group with property (T) and
  no nontrivial homomorphism to an MF group."*  This is `AbstractTorsionFreeClause`.
* Introduction, tex 292–293, second half: *"The last group has none."*  This is
  `IntroLastGroupHasNone`.
* `thm:torsion-free`, tex 295–301.  This is `TorsionFreePrinted.PrintedTorsionFreeTheorem`, with
  its Osin and limit-set variants.
* Introduction, tex 303–305: *"Its reduced C*-algebra is simple, has a unique tracial state and
  stable rank one, and is not MF."*  This is `IntroReducedAlgebraSentence`.  It is stated at the
  same group `Q` as the theorem.
* `sec:torsion-free`: `thm:hull`, `lem:saturation`, the Fournier-Facio paragraph and
  `cor:regular-nonmf-algebra`, each with its Osin and limit-set variants where they exist.

## What is proved here

* `*_of_printedTorsionFreeTheorem` derives each introduction or abstract sentence from the
  printed theorem.  These proofs need no Greendlinger input: they use only the seven printed
  clauses and closed theorems of the repository.
* `*_of_greendlinger` states each endpoint with exactly one binder:
  `GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}`.  That binder is
  Osin's Lemma 4.4 at least-area diagrams, the relative Greendlinger lemma.
* `TorsionFreeEndpoints` bundles every zero-parameter endpoint.  `torsionFreeEndpoints_of_greendlinger`
  proves the bundle from the one binder.

## Verification of the reductions

`TorsionFreeGreendlingerLeaf` applies `TorsionFreeFourLeaves` to three closed producers:

* `HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed`;
* `KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed`;
* `HydeLodha.finitelyPresentedInfiniteSimple_closed`.

The Dahmani–Guirardel–Osin and Gerasimova–Osin citations are closed in
`TorsionFreeAlgebraSentencesClosed`.  No `FournierFacioParagraph` or `HullPrintedInputs` binder
survives: `FournierFacioParagraph` appears below only as a conclusion.

The unconditional endpoints are obtained by applying these theorems to the relative Greendlinger
theorem of lane GL06, once it lands.
-/

namespace GroupApproximation
namespace Full
namespace TorsionFreeEndpoints

open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted
open GroupApproximation.ReducedGroupCStarTrace

/-! ## The sentences outside `sec:torsion-free` -/

/-- **Abstract, tex 78–79, second half.**

> We also construct ... a finitely presented torsion-free group with property (T) and no
> nontrivial homomorphism to an MF group.

"Torsion-free" is stated in its literal form: the only element of finite order is the identity.
The conjunct `Infinite Q` is added so that the statement cannot hold vacuously at the trivial
group. -/
def AbstractTorsionFreeClause : Prop :=
  ∃ (Q : Type) (_ : Group Q),
    Group.IsFinitelyPresented Q ∧ Infinite Q ∧ (∀ g : Q, IsOfFinOrder g → g = 1) ∧
      HasKazhdanPropertyT.{0, 0} Q ∧
        ∀ (M : Type) (_ : Group M), IsOperatorMF M → ∀ f : Q →* M, f = 1

/-- **Introduction, tex 292–293, second half.**

> Every example above has torsion, and in the lamp construction the obstruction is itself a
> torsion element.  The last group has none.

"The last group" is the group `Q` of `thm:torsion-free`.  The statement names `Q` by all seven
printed clauses of that theorem.  It then records the contrast the sentence draws: `Q` is
infinite, every element of `Q` lies in the obstruction because every homomorphism to an MF group
kills it, and no nontrivial element has finite order. -/
def IntroLastGroupHasNone : Prop :=
  ∃ (Q : Type) (_ : Group Q),
    IsTwoGenerated Q ∧ Group.IsFinitelyPresented Q ∧ IsPowerTorsionFree Q ∧
      IsAcylindricallyHyperbolic Q ∧ HasKazhdanPropertyT.{0, 0} Q ∧
        (∀ (M : Type) (_ : Group M), IsOperatorMF M →
          ∀ (f : Q →* M) (x : Q), f x = 1) ∧
        (∀ (L : Type) (_ : Group L) (r : Q →* L), Function.Surjective r →
          Nontrivial L → ¬ IsOperatorMF L) ∧
        Infinite Q ∧ ∀ g : Q, IsOfFinOrder g → g = 1

/-- **Introduction, tex 303–305.**

> Its reduced C*-algebra is simple, has a unique tracial state and stable rank one, and is not
> MF.

"Its" refers to the group `Q` of `thm:torsion-free`.  The statement therefore carries the seven
printed clauses of the theorem and the four algebraic clauses of the sentence at the same `Q`. -/
def IntroReducedAlgebraSentence : Prop :=
  ∃ (Q : Type) (_ : Group Q),
    IsTwoGenerated Q ∧ Group.IsFinitelyPresented Q ∧ IsPowerTorsionFree Q ∧
      IsAcylindricallyHyperbolic Q ∧ HasKazhdanPropertyT.{0, 0} Q ∧
        (∀ (M : Type) (_ : Group M), IsOperatorMF M →
          ∀ (f : Q →* M) (x : Q), f x = 1) ∧
        (∀ (L : Type) (_ : Group L) (r : Q →* L), Function.Surjective r →
          Nontrivial L → ¬ IsOperatorMF L) ∧
        IsSimpleCStar (ReducedGroupCStar Q) ∧
          HasUniqueTracialState (ReducedGroupCStar Q) ∧
            IsStableRankOne (ReducedGroupCStar Q) ∧
              ¬ IsMFAlgebra (ReducedGroupCStar Q)

/-! ## Reductions to `thm:torsion-free`, with no Greendlinger input -/

/-- `thm:torsion-free` gives the torsion-free clause of the abstract. -/
theorem abstractTorsionFreeClause_of_printedTorsionFreeTheorem
    (h : PrintedTorsionFreeTheorem) : AbstractTorsionFreeClause := by
  obtain ⟨Q, instQ, -, hfp, htf, hacyl, hT, hkill, -⟩ := h
  letI := instQ
  haveI := hacyl
  refine ⟨Q, instQ, hfp, infinite_of_acylHyperbolic Q, ?_, hT, ?_⟩
  · intro g hg
    by_contra hne
    exact IsPowerTorsionFree.not_isOfFinOrder htf hne hg
  · intro M instM hM f
    refine MonoidHom.ext fun x => ?_
    rw [MonoidHom.one_apply]
    exact hkill M instM hM f x

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.abstractTorsionFreeClause_of_printedTorsionFreeTheorem

/-- `thm:torsion-free` gives "The last group has none". -/
theorem introLastGroupHasNone_of_printedTorsionFreeTheorem
    (h : PrintedTorsionFreeTheorem) : IntroLastGroupHasNone := by
  obtain ⟨Q, instQ, hgen, hfp, htf, hacyl, hT, hkill, hquot⟩ := h
  letI := instQ
  haveI := hacyl
  refine ⟨Q, instQ, hgen, hfp, htf, hacyl, hT, hkill, hquot,
    infinite_of_acylHyperbolic Q, ?_⟩
  intro g hg
  by_contra hne
  exact IsPowerTorsionFree.not_isOfFinOrder htf hne hg

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.introLastGroupHasNone_of_printedTorsionFreeTheorem

/-- **`thm:torsion-free` gives tex 303–305 at the same group.**

The steps are:

* `Q` is finitely presented, hence countable (`ChiodoBelegradek.countable_of_isFinitelyPresented`).
* `Q` is acylindrically hyperbolic, hence nontrivial.  So the identity quotient is a nontrivial
  quotient of `Q`, and the last clause of the theorem says `Q` is not MF.
* Simplicity, the unique trace and stable rank one come from
  `manuscriptSentence_algebraSimpleUniqueTraceStableRank_closed`, where the Dahmani–Guirardel–Osin
  and Gerasimova–Osin citations are proved.
* "Not MF" for the algebra comes from `reducedGroupCStar_separable_stablyFinite_not_isMFAlgebra`,
  applied to the literal Carrión–Dadarlat–Eckhardt predicate through
  `isCDEOperatorMF_iff_isOperatorMF`. -/
theorem introReducedAlgebraSentence_of_printedTorsionFreeTheorem
    (h : PrintedTorsionFreeTheorem) : IntroReducedAlgebraSentence := by
  obtain ⟨Q, instQ, hgen, hfp, htf, hacyl, hT, hkill, hquot⟩ := h
  letI := instQ
  haveI := hfp
  haveI := hacyl
  haveI : Countable Q := ChiodoBelegradek.countable_of_isFinitelyPresented Q
  haveI hnt : Nontrivial Q := nontrivial_of_acylHyperbolic Q
  have hnotOp : ¬ IsOperatorMF Q :=
    hquot Q instQ (MonoidHom.id Q) Function.surjective_id hnt
  have hnotCDE : ¬ IsCDEOperatorMF Q := fun hCDE =>
    hnotOp ((isCDEOperatorMF_iff_isOperatorMF Q).mp hCDE)
  obtain ⟨hsimple, htrace, hsr⟩ :=
    Manuscript.NonMF.TorsionFreePrintedSentences.manuscriptSentence_algebraSimpleUniqueTraceStableRank_closed
      Q htf
  obtain ⟨-, -, hnotMF⟩ := reducedGroupCStar_separable_stablyFinite_not_isMFAlgebra Q hnotCDE
  exact ⟨Q, instQ, hgen, hfp, htf, hacyl, hT, hkill, hquot, hsimple, htrace, hsr, hnotMF⟩

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.introReducedAlgebraSentence_of_printedTorsionFreeTheorem

/-! ## The same sentences over the one Greendlinger binder -/

/-- Abstract, tex 78–79, from the relative Greendlinger lemma alone. -/
theorem abstractTorsionFreeClause_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    AbstractTorsionFreeClause :=
  abstractTorsionFreeClause_of_printedTorsionFreeTheorem
    (Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedTorsionFreeTheorem_of_greendlinger
      hgreendlinger)

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.abstractTorsionFreeClause_of_greendlinger

/-- Introduction, tex 292–293, from the relative Greendlinger lemma alone. -/
theorem introLastGroupHasNone_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    IntroLastGroupHasNone :=
  introLastGroupHasNone_of_printedTorsionFreeTheorem
    (Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedTorsionFreeTheorem_of_greendlinger
      hgreendlinger)

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.introLastGroupHasNone_of_greendlinger

/-- Introduction, tex 303–305, from the relative Greendlinger lemma alone. -/
theorem introReducedAlgebraSentence_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    IntroReducedAlgebraSentence :=
  introReducedAlgebraSentence_of_printedTorsionFreeTheorem
    (Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedTorsionFreeTheorem_of_greendlinger
      hgreendlinger)

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.introReducedAlgebraSentence_of_greendlinger

/-! ## Every zero-parameter torsion-free endpoint, bundled -/

/-- **Every zero-parameter torsion-free endpoint of `non_mf_groups_exist.tex`.**

The conjuncts, in order:

1. `thm:torsion-free` at Hull's notion, Osin's notion and the limit-set notion (tex 295–301).
2. `thm:hull`, at the three notions.
3. `lem:saturation`, at the three notions.
4. The Fournier-Facio paragraph.
5. `cor:regular-nonmf-algebra`, at the three notions.
6. Abstract tex 78–79, and the introduction at tex 292–293 and tex 303–305. -/
def TorsionFreeEndpoints : Prop :=
  PrintedTorsionFreeTheorem ∧
    Manuscript.NonMF.TorsionFreeOsinNotion.PrintedTorsionFreeTheoremOsin ∧
    Manuscript.NonMF.TorsionFreeLimitSetNotion.PrintedTorsionFreeTheoremLimitSet ∧
    Manuscript.NonMF.TorsionFreeSectionSentences.PrintedHullSmallCancellationCurrent.{0} ∧
    Manuscript.NonMF.TorsionFreeOsinNotion.PrintedHullSmallCancellationOsin ∧
    Manuscript.NonMF.TorsionFreeLimitSetNotion.PrintedHullSmallCancellationLimitSet ∧
    PrintedSaturationNoOmega.{0} ∧
    Manuscript.NonMF.TorsionFreeOsinNotion.PrintedSaturationOsin ∧
    Manuscript.NonMF.TorsionFreeLimitSetNotion.PrintedSaturationLimitSet ∧
    FournierFacioParagraph ∧
    PrintedRegularNonMFAlgebra ∧
    Manuscript.NonMF.TorsionFreeOsinNotion.PrintedRegularNonMFAlgebraOsin ∧
    Manuscript.NonMF.TorsionFreeLimitSetNotion.PrintedRegularNonMFAlgebraLimitSet ∧
    AbstractTorsionFreeClause ∧ IntroLastGroupHasNone ∧ IntroReducedAlgebraSentence

/-- The bundle of every zero-parameter torsion-free endpoint, from the relative Greendlinger
lemma alone. -/
theorem torsionFreeEndpoints_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TorsionFreeEndpoints :=
  ⟨Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedTorsionFreeTheorem_of_greendlinger
      hgreendlinger,
    Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedTorsionFreeTheoremOsin_of_greendlinger
      hgreendlinger,
    Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedTorsionFreeTheoremLimitSet_of_greendlinger
      hgreendlinger,
    Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedHullTheorem_of_greendlinger hgreendlinger,
    Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedHullTheoremOsin_of_greendlinger
      hgreendlinger,
    Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedHullTheoremLimitSet_of_greendlinger
      hgreendlinger,
    Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedSaturation_of_greendlinger hgreendlinger,
    Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedSaturationOsin_of_greendlinger
      hgreendlinger,
    Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedSaturationLimitSet_of_greendlinger
      hgreendlinger,
    Manuscript.NonMF.TorsionFreeGreendlingerLeaf.fournierFacioParagraph_of_greendlinger
      hgreendlinger,
    Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedRegularNonMFAlgebra_of_greendlinger
      hgreendlinger,
    Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedRegularNonMFAlgebraOsin_of_greendlinger
      hgreendlinger,
    Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedRegularNonMFAlgebraLimitSet_of_greendlinger
      hgreendlinger,
    abstractTorsionFreeClause_of_greendlinger hgreendlinger,
    introLastGroupHasNone_of_greendlinger hgreendlinger,
    introReducedAlgebraSentence_of_greendlinger hgreendlinger⟩

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.torsionFreeEndpoints_of_greendlinger

end TorsionFreeEndpoints
end Full
end GroupApproximation
