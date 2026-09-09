import GroupApproximation.Sofic.ActualCoronaMFRadical
import GroupApproximation.Sofic.NormMFCoronaRadical
import GroupApproximation.Sofic.NormMFUniversalQuotient
import GroupApproximation.Sofic.NormMFUniversalCorona
import GroupApproximation.Sofic.CDEOperatorMF
import GroupApproximation.Analysis.ReducedGroupCStarMFAlgebra
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedDefinitions
import GroupApproximation.Meta.AxiomGuard

/-!
# Sentence-level formalization of `non_mf_groups_exist.tex`, Introduction, lines 1-352

The abstract and the Introduction of `non_mf_groups_exist.tex` are already
covered sentence by sentence almost everywhere: `IntroductionClaimSentences.lean`,
`SentenceAbstractClosure.lean`, `PrintedDefinitions.lean`, `PrintedCriterion.lean`,
`PrintedDefect.lean`, `KazhdanTransportSentences.lean`, `NormalKazhdanSentences.lean`,
`FullDefectRingSentences.lean`, `FullDefectRingEJZUnconditional.lean`,
`UnitGroupHeadline.lean`, `AmenableTraceTheorem.lean`,
`PriorWorkConnesEmbedding.lean` and `Criterion/CompressionCentralizerDefect.lean`
between them already carry a landed declaration for the overwhelming majority
of printed sentences in this range.  This module supplies the printed
sentences that remained genuinely without a carrier after that census pass:

* the printed formula for the MF radical, `Rad_MF(G) = ⋂{ker f : f : G → M,
  M an MF group}`, as a literal membership equivalence with
  `manuscriptCoronaMFResidual`, whose own definition instead intersects over
  representations into genuine norm-matrix coronas;
* "For countable `G` the quotient `G/Rad_MF(G)` is again MF, and hence the
  largest MF quotient of `G`", restated with `Rad_MF(G) = manuscriptCoronaMFResidual G`
  in place of the development's internal `normMFResidual`/`normMFQuotient`,
  which the printed radical formula above identifies with it; and
* "A positive answer [to the MF problem] would make every countable group
  MF, because the reduced group `C^*`-algebra is separable and stably
  finite", formalized as the conditional it is printed as.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMFSentences

open OneSidedMFRadical

noncomputable section

/-! ## Introduction: `10e027681ba5`

"Write `Rad_{MF}(G) = ⋂{ker f : f : G → M, M an MF group}` for the *MF
radical* of `G`." -/

/-- **The printed MF-radical formula, literally.**  `manuscriptCoronaMFResidual`
(`Sofic.ActualCoronaMFRadical`) is already the intersection of the kernels of
every representation into a genuine norm-matrix corona with coordinates
`M_(d_n)(ℂ)` (`ManuscriptCoronaMFInvisible`).  This restates membership in it
as intersection of the kernels of homomorphisms into MF *groups* themselves,
exactly as printed: an element is invisible to every corona representation
iff it is killed by every homomorphism to a countable MF group, because the
image of a corona homomorphism is itself a countable MF group
(`coronaImage_countable`, `coronaImage_isOperatorMF`), and conversely an MF
group's own defining embedding, precomposed with any homomorphism into it, is
a corona homomorphism. -/
def PrintedMFRadicalFormula : Prop :=
  ∀ (G : Type) [Group G] [Countable G] (x : G),
    x ∈ manuscriptCoronaMFResidual G ↔
      ∀ (M : Type) [Group M] [Countable M], IsCDEOperatorMF M →
        ∀ f : G →* M, f x = 1

theorem manuscriptSentence_mfRadicalFormula :
    PrintedMFRadicalFormula := by
  intro G _ _ x
  rw [mem_manuscriptCoronaMFResidual_iff]
  constructor
  · intro hx M _ _ hM f
    obtain ⟨d, hd, -, rho, hrho⟩ := hM
    letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
      fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
    have hcomp := hx d hd (rho.comp f)
    have hker : rho (f x) = 1 := by simpa using hcomp
    exact hrho (hker.trans (map_one rho).symm)
  · intro h d hd rho
    letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
      fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
    have hX : ∀ n, 0 < Fintype.card (naturalFiniteModel (d n)) :=
      fun n ↦ by simpa using hd n
    letI : Countable rho.range := OneSidedMFRadical.coronaImage_countable G _ rho
    have hMF : IsCDEOperatorMF rho.range :=
      (isCDEOperatorMF_iff_isOperatorMF rho.range).mpr
        (OneSidedMFRadical.coronaImage_isOperatorMF G _ hX rho)
    have hval := h rho.range hMF rho.rangeRestrict
    exact congrArg Subtype.val hval

#audit_closed_axioms
  GroupApproximation.Manuscript.NonMFSentences.manuscriptSentence_mfRadicalFormula

/-! ## Introduction: `07de7e8a943a` + `8e54f4138ac7`

"For countable `G` the quotient `G/Rad_{MF}(G)` is again MF, and hence the
largest MF quotient of `G`: enumerate its nontrivial elements and separate
each by an MF model, and at stage `n` take the direct sum of the first `n`
models, each carried far enough along its own sequence to have multiplicative
defect below `1/n` on the first `n` elements while still separating its own
element.  This family is asymptotically multiplicative and separates every
nontrivial element." -/

/-- **The printed quotient sentence, literally.**  A quotient of `G` realizes
`Rad_{MF}(G)` as its kernel, is itself operator-norm MF, and every
homomorphism from `G` to a countable operator-norm MF group factors uniquely
through it.  The witness is `Q := normMFQuotient G` along its canonical map
`q := normMFQuotientMk G`; the kernel identity chases `normMFQuotientMk_ker`
through `manuscriptCoronaMFResidual_eq_coronaMFResidual` and
`coronaMFResidual_eq_normMFResidual`, so that the printed `Rad_MF(G)` and the
development's internal `normMFResidual G` name the same subgroup.  The
diagonal block-sum construction described in the printed colon clause --
carrying each of the first `n` detectors far enough along its own sequence
for multiplicative defect below `1/n` on the first `n` marked elements, so
that the resulting family is asymptotically multiplicative and separates
every nontrivial element -- is exactly the internal construction inside the
proof of `normMFQuotient_isOperatorMF` in `Sofic.NormMFUniversalCorona`; it is
consumed here as a completed fact and is not re-exposed as a separate
declaration, since the printed sentence states no fact about that
construction beyond the conclusion this proposition already gives. -/
def PrintedMFRadicalQuotientIsMFAndLargest : Prop :=
  ∀ (G : Type) [Group G] [Countable G],
    ∃ (Q : Type) (_ : Group Q) (q : G →* Q),
      q.ker = manuscriptCoronaMFResidual G ∧ Function.Surjective q ∧
        IsOperatorMF Q ∧
          ∀ (H : Type) [Group H] [Countable H] (f : G →* H), IsOperatorMF H →
            ∃! fBar : Q →* H, fBar.comp q = f

theorem manuscriptSentence_mfRadicalQuotientIsMFAndLargest :
    PrintedMFRadicalQuotientIsMFAndLargest := by
  intro G _ _
  refine ⟨normMFQuotient G, inferInstance, normMFQuotientMk G, ?_, ?_, ?_, ?_⟩
  · rw [normMFQuotientMk_ker, manuscriptCoronaMFResidual_eq_coronaMFResidual,
      coronaMFResidual_eq_normMFResidual]
  · exact QuotientGroup.mk'_surjective (normMFResidual G)
  · exact normMFQuotient_isOperatorMF
  · intro H _ _ f hH
    exact existsUnique_normMFQuotient_factorization_to_isOperatorMF f hH

#audit_closed_axioms
  GroupApproximation.Manuscript.NonMFSentences.manuscriptSentence_mfRadicalQuotientIsMFAndLargest

/-! ## Related work: `6edef6dc2d68`

"A positive answer would make every countable group MF, because the reduced
group `C^*`-algebra is separable and stably finite; Lubotzky--Oppenheim and,
separately, Thom noted this when they listed operator norm approximation of
groups among the open approximation problems~[LubotzkyOppenheim,Thom]." -/

/-- **The printed conditional, literally.**  The sentence is itself
conditional ("a positive answer *would* make"), so a conditional theorem is
the faithful formalization: if every separable stably finite `C^*`-algebra
has a faithful embedding into a norm matrix corona (a positive answer to the
MF problem for `C^*`-algebras, in the paper's own separable convention, see
`IntroductionSeparableCStarAlgebraIsMFDef`), then every countable group is
MF, because its reduced group `C^*`-algebra is separable and stably finite
(`reducedGroupCStar_separable_stablyFinite`) and an MF embedding of it
restricts, along the faithful left regular unitary representation, to a
corona embedding of the group itself
(`isCDEOperatorMF_of_hasMFEmbedding_reducedGroupCStar`).  The attribution
clause crediting Lubotzky--Oppenheim and Thom with this observation is not a
mathematical assertion and carries no proof obligation of its own. -/
def PrintedPositiveMFProblemAnswerMakesEveryCountableGroupMF : Prop :=
  (∀ (A : Type) [CStarAlgebra A],
      TopologicalSpace.SeparableSpace A → IsStablyFiniteCStarAlgebra A →
        HasMFEmbedding A) →
    ∀ (G : Type) [Group G] [Countable G], IsCDEOperatorMF G

theorem manuscriptSentence_positiveMFProblemAnswerMakesEveryCountableGroupMF :
    PrintedPositiveMFProblemAnswerMakesEveryCountableGroupMF := by
  intro hpos G _ _
  obtain ⟨hsep, hsf⟩ := reducedGroupCStar_separable_stablyFinite G
  exact isCDEOperatorMF_of_hasMFEmbedding_reducedGroupCStar G (hpos _ hsep hsf)

#audit_closed_axioms
  GroupApproximation.Manuscript.NonMFSentences.manuscriptSentence_positiveMFProblemAnswerMakesEveryCountableGroupMF

end
end NonMFSentences
end Manuscript
end GroupApproximation
