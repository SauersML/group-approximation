import GroupApproximation.Computability.ExactSwitchAlgorithmicConsequences
import GroupApproximation.Computability.MFRecognitionSecondLevel
import GroupApproximation.Manuscript.MFRecognition.HNNPermanence
import GroupApproximation.Manuscript.MFRecognition.NegativeBranch
import GroupApproximation.Manuscript.MFRecognition.PositiveBranch

/-!
# `thm:recognition`: MF recognition is `Π⁰₂`-complete

> **Main Theorem (MF recognition is `Π⁰₂`-complete).**  Deciding whether a
> finite presentation defines an MF group is `Π⁰₂`-complete, and the
> complementary problem is `Σ⁰₂`-complete.  In particular, it is impossible to
> construct an algorithm that decides from a finite presentation whether the
> group it defines is MF, or even one that enumerates the presentations of MF
> groups or those of non-MF groups.  There is a computable map
> `e ↦ R̂_e` such that `R̂_e` presents an MF group if and only if the `e`-th
> partial computable function has infinite domain.
>
> *Proof.*  By `lem:finite-rope` the map `e ↦ R̂_e` is computable, by
> `lem:positive-branch` the presented group is MF for `e ∈ INF`, and by
> `lem:negative-branch` it is not MF for `e ∈ FIN`.  So `INF` reduces to
> `MF_fp` and `FIN` reduces to `NONMF_fp` under computable many-one
> reductions.  Since `INF` is `Π⁰₂`-complete and `FIN` is `Σ⁰₂`-complete, and
> since `MF_fp ∈ Π⁰₂` and `NONMF_fp ∈ Σ⁰₂` by `prop:mf-upper-bound`, the two
> sets are complete at their levels.  A `Π⁰₂`-complete set is not `Σ⁰₂` and a
> `Σ⁰₂`-complete set is not `Π⁰₂`, so neither set is recursively enumerable,
> and in particular neither is decidable.

Everything after the three lemma citations is already in the repository:
`prop:mf-upper-bound` is `MFRecognitionPi02.operatorMFCode_pi02`, and the
reduction bookkeeping is `HereditaryPropertySwitchCompleteness`, whose
`FinitePresentationSwitchCompiler` is precisely "a computable `e ↦ R̂_e` with
`R̂_e` MF iff `e ∈ INF`".  So the only new content here is

* `RecognitionFamily` --- that datum, in the manuscript's own words.  It is
  the explicit hypothesis of every conditional theorem below: nothing here
  asserts it.  Its `code` and `computable_code` fields are what the landed
  `FiniteRope` (`lem:finite-rope`) and `EffectiveHigmanCompiler` produce, and
  its `negative` and `positive` fields are the two branch lemmas;
* `recognitionFamily_of_inputs` --- the assembly point, taking the remaining
  HNN-permanence theorem as a leading binder;
* `mfPresentations_not_re` --- **`MF_fp ∉ RE`**, which the repository did not
  yet carry for finite presentations (it carried `NONMF_fp ∉ RE`
  unconditionally, and `MF_fp ∉ RE` only for enumerated codes).  The proof is
  the printed one: a `Π⁰₂`-complete set is not `Σ⁰₂`, so it is not `Σ⁰₁`; in
  the effective form used here, the `Π⁰₂` set `NonhaltsZero` many-one reduces
  to `MF_fp`, and `NonhaltsZero` is not RE.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace Recognition

open ArithmeticalHierarchy
open GroupApproximation.SecondLevelIndexSets
open GroupApproximation.PresentationCodes
open GroupApproximation.MFRecognitionSecondLevel

/-! ## 0.  The analytic citation, from the HNN-permanence lane's bundle -/

/-- **One hypothesis, not two.**

The two statements the "Consequently" clause of `lem:tensor-sync` consumes are
both already among the ones the `hnn-permanence` lane bundles: that lane's
`manuscriptHNNPermanence` *is* `thm:hnn-permanence`, in the very binder order
the tensor-sync bundle asks for, and its `unitalCoronaEmbedding` field is
literally `UnitalCoronaEmbeddingStatement`, the same proposition.  So a caller
holding the single `HNNPermanence.HNNInputs` needs no second hypothesis to
build the family below. -/
theorem hnnPermanenceInputs_of_hnnInputs (hIn : HNNPermanence.HNNInputs) :
    TensorSynchronization.HNNPermanenceInputs where
  hnnPermanence := by
    intro G _ _ S T phi A _ realization X _ iota hiota W hW
    exact HNNPermanence.manuscriptHNNPermanence hIn phi realization iota hiota W hW

/-! ## 1.  The computable family `e ↦ R̂_e` -/

/-- **The datum the proof of `thm:recognition` opens with**: a computable map
`e ↦ R̂_e` into finite presentations whose group is not MF for `e ∈ FIN`
(`lem:negative-branch`) and is MF for `e ∈ INF` (`lem:positive-branch`). -/
structure RecognitionFamily : Type where
  /-- The code of the finite presentation `R̂_e` of `eq:finite-rope`. -/
  code : Nat.Partrec.Code → PresentationCode
  /-- **`lem:finite-rope`.**  "A code of the finite presentation
  `eq:finite-rope` is computable from `e`." -/
  computable_code : Computable code
  /-- **`lem:negative-branch`.**  "For `e ∈ FIN`, the group `R̂_e` is not
  MF." -/
  negative : ∀ c, FiniteDomain c → ¬ IsOperatorMF (Carrier (code c))
  /-- **`lem:positive-branch`.**  "for `e ∈ INF`, `lem:positive-branch` proves
  that it is MF." -/
  positive : ∀ c, InfiniteDomain c → IsOperatorMF (Carrier (code c))

/-- **The two branch lemmas produce the family.**  The negative branch gives
`negative` and the positive branch gives `positive`; computability of the code
is `lem:finite-rope`. -/
def recognitionFamily_of_inputs
    (hIn : TensorSynchronization.HNNPermanenceInputs)
    (code : Nat.Partrec.Code → PresentationCode) (hcode : Computable code)
    (H C F P Qplus Q K0 : Nat.Partrec.Code → Type)
    [∀ e, Group (H e)] [∀ e, Group (C e)] [∀ e, Group (F e)]
    [∀ e, Group (P e)] [∀ e, Group (Qplus e)] [∀ e, Group (Q e)]
    [∀ e, Group (K0 e)]
    (D : ∀ e, RecognitionInputs e (H e) (C e) (F e) (P e) (Qplus e) (Q e)
      (K0 e) (Carrier (code e))) :
    RecognitionFamily where
  code := code
  computable_code := hcode
  negative := fun c hfin => not_isOperatorMF_Rhat (D c) hfin
  positive := fun c hinf => (manuscriptPositiveBranch hIn (D c) hinf).2

/-- The family is exactly the repository's finite-output switch compiler for
operator-MF, so every second-level consequence already proved for such a
compiler applies to it. -/
def manuscriptMFCompiler (R : RecognitionFamily) : MFCompiler where
  compile := R.code
  computable_compile := R.computable_code
  correct := by
    intro c
    show IsOperatorMF (Carrier (R.code c)) ↔ InfiniteDomain c
    constructor
    · intro hMF
      by_contra hinf
      have hfin : FiniteDomain c := by
        simpa only [FiniteDomain, InfiniteDomain, Set.not_infinite] using hinf
      exact R.negative c hfin hMF
    · intro hinf
      exact R.positive c hinf

/-! ## 2.  The clauses of `thm:recognition` -/

/-- **"`MF_fp ∈ Π⁰₂` by finite certificates."**  `prop:mf-upper-bound`. -/
theorem mfPresentations_pi02 : Pi02 MFCode := MFRecognitionSecondLevel.mfCode_pi02

/-- **"`NONMF_fp ∈ Σ⁰₂`."**  `prop:mf-upper-bound`, complemented. -/
theorem nonMFPresentations_sigma02 : Sigma02 NonMFCode :=
  MFRecognitionSecondLevel.nonMFCode_sigma02

/-- **"Deciding whether a finite presentation defines an MF group is
`Π⁰₂`-complete."** -/
theorem mfPresentations_pi02Complete (R : RecognitionFamily) :
    Pi02Complete MFCode :=
  mfCode_pi02Complete_of_compiler (manuscriptMFCompiler R)

/-- **"and the complementary problem is `Σ⁰₂`-complete."** -/
theorem nonMFPresentations_sigma02Complete (R : RecognitionFamily) :
    Sigma02Complete NonMFCode :=
  nonMFCode_sigma02Complete_of_compiler (manuscriptMFCompiler R)

/-- **"it is impossible to construct an algorithm that decides from a finite
presentation whether the group it defines is MF".**  This clause is
unconditional in the repository. -/
theorem mfPresentations_not_computable : ¬ ComputablePred MFCode :=
  MFRecognitionImpossible.mf_recognition_not_computable

/-- The Boolean-decider restatement of the previous clause. -/
theorem no_mfPresentations_decider :
    ¬ ∃ f : PresentationCode → Bool, Computable f ∧ ∀ c, f c = true ↔ MFCode c :=
  no_finitePresentation_MF_decider

/-- **"or even one that enumerates the presentations of MF groups".**

"A `Π⁰₂`-complete set is not `Σ⁰₂` ... so neither set is recursively
enumerable."  In effective form: the `Π⁰₂` predicate `NonhaltsZero` many-one
reduces to `MF_fp` by `Π⁰₂`-hardness, and `NonhaltsZero` is not RE. -/
theorem mfPresentations_not_re (R : RecognitionFamily) : ¬ REPred MFCode :=
  ExactSwitchAlgorithmicConsequences.not_re_of_manyOneReduction
    ExactSwitchAlgorithmicConsequences.nonhaltsZero_not_re
    ((mfPresentations_pi02Complete R).2 ExactSwitchAlgorithmicConsequences.NonhaltsZero
      ExactSwitchAlgorithmicConsequences.nonhaltsZero_pi02)

/-- **"or those of non-MF groups".**  This clause is unconditional in the
repository. -/
theorem nonMFPresentations_not_re : ¬ REPred NonMFCode :=
  MFRecognitionImpossible.nonMF_presentations_not_re

/-- **"There is a computable map `e ↦ R̂_e` such that `R̂_e` presents an MF
group if and only if the `e`-th partial computable function has infinite
domain."** -/
theorem exists_computable_mf_family (R : RecognitionFamily) :
    ∃ f : Nat.Partrec.Code → PresentationCode, Computable f ∧
      ∀ e, IsOperatorMF (Carrier (f e)) ↔ InfiniteDomain e :=
  ⟨R.code, R.computable_code, (manuscriptMFCompiler R).correct⟩

/-! ## 3.  The theorem -/

/-- **`thm:recognition`, every printed assertion, in printed order.**

1. "`MF_fp ∈ Π⁰₂` by finite certificates" (`prop:mf-upper-bound`);
2. "`NONMF_fp ∈ Σ⁰₂`";
3. "Deciding whether a finite presentation defines an MF group is
   `Π⁰₂`-complete";
4. "and the complementary problem is `Σ⁰₂`-complete";
5. "In particular, it is impossible to construct an algorithm that decides
   from a finite presentation whether the group it defines is MF";
6. the same clause as a Boolean decider;
7. "or even one that enumerates the presentations of MF groups";
8. "or those of non-MF groups";
9. "There is a computable map `e ↦ R̂_e` such that `R̂_e` presents an MF group
   if and only if the `e`-th partial computable function has infinite
   domain."
-/
theorem manuscriptRecognition (R : RecognitionFamily) :
    Pi02 MFCode ∧
      Sigma02 NonMFCode ∧
      Pi02Complete MFCode ∧
      Sigma02Complete NonMFCode ∧
      ¬ ComputablePred MFCode ∧
      (¬ ∃ f : PresentationCode → Bool,
        Computable f ∧ ∀ c, f c = true ↔ MFCode c) ∧
      ¬ REPred MFCode ∧
      ¬ REPred NonMFCode ∧
      (∃ f : Nat.Partrec.Code → PresentationCode, Computable f ∧
        ∀ e, IsOperatorMF (Carrier (f e)) ↔ InfiniteDomain e) :=
  ⟨mfPresentations_pi02, nonMFPresentations_sigma02,
    mfPresentations_pi02Complete R, nonMFPresentations_sigma02Complete R,
    mfPresentations_not_computable, no_mfPresentations_decider,
    mfPresentations_not_re R, nonMFPresentations_not_re,
    exists_computable_mf_family R⟩

end Recognition
end MFRecognition
end Manuscript
end GroupApproximation
