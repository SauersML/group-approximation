import GroupApproximation.Manuscript.MFRecognition.RecognitionAssembly
import GroupApproximation.Manuscript.MFRecognition.RopeCodeFamilySemantics
import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceNonunital
import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaCornerProof
import GroupApproximation.Manuscript.MFRecognition.EffectiveCompilerOfOmega
import GroupApproximation.Higman.CurrentREBenign
import GroupApproximation.Higman.OmegaDebt
import GroupApproximation.Analysis.ShulmanFillNormingRecognitionWiring

/-!
# `thm:recognition`: the remaining analytic inputs exposed

`RecognitionAssembly.manuscriptRecognition_of` proves every printed clause of
`thm:recognition` from four inputs.  The algebraic and computability inputs are
proved.  The analytic input is reduced, without axioms, to the two literature
interfaces in `RecognitionAnalyticInputs` below.  Keeping those interfaces as
an explicit argument makes the remaining theorem boundary visible in every
endpoint type instead of hiding it behind an admitted proof.

* `conjugateWordNorming` — Shulman's Theorem 16 input
  (amalgamated free products of separable `C*`-algebras are MF under
  compatible corona embeddings), in the shape the analytic construction
  produces.  The reduction chain `ShulmanFillTheorem16` →
  `ShulmanFillDenseNorming` → `ShulmanFillWordNorming` →
  `ShulmanFillConjugatePair` proves the printed criterion from it, so
  `shulmanTheorem16` below is a proof rather than an unresolved declaration;
* `uedaCornerMap` is no longer a debt: `HNNPermanenceUedaCornerProof` builds
  Ueda's corner map coordinate by coordinate, around the universe gap recorded
  on `UedaCornerMapStatement`;
* `omegaInput` — Higman's ω-closure, the last construction the benign-subgroup
  route to Higman's embedding theorem needed; it is proved in
  `Higman.OmegaFillLeadLinkBenign` and read once for the repository from
  `Higman.OmegaDebt`, and with it Higman's theorem is the theorem `reBenign`
  below.

The code of `eq:finite-rope` is not a debt either: `RopeCodes.ropeCodeFamilyOf`
compiles it from the marked output of any effective Higman compiler and proves
that it presents `R̂_e`, so `ropeCodeFamily` below is a proved term.

The effective, marked form of Higman's theorem is not a separate debt: the
compiler of `lem:mikhailova` is built from the ω-closure in
`EffectiveCompilerOfOmega`, so `effectiveHigmanCompiler_nonempty` below is a
proof rather than an unresolved declaration.

The printed nonunital form of `thm:hnn-permanence` is not a debt: its passage
from the unital form is the corner compression `p𝒬p ≅ 𝒬'`, proved in
`HNNPermanenceNonunital`.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HigmanCompiler
namespace Assembly

open GroupApproximation.Manuscript.OneSidedMFRadical.HNNCoronaConjugatorSentenceAudit

noncomputable section

/-! ## The analytic debts -/

/-- The two analytic literature interfaces still needed by Shulman's route.
The first is Theorem 10, whose proof uses the one-leg Theorem 4 only through
the special stabilized flip/Halmos construction.  The second is the
compatible-target form of Enders--Shulman, Theorem 4.11.  In particular this
does not assume an arbitrary unamplified pair of asymptotic lifts. -/
structure RecognitionAnalyticInputs : Prop where
  symmetricDoubleMF : ShulmanSymmetricDouble.SymmetricDoubleMFStatement
  compatibleTargetPair :
    ShulmanSymmetricDouble.CompatibleTargetPairStatement

/-- **DEBT (analysis).**  The remaining input of Shulman's Theorem 16, in the
shape the construction produces: for every word `y` in the two factor
images and every `δ > 0`, there are discrete models `Z`, a unital compatible
pair `(l, r)` into their corona, and a unitary `u` commuting with `l(ι_A C)`,
such that the conjugated pair `(l, u r u*)` evaluates `y` to within `δ` of its
amalgam norm.  Nothing is left to choose but the models and the unitary; the
carrier is a corona, so the MF clause is automatic.  Everything else in Theorem
16 is proved in `Analysis/ShulmanFill*` — separability of the amalgam, the
diagonal choice of a norming family, reduced-product permanence, the `ε/3`
passage from a dense set to the whole amalgam, and the density of words.

The transcription boundary is now split where the source splits it:

* `ShulmanFill.Theorem4OneLegStatement`
  (`Analysis/ShulmanFillNormingTailPrinted`) records Theorem 4 as one
  nonunital contractive asymptotic lift of one representation.  It has no
  `tendsto_one`, no second leg and no agreement-on-`C` conclusion.
  `ShulmanFill.UnitalTailPairPackageStatement` names the old stronger
  two-leg tail package for its conditional development, but it is not a
  citation interface and is not consumed here;
* `ShulmanSymmetricDouble.SymmetricDoubleMFStatement`
  (`Analysis/ShulmanSymmetricDoubleRoute`) is Shulman's Theorem 10.  This is
  the first recognition input because the missing passage from the one-leg
  lift to a pair is special: stabilize the two representations in opposite
  order, conjugate by the explicit flip, and apply Lemma 9's Halmos correction.
  No arbitrary unamplified two-leg statement is asserted;
* `ShulmanSymmetricDouble.CompatibleTargetPairStatement`
  (`Analysis/ShulmanFillTheorem13`): the output of Enders--Shulman,
  arXiv:2403.12224, Theorem 4.11 — a compatible target through which the
  factor map of the symmetric double is injective — whose printed proof runs
  through the Arveson extension theorem, the Stinespring dilation theorem and
  Voiculescu's theorem in the Calkin algebra;
* `ShulmanFill.SeparableFaithfulRepresentationStatement.{1}`
  (`Analysis/ShulmanFillNormingRecognitionWiring`): a separable `C*`-algebra
  has a faithful representation on a Hilbert space in `Type`.  The algebra is
  quantified one universe up because the universal amalgam lives there; the
  space stays small.  This one is a theorem,
  `CStarState.separableFaithfulRepresentation` in
  `Analysis/CStarSeparableTypeZeroRepresentation`: the GNS sum over a
  countable separating family of states carries a countable total sequence,
  and the countable Gram--Schmidt basis of
  `Analysis/CStarHilbertCountableBasis` moves the representation to `ℓ²`
  over a small index along `Analysis/CStarHilbertTransport`.

So the debt rests on the two inputs in `RecognitionAnalyticInputs`.  The route
itself is Shulman's own: Theorem 13 embeds the amalgam in the symmetric double
`D *_C D`, the `symmetricDoubleMF` field supplies Theorem 10 at precisely its
special flip-pair endpoint, and the injective
factor map turns the MF double into the type-zero witness that
`shulmanTheorem16_of_typeZeroWitness` consumes.  Until both interfaces are
theorems the debt remains an explicit argument here. -/
theorem conjugateWordNorming (h : RecognitionAnalyticInputs) :
    ShulmanFill.ConjugateWordNormingStatement :=
  ShulmanFill.conjugateWordNorming_of_typeZeroWitness
    h.symmetricDoubleMF
    (ShulmanFill.factorMapInjective_of_compatibleTargetPair
      h.compatibleTargetPair)

/-- **Shulman, Theorem 16**, from the conjugate form of its remaining input. -/
theorem shulmanTheorem16 (h : RecognitionAnalyticInputs) :
    HNNPermanence.ShulmanTheorem16Statement :=
  ShulmanFill.shulmanTheorem16_of_conjugateWordNorming
    (conjugateWordNorming h)

/-- **Ueda, Proposition 2.4, as the corner map** — proved coordinate by
coordinate in `HNNPermanenceUedaCornerProof`: the universal `C*`-HNN algebra
maps injectively into the corner `ePe` of the full amalgam, carrying the base
and the stable unitary to the printed elements. -/
theorem uedaCornerMap : HNNPermanence.UedaCornerMapStatement :=
  HNNPermanence.uedaCornerMap_proved

/-- **`thm:hnn-permanence`, printed form, with a possibly nonunital `ι`.**
Printed: *"an injective `*`-homomorphism `ι : A → 𝒬` and a unitary `W ∈ 𝒬`
with `W ιρ(s) W* = ιρ(θ(s))`."*  The passage from the unital form is the
compression of `𝒬` to the corner `p𝒬p`, `p = ι(1)`, which is again a norm
matrix corona; it is proved in `HNNPermanenceNonunital`, so this form rests
on the same two citations as the unital one. -/
theorem manuscriptHNNPermanence_nonunital
    (h : RecognitionAnalyticInputs)
    {G : Type} [Group G] [Countable G]
    {S T : Subgroup G} (phi : S ≃* T)
    {A : Type} [CStarAlgebra A] (realization : RegularRealizationData G A)
    {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]
    (iota : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ X n))
    (hiota : Function.Injective iota)
    (W : unitary (NormMatrixCStarCorona (fun n ↦ X n)))
    (hW : ∀ s : S,
      (W : NormMatrixCStarCorona (fun n ↦ X n)) *
            iota ((realization.rho (s : G) : unitary A) : A) *
          star (W : NormMatrixCStarCorona (fun n ↦ X n)) =
        iota ((realization.rho ((phi s : T) : G) : unitary A) : A)) :
    IsRegularlyRealized (HNNExtension G S T phi) :=
  HNNPermanenceNonunital.manuscriptHNNPermanence_nonunital
    (HNNPermanence.hnnInputs_of_citations (shulmanTheorem16 h) uedaCornerMap)
    phi realization iota hiota W hW

/-! ## Higman's embedding theorem -/

/-- The ω-closure, as a term.  The statement itself is `Higman.OmegaDebt`, which
the Theorem C lane imports too, so the repository proves it once rather than
once per lane. -/
theorem omegaInput : Higman.Omega.OmegaInput := Higman.OmegaDebt.omegaInput

/-- **Higman's embedding theorem** (recursively enumerable normal subgroups of
finitely generated free groups are benign), through the ω-closure. -/
theorem reBenign : Higman.REBenign := Higman.OmegaDebt.reBenign

/-- **The effective marked form of Higman's theorem**: a computable compiler
from recursive presentations on three generators to finite presentations with
marked embedding words.  Not a debt: it is `EffectiveCompilerOfOmega`, one
fixed marked host for the free product of every rank-three input, running off
the ω-closure like `reBenign` above. -/
theorem effectiveHigmanCompiler_nonempty : Nonempty EffectiveHigmanCompiler :=
  EffectiveCompilerOfOmega.effectiveHigmanCompiler_of_omega omegaInput

/-- The compiler, as a term. -/
def effectiveHigmanCompiler : EffectiveHigmanCompiler :=
  effectiveHigmanCompiler_nonempty.some

/-- The marked outputs of `lem:mikhailova` at every `Q_e`. -/
def markedOutputs : ∀ e, MarkedHigmanOutput (qcodeSeed e) :=
  markedOutputsOfCompiler effectiveHigmanCompiler

/-! ## The finite-rope codes -/

/-- **The code of `eq:finite-rope` exists.**  Not a debt: the code is built
and proved correct in `RopeCodeFamilySemantics`. -/
theorem ropeCodeFamily_nonempty : Nonempty (RopeCodeFamily markedOutputs) :=
  ⟨RopeCodes.ropeCodeFamilyOf effectiveHigmanCompiler⟩

/-- **The code of `eq:finite-rope`**, computable from `e` and presenting
`R̂_e`: `Higman.MikhailovaRopeCode.compile` on the ambient code of `K_e`, the
cutting words of `L_e` and the marked words `i(x), i(y), i(t)`, identified
with `FiniteRope` by
`Higman.MikhailovaRopeCodeSemantics.compileEquivToRope`.  Taken as the
compiled term itself rather than through `ropeCodeFamily_nonempty.some`, so
that `recognitionFamily.code` stays the concrete `e ↦ ropeCode (compile e)`. -/
def ropeCodeFamily : RopeCodeFamily markedOutputs :=
  RopeCodes.ropeCodeFamilyOf effectiveHigmanCompiler

/-! ## `thm:recognition`, conditional only on the exposed analytic inputs -/

/-- **The family `e ↦ R̂_e` of `thm:recognition`**, from the remaining
analytic inputs. -/
def recognitionFamily (h : RecognitionAnalyticInputs) :
    Recognition.RecognitionFamily :=
  recognitionFamilyOf
    (HNNPermanence.hnnPermanenceInputs_of_citations
      (shulmanTheorem16 h) uedaCornerMap)
    markedOutputs ropeCodeFamily

/-- **`thm:recognition`, the `Π⁰₂`-completeness clause**, from the remaining
analytic inputs. -/
theorem mfPresentations_pi02Complete (h : RecognitionAnalyticInputs) :
    ArithmeticalHierarchy.Pi02Complete MFRecognitionSecondLevel.MFCode :=
  Recognition.mfPresentations_pi02Complete (recognitionFamily h)

/-- **`thm:recognition`, the `Σ⁰₂`-completeness clause**, from the remaining
analytic inputs. -/
theorem nonMFPresentations_sigma02Complete (h : RecognitionAnalyticInputs) :
    ArithmeticalHierarchy.Sigma02Complete MFRecognitionSecondLevel.NonMFCode :=
  Recognition.nonMFPresentations_sigma02Complete (recognitionFamily h)

/-- **`thm:recognition`, every printed clause**, from the remaining analytic
inputs. -/
theorem manuscriptRecognition (h : RecognitionAnalyticInputs) :
    ArithmeticalHierarchy.Pi02 MFRecognitionSecondLevel.MFCode ∧
      ArithmeticalHierarchy.Sigma02 MFRecognitionSecondLevel.NonMFCode ∧
      ArithmeticalHierarchy.Pi02Complete MFRecognitionSecondLevel.MFCode ∧
      ArithmeticalHierarchy.Sigma02Complete MFRecognitionSecondLevel.NonMFCode ∧
      ¬ ComputablePred MFRecognitionSecondLevel.MFCode ∧
      (¬ ∃ f : PresentationCodes.PresentationCode → Bool,
        Computable f ∧ ∀ c, f c = true ↔ MFRecognitionSecondLevel.MFCode c) ∧
      ¬ REPred MFRecognitionSecondLevel.MFCode ∧
      ¬ REPred MFRecognitionSecondLevel.NonMFCode ∧
      (∃ f : Nat.Partrec.Code → PresentationCodes.PresentationCode, Computable f ∧
        ∀ e, IsOperatorMF (PresentationCodes.Carrier (f e)) ↔
          SecondLevelIndexSets.InfiniteDomain e) :=
  Recognition.manuscriptRecognition (recognitionFamily h)

end

end Assembly
end HigmanCompiler
end MFRecognition
end Manuscript
end GroupApproximation
