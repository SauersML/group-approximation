import GroupApproximation.Manuscript.MFRecognition.RecognitionAssembly
import GroupApproximation.Manuscript.MFRecognition.RopeCodeFamilySemantics
import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceNonunital
import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaCornerProof
import GroupApproximation.Manuscript.MFRecognition.EffectiveCompilerOfOmega
import GroupApproximation.Higman.CurrentREBenign
import GroupApproximation.Higman.OmegaDebt
import GroupApproximation.Analysis.ShulmanFillConjugatePair

/-!
# `thm:recognition`, closed: the remaining inputs as recorded debts

`RecognitionAssembly.manuscriptRecognition_of` proves every printed clause of
`thm:recognition` from four inputs.  This module names each of them as its own
declaration, so that whatever is still owed is visible in the kernel's axiom
report instead of a leading binder, and closes the theorem on top of them.
Only `conjugateWordNorming` is still a `sorry` here; the ω-closure is read once
for the repository from `Higman.OmegaDebt`, where it is now a theorem, and the
other inputs are proved:

* `conjugateWordNorming` — the one remaining input of Shulman, Theorem 16
  (amalgamated free products of separable `C*`-algebras are MF under
  compatible corona embeddings), in the shape the analytic construction
  produces.  The reduction chain `ShulmanFillTheorem16` →
  `ShulmanFillDenseNorming` → `ShulmanFillWordNorming` →
  `ShulmanFillConjugatePair` proves the printed criterion from it, so
  `shulmanTheorem16` below is a proof and not a `sorry`;
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
that it presents `R̂_e`, so `ropeCodeFamily` below is a term and not a `sorry`.

The effective, marked form of Higman's theorem is not a separate debt: the
compiler of `lem:mikhailova` is built from the ω-closure in
`EffectiveCompilerOfOmega`, so `effectiveHigmanCompiler_nonempty` below is a
proof and not a `sorry`.

The printed nonunital form of `thm:hnn-permanence` is not a debt: its passage
from the unital form is the corner compression `p𝒬p ≅ 𝒬'`, proved in
`HNNPermanenceNonunital`.
-/

set_option warningAsError false

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HigmanCompiler
namespace Assembly

open GroupApproximation.Manuscript.OneSidedMFRadical.HNNCoronaConjugatorSentenceAudit

noncomputable section

/-! ## The analytic debts -/

/-- **DEBT (analysis).**  The one remaining input of Shulman's Theorem 16, in
the shape the construction produces: for every word `y` in the two factor
images and every `δ > 0`, there are discrete models `Z`, a unital compatible
pair `(l, r)` into their corona, and a unitary `u` commuting with `l(ι_A C)`,
such that the conjugated pair `(l, u r u*)` evaluates `y` to within `δ` of its
amalgam norm.  Nothing is left to choose but the models and the unitary; the
carrier is a corona, so the MF clause is automatic.  Everything else in Theorem
16 is proved in `Analysis/ShulmanFill*` — separability of the amalgam, the
diagonal choice of a norming family, reduced-product permanence, the `ε/3`
passage from a dense set to the whole amalgam, and the density of words.

Two routes reach this point, and each ends at one analytic atom the repository
does not have.  The debt is recorded on the first because its reduction chain
is the one that is wired.

* **The norming route**, `Analysis/ShulmanFillTheorem16` →
  `ShulmanFillDenseNorming` → `ShulmanFillWordNorming` →
  `ShulmanFillConjugatePair`, ending here.  Its atom is the word estimate:
  the conjugated pair must reproduce, on a given word, the supremum over all
  compatible pairs that defines the full amalgam norm.  That estimate is of
  Haagerup--Thorbjørnsen type.
* **Shulman's own route**, `Analysis/ShulmanSymmetricDoubleRoute` with
  `ShulmanFillSymmetricDouble*` and `ShulmanFillSymmetricDoubleEmbed*`:
  Theorem 16 is his Theorem 13 (the amalgam embeds in the symmetric double
  `D *_C D`) followed by his Theorem 10 (`D *_C D` is MF for separable MF
  `D`).  It has *two* atoms.  Theorem 10 needs his Theorem 4, the lifting
  characterization of MF against the algebra `𝒟` of `*`-strongly convergent
  matrix sequences, which the repository does not yet carry.  Theorem 13 is
  Enders--Shulman, arXiv:2403.12224, Theorem 4.11, whose proof runs through
  the Arveson extension theorem, the Stinespring dilation theorem and
  Voiculescu's theorem in the Calkin algebra. -/
theorem conjugateWordNorming : ShulmanFill.ConjugateWordNormingStatement := by
  sorry

/-- **Shulman, Theorem 16**, from the conjugate form of its remaining input. -/
theorem shulmanTheorem16 : HNNPermanence.ShulmanTheorem16Statement :=
  ShulmanFill.shulmanTheorem16_of_conjugateWordNorming conjugateWordNorming

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
    (HNNPermanence.hnnInputs_of_citations shulmanTheorem16 uedaCornerMap)
    phi realization iota hiota W hW

/-! ## Higman's embedding theorem -/

/-- The ω-closure, as a term.  The statement itself is `Higman.OmegaDebt`, which
the Theorem C lane imports too, so the repository proves it once rather than
once per lane. -/
def omegaInput : Higman.Omega.OmegaInput := Higman.OmegaDebt.omegaInput

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

/-! ## `thm:recognition`, closed -/

/-- **The family `e ↦ R̂_e` of `thm:recognition`**, as a closed term. -/
def recognitionFamily : Recognition.RecognitionFamily :=
  recognitionFamilyOf
    (HNNPermanence.hnnPermanenceInputs_of_citations shulmanTheorem16 uedaCornerMap)
    markedOutputs ropeCodeFamily

/-- **`thm:recognition`, the `Π⁰₂`-completeness clause**, closed on the
recorded debts. -/
theorem mfPresentations_pi02Complete :
    ArithmeticalHierarchy.Pi02Complete MFRecognitionSecondLevel.MFCode :=
  Recognition.mfPresentations_pi02Complete recognitionFamily

/-- **`thm:recognition`, the `Σ⁰₂`-completeness clause**, closed on the
recorded debts. -/
theorem nonMFPresentations_sigma02Complete :
    ArithmeticalHierarchy.Sigma02Complete MFRecognitionSecondLevel.NonMFCode :=
  Recognition.nonMFPresentations_sigma02Complete recognitionFamily

/-- **`thm:recognition`, every printed clause**, closed on the recorded
debts. -/
theorem manuscriptRecognition :
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
  Recognition.manuscriptRecognition recognitionFamily

end

end Assembly
end HigmanCompiler
end MFRecognition
end Manuscript
end GroupApproximation
