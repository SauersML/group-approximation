import GroupApproximation
import Audit.Scan
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Kernel audit of the headline theorems

`lake build` establishes that every module elaborates.  It does **not**
establish what the resulting proof terms depend on: a `sorry` anywhere in the
library elaborates fine and only shows up as the `sorryAx` axiom in the closure
of whatever used it, and `native_decide` shows up as `Lean.ofReduceBool`.

This file is run by CI with `lake env lean scripts/Audit.lean` after the build.
It fails, with a nonzero exit code, if either check below fails:

1. **Statement pinning.**  The `example`s restate the principal headline
   theorems verbatim.  The complete manuscript-mapped surface is pinned by
   `scripts/Signatures.lean` and `docs/CLAIM_SIGNATURES.md`; if a mapped
   statement is weakened or gains a premise, that signature gate changes.
2. **Transitive axiom closure.**  Every declaration in the
   `GroupApproximation` namespace is traversed through the *kernel*
   environment, and the accumulated axiom set must be contained in the three
   axioms of classical Lean.  `sorryAx`, `Lean.ofReduceBool`,
   `Lean.trustCompiler` and any hand-declared `axiom` are all rejected here.
-/

open Lean Elab Command

namespace GroupApproximation.Audit

/-! ## 1. Statement pinning -/

example : ∃ (G : Type) (_ : Group G), ¬ IsSofic G :=
  nonsofic_groups_exist

example : ∃ (G : Type) (_ : Group G), Group.IsFinitelyPresented G ∧ ¬ IsSofic G :=
  exists_finitelyPresented_nonsofic_group

example :
    ∃ (E : Type) (_ : Group E), Countable E ∧ ¬ IsWeakMF E :=
  ChosenNonMFTheorem.exists_countable_not_isWeakMF

example :
    ∃ (E : Type) (_ : Group E),
      Group.IsFinitelyPresented E ∧ ¬ IsWeakMF E :=
  ChosenNonMFTheorem.exists_finitelyPresented_not_isWeakMF

example :
    Group.IsFinitelyPresented
        ChosenMarkedPresentation.MarkedGroup ∧
      ¬ IsOperatorMF ChosenMarkedPresentation.MarkedGroup :=
  ChosenNonMFTheorem.chosenFinitelyPresented_not_isOperatorMF

example : LiteralCyclicCalibration.mark ≠ 1 :=
  LiteralCyclicCalibration.mark_ne_one

example : Function.Surjective LiteralNonMFLinearWitness.matrixBaseHom :=
  LiteralNonMFLinearWitness.matrixBaseHom_surjective

example : LiteralBaseRelations.x * LiteralBaseRelations.v1 *
    LiteralBaseRelations.x⁻¹ = LiteralBaseRelations.v3 :=
  LiteralBaseRelations.x_conj_v1

example : Subgroup.normalizer
    (LiteralBaseTranslationNormal.translations :
      Set LiteralBaseTranslationNormal.Base) = ⊤ :=
  LiteralBaseTranslationNormal.normalizer_translations_eq_top

example {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V]
    (pi : LiteralCyclicCalibration.LiteralGroup →* (Module.End k V)ˣ) :
    pi LiteralCyclicCalibration.mark = 1 :=
  LiteralCyclicCalibration.finiteDimensional_kill pi

example :
    ¬ IsOperatorMF MarkedCompression.Explicit.theGroup :=
  ChosenNonMFTheorem.countableWitness_not_isOperatorMF

example :
    ∃ (E : Type) (_ : Group E),
      Group.IsFinitelyPresented E ∧ ¬ IsOperatorMF E :=
  ChosenNonMFTheorem.exists_finitelyPresented_not_isOperatorMF

example : ¬ (∀ (E : Type) [Group E], IsOperatorMF E) :=
  ChosenNonMFTheorem.not_every_group_isOperatorMF

example :
    ¬ (∀ (E : Type) [Group E] [Group.IsFinitelyPresented E],
      IsOperatorMF E) :=
  ChosenNonMFTheorem.not_every_finitelyPresented_group_isOperatorMF

example (G : Type) [Group G] [Countable G] :
    IsOperatorMF G ↔ normMFResidual G = ⊥ :=
  isOperatorMF_iff_normMFResidual_eq_bot

example (G : Type) [Group G] [Countable G] :
    IsOperatorMF G ↔ coronaMFResidual G = ⊥ :=
  isOperatorMF_iff_coronaMFResidual_eq_bot

example (G H : Type) [Group G] [Group H] [Countable G] [Countable H]
    (f : G →* H) :
    (coronaMFResidual G).map f ≤ coronaMFResidual H :=
  map_coronaMFResidual_le f

example (Gamma E : Type) [Group Gamma] [Group E] [Countable E]
    (C : KazhdanCompressionCore Gamma E)
    (F : Subgroup E) [Finite F] [F.Normal] [Nontrivial F]
    (hF : F ≤ C.defectNormal) :
    ¬ IsOperatorMF E :=
  C.not_isOperatorMF_of_finiteNormal_le_defect F hF

example (Gamma E : Type) [Group Gamma] [Group E] [Countable E]
    (C : KazhdanCompressionCore Gamma E)
    (F : Subgroup E) [Finite F] [F.Normal]
    (hF : F ≤ C.defectNormal)
    (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n))
    (rho : E →* NormMatrixCoronaUnitary X) :
    F ≤ rho.ker :=
  C.finiteNormal_le_normMatrixCoronaKernel F hF X hX rho

example (G : Type) [Group G] [Countable G] :
    IsSofic G ↔ AdmitsEssentiallyFreeNearAction G :=
  isSofic_iff_admitsEssentiallyFreeNearAction G

example :
    ∃ (G : Type) (_ : Group G),
      Countable G ∧ ¬ AdmitsEssentiallyFreeNearAction G :=
  countable_group_without_essentiallyFreeNearAction_exists

example : ¬ IsSofic UniversalRankFour.Ambient :=
  universalLeavittEL4_not_isSofic

example : ¬ IsSofic UniversalRankFour.Core :=
  universalLeavittEL3_not_isSofic

example : ¬ IsSofic UniversalLeavittUnits :=
  universalLeavittUnits_not_isSofic

example (m : ℕ) : ¬ IsSofic (UniversalLeavittGL m) :=
  universalLeavittGL_not_isSofic m

example (k : Type) [Field k] [Finite k] :
    ¬ IsSofic (BinaryLeavittUnits k) :=
  binaryLeavittUnits_not_isSofic k

example (k : Type) [Field k] [Finite k] (m : ℕ) :
    ¬ IsSofic (BinaryLeavittGL k m) :=
  binaryLeavittGL_not_isSofic k m

example : ¬ IsLEF ↥ThompsonV.thompsonV :=
  BinaryLeavitt.thompsonV_not_isLEF

example (m : ℕ) (hm : 1 ≤ m) :
    Group.FG (UniversalLeavittEL m) ∧
      Infinite (UniversalLeavittEL m) ∧
      HasKazhdanPropertyT.{0, 0} (UniversalLeavittEL m) ∧
      ¬ IsSofic (UniversalLeavittEL m) :=
  universalLeavitt_profile m hm

example (n : ℕ) (hn : 2 ≤ n) :
    HasTTmodT.{0, 0}
      (elementaryGroup (Fin n)
        (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))) :=
  PropertyTTPaper.binaryLeavitt_elementaryGroup_hasTTmodT n hn

example : HasTTmodT.{0, 0}
    (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))ˣ :=
  PropertyTTPaper.binaryLeavittUnits_hasTTmodT

noncomputable example (n : ℕ) (hn : 2 ≤ n) :
    elementaryGroup (Fin n)
        (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) ≃*
      (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))ˣ :=
  PropertyTTPaper.binaryLeavitt_elementaryEquivUnits n hn

example {R : Type} [Ring R] [Nontrivial R]
    (X : Type) [Fintype X]
    (f : FreeAlgebra (ZMod 2) X →+* R) (hf : Function.Surjective f)
    (L : LeavittFamily R)
    (hdiv : HasSingleSandwichDivision R)
    (hdiag : HasElementaryDiagonalClass R)
    (n : ℕ) (hn : 2 ≤ n) :
    HasTTmodT.{0, 0} (elementaryGroup (Fin n) R) :=
  FiniteTypeLeavittTT.elementaryGroup_hasTTmodT
    X f hf L hdiv hdiag n hn

example (k : Type) [Field k] [Finite k]
    (m : ℕ) (hm : 1 ≤ m) :
    Group.FG (BinaryLeavittEL k m) ∧
      Infinite (BinaryLeavittEL k m) ∧
      HasKazhdanPropertyT.{0, 0} (BinaryLeavittEL k m) ∧
      ¬ IsSofic (BinaryLeavittEL k m) :=
  binaryLeavitt_finiteField_profile k m hm

example :
    Group.FG UniversalRankFour.Ambient ∧
      Infinite UniversalRankFour.Ambient ∧
      HasKazhdanPropertyT.{0, 0} UniversalRankFour.Ambient ∧
      ¬ IsSofic UniversalRankFour.Ambient :=
  ambient_profile

example :
    Countable UniversalRankFour.Ambient ∧
      Group.FG UniversalRankFour.Ambient ∧
      Infinite UniversalRankFour.Ambient ∧
      HasKazhdanPropertyT.{0, 0} UniversalRankFour.Ambient ∧
      ¬ IsSofic UniversalRankFour.Ambient :=
  ambient_full_profile

example :
    ∃ (H : Type) (_ : Group H),
      Infinite H ∧ Group.IsFinitelyPresented H ∧ ¬ IsSofic H ∧
        ∃ π : H →* UniversalRankFour.Ambient,
          Function.Surjective π :=
  exists_infinite_finitelyPresented_nonsofic_ambient_cover

/-- The positive control, pinned here so that it cannot be deleted while the
negative results remain.  Every other occurrence of `IsSofic` in the library is
a hypothesis to refute or a conclusion under a `¬`; if no group is ever
exhibited satisfying it, `¬ IsSofic G` is equally consistent with the
definition being unsatisfiable, and a kernel-clean proof of it would be worth
nothing.  See `GroupApproximation/SoficPositiveControl.lean`. -/
example (G : Type) [Group G] [Fintype G] [DecidableEq G] : IsSofic G :=
  isSofic_of_fintype G

example (G : Type) [Group G] [Finite G] : IsSofic G :=
  isSofic_of_finite G

example : IsSofic (Multiplicative ℤ) :=
  isSofic_multiplicative_int

example (G : Type) [Group G] :
    IsSofic G ↔ IsSoficProductRestricted G :=
  isSofic_iff_productRestricted G

example (G : Type) [Group G] [Finite G] : IsLEF G :=
  isLEF_of_finite G

example : IsLEF (Multiplicative ℤ) :=
  isLEF_multiplicative_int

example (G : Type) [Group G] [Finite G] : IsTextbookLEF G :=
  isTextbookLEF_of_finite G

example : IsTextbookLEF (Multiplicative ℤ) :=
  isTextbookLEF_multiplicative_int

example (G : Type) [Group G] : IsLEF G ↔ IsTextbookLEF G :=
  isLEF_iff_textbook G

example {H : Type} [Group H] [Finite H]
    (f : FreeGroup (Fin 2) →* H)
    (h₁ : f ThompsonFObstruction.relator₁ = 1)
    (h₂ : f ThompsonFObstruction.relator₂ = 1) :
    f ThompsonFObstruction.generatorCommutator = 1 :=
  ThompsonFObstruction.finite_image_generatorCommutator_eq_one f h₁ h₂

/-! ### The exact manuscript endpoints

One pin per printed headline statement of `Endpoint/ManuscriptStatements`,
restated verbatim so that a weakening stops typechecking here. -/

open Manuscript

example :
    (∀ m : ℕ, 1 ≤ m →
      Group.FG (UniversalLeavittEL m) ∧
        Infinite (UniversalLeavittEL m) ∧
        HasKazhdanPropertyT.{0, 0} (UniversalLeavittEL m) ∧
        ¬ IsSofic (UniversalLeavittEL m)) ∧
      ¬ IsSofic UniversalRankFour.Ambient ∧
      CountableNonsoficGroupExists :=
  theoremA_exact

example :
    ∃ (G : Type) (_ : Group G), Countable G ∧ ¬ IsSofic G :=
  countable_nonsofic_groups_exist

example (k : Type) [Field k] [Finite k] :
    ManuscriptProfile (BinaryLeavittUnits k) ∧
      (∀ (r : ℕ), 1 ≤ r → ∀ (C : BinaryPrefixCode (Fin r))
          (hC : (BinaryLeavitt.family k).IsComplete C)
          (M : BinaryLeavittGLRank k r),
          ((theoremB_Theta k C hC M : BinaryLeavittUnits k) :
              BinaryLeavitt.BinaryLeavittAlgebra k) =
            ∑ i, ∑ j, (BinaryLeavitt.family k).wordS (C.word i) *
              (M : Matrix (Fin r) (Fin r) (BinaryLeavitt.BinaryLeavittAlgebra k)) i j *
              (BinaryLeavitt.family k).wordT (C.word j)) ∧
      (∀ r : ℕ, 2 ≤ r → BinaryLeavittELRank k r = ⊤) ∧
      (∀ r : ℕ, 1 ≤ r → ManuscriptProfile (BinaryLeavittGLRank k r)) ∧
      (∀ r : ℕ, 2 ≤ r → ManuscriptProfile ↥(BinaryLeavittELRank k r)) :=
  theoremB_exact k

example (k : Type) [Field k] [Finite k] :
    ∃ (H : Type) (_ : Group H) (π : H →* BinaryLeavittUnits k),
      Function.Surjective π ∧ Infinite H ∧ Group.IsFinitelyPresented H ∧
        HasKazhdanPropertyT.{0, 0} H ∧ ¬ IsSofic H :=
  theoremC_exact k

example (k : Type) [Field k] [Finite k] :
    ∃ (H : Type) (_ : Group H),
      Infinite H ∧ Group.IsFinitelyPresented H ∧
        HasKazhdanPropertyT.{0, 0} H ∧ ¬ IsSofic H ∧
        (∃ π : H →* BinaryLeavittUnits k, Function.Surjective π) ∧
        (∀ m : ℕ, ∃ π : H →* BinaryLeavittGL k m, Function.Surjective π) ∧
        (∀ m : ℕ, 1 ≤ m →
          ∃ π : H →* BinaryLeavittEL k m, Function.Surjective π) :=
  theoremC_covers_theoremB_groups k

example {G : Type} [Group G]
    (Γ J : Subgroup G) (Q : Finset G) (q₀ : G)
    (hTG : HasKazhdanPropertyT.{0, 0} G)
    (hTΓ : HasKazhdanPropertyT.{0, 0} ↥Γ)
    (hΓinf : Infinite ↥Γ) (hJfg : Group.FG ↥J)
    (hJΓ : J ≤ Γ)
    (hgen : Subgroup.closure ((Γ : Set G) ∪ (Q : Set G)) = ⊤)
    (hcompress : ∀ q ∈ Q, ∀ g ∈ Γ, q * g * q⁻¹ ∈ Γ)
    (hq₀ : q₀ ∈ Q)
    (hcent : ∀ x ∈ conjSubgroup q₀ Γ, ∀ y ∈ J, x * y = y * x)
    (hdisj : conjSubgroup q₀ Γ ⊓ J = ⊥)
    (hS : IsSofic G) : IsLEF ↥J :=
  theoremD_subgroups Γ J Q q₀ hTG hTΓ hΓinf hJfg hJΓ hgen hcompress
    hq₀ hcent hdisj hS

example (k A : Type) [Field k] [Finite k] [Ring A] [Nontrivial A]
    [Algebra k A] [Algebra.FiniteType k A] (L : LeavittFamily A)
    (m : ℕ) (hm : 0 < m) (hm2 : 2 ≤ m)
    (hu : GeneralScheme.uUnit L (m := m) ∈ elementaryGroup (Fin (m + 1)) A)
    (hz : GeneralScheme.zUnit L hm ∈ elementaryGroup (Fin (m + 1)) A) :
    ManuscriptProfile ↥(elementaryGroup (Fin (m + 1)) A) :=
  cor_fgring_printed k A L m hm hm2 hu hz

example (k : Type) [Field k] : Subsingleton (BinaryLeavittWhiteheadK1 k) :=
  binaryLeavittWhiteheadK1_subsingleton k

example (c : ℝ) (hc : 0 < c) :
    ∃ m : ℕ, 4 ≤ m ∧ (KunSpectral.switched m).HasCheegerLowerBound 1 ∧
      ¬ KunSpectral.IsBipartite (KunSpectral.switched m) ∧
      KunSpectral.rayleigh (KunSpectral.switched m) (KunSpectral.testVector m)
        < -1 + c :=
  KunSpectral.no_uniform_spectral_gap c hc

/-! ## 2. Transitive axiom closure -/

/-- The axioms of classical Lean, which Mathlib itself uses.  Nothing else is
permitted anywhere in this development.

`lcProof` is deliberately absent: it is the compiler's erased-proof placeholder
and reaches a kernel closure through `partial def` and friends.  This library
has none, so if it ever appears the right response is to find out which
declaration introduced it, not to widen this list. -/
def allowedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

/-- Named propositions that transcribe theorems of the literature which this
repository does not prove.  Under the same custody as `allowedAxioms`: the
list lives in the lint, so the corpus cannot untag its own citations.

Any user-written declaration on the trust surface that takes one of these --
or anything that unfolds to mention one -- as a premise, or embeds one in its
conclusion other than by proving it, is a LITERATURE_INPUT finding and fails
the audit.  The kernel cannot make this distinction: such an implication is
genuinely proved, and its axiom report is clean.  The point of the gate is
that a conditional result must not LIVE on the trust surface, however honest
its type: it belongs in `Superseded`, or its antecedent belongs in the
corpus as a theorem, after which its name comes off this list.

The roster is empty: literature-transcription premises are not permitted in
the corpus.  Keep this mechanism in place so adding one cannot silently turn
an external theorem into a conditional trust-surface result. -/
def literatureInputNames : List Name := []

/-- The public results.  Their individual closures are reported separately so
that a CI log records exactly what each headline theorem rests on. -/
def headlineTheorems : List Name :=
  [``nonsofic_groups_exist,
   ``countable_nonsofic_groups_exist,
   ``isSofic_iff_admitsEssentiallyFreeNearAction,
   ``universalLeavittEL4_not_admitsEssentiallyFreeNearAction,
   ``countable_group_without_essentiallyFreeNearAction_exists,
   ``exists_finitelyPresented_nonsofic_group,
   ``exists_infinite_finitelyPresented_nonsofic_ambient_cover,
   ``ChosenNonMFTheorem.mark_normMFInvisible,
   ``ChosenNonMFTheorem.chosenFinitelyPresented_not_isWeakMF,
   ``ChosenNonMFTheorem.exists_countable_not_isWeakMF,
   ``ChosenNonMFTheorem.exists_finitelyPresented_not_isWeakMF,
   ``ChosenNonMFTheorem.chosenFinitelyPresented_not_isOperatorMF,
   ``ChosenNonMFTheorem.exists_finitelyPresented_not_isOperatorMF,
   ``ChosenNonMFTheorem.not_every_group_isOperatorMF,
   ``ChosenNonMFTheorem.not_every_finitelyPresented_group_isOperatorMF,
   ``OperatorMFMarkovWitness.positive_punit,
   ``OperatorMFMarkovWitness.chosen_forbidden_subgroup,
   ``OperatorMFMarkovWitness.exists_finitelyPresented_forbidden_subgroup,
   ``FixedSpaceDefect.compressionCentralizerDefect_le_ker,
   ``LiteralCyclicCalibration.mark_ne_one,
   ``LiteralCyclicCalibration.finiteDimensional_kill,
   ``KazhdanCompressionCore.finiteNormal_le_normMFResidual,
   ``KazhdanCompressionCore.finiteNormal_le_normMatrixCoronaKernel,
   ``KazhdanCompressionCore.not_isOperatorMF_of_finiteNormal_le_defect,
   ``isOperatorMF_iff_normMFResidual_eq_bot,
   ``coronaMFResidual_eq_normMFResidual,
   ``map_coronaMFResidual_le,
   ``isOperatorMF_iff_coronaMFResidual_eq_bot,
   ``normMFQuotient_isOperatorMF,
   ``coronaMFQuotient_isOperatorMF,
   ``exists_normMatrixCoronaRepresentation_ker_eq_normMFResidual,
   ``exists_normMatrixCoronaRepresentation_ker_eq_coronaMFResidual,
   ``existsUnique_normMFQuotient_factorization_to_isOperatorMF,
   ``existsUnique_coronaMFQuotient_factorization_to_isOperatorMF,
   ``isOperatorMF_of_residuallyFinite,
   ``IsOperatorMF.subgroup,
   ``OperatorMFQuotientNonclosure.operatorMF_not_closed_under_this_quotient,
   ``not_injective_of_coronaMFInvisible,
   ``KazhdanCompressionCore.finiteNormal_uniform_invisibility,
   ``FaithfulTracialState.matrix_mul_star_eq_one_of_star_mul_eq_one,
   ``ProperProjectionCompression.star_isometry_mul_eq_one_and_reverse_ne,
   ``ProperProjectionCompression.not_isStablyFiniteRing,
   ``universalLeavittEL4_not_isSofic,
   ``universalLeavittEL3_not_isSofic,
   ``universalLeavittUnits_not_isSofic,
   ``universalLeavittGL_not_isSofic,
   ``binaryLeavittUnits_not_isSofic,
   ``binaryLeavittGL_not_isSofic,
   ``BinaryLeavitt.thompsonV_not_isLEF,
   ``universalLeavitt_profile,
   ``binaryLeavitt_finiteField_profile,
   ``ambient_profile,
   ``ambient_full_profile,
   ``Manuscript.theoremA_exact,
   ``Manuscript.theoremB_exact,
   ``Manuscript.theoremC_exact,
   ``Manuscript.theoremC_covers_theoremB_groups,
   ``Manuscript.theoremD_subgroups,
   ``Manuscript.cor_fgring_printed,
   ``Manuscript.cor_fgring_exact,
   ``Manuscript.cor_fgring_countableFree,
   ``binaryLeavittWhiteheadK1_subsingleton,
   ``KunSpectral.no_uniform_spectral_gap]

/-- Every declaration of this development, taken from the environment rather
than from a hand-maintained list, so that a new module cannot escape the
audit by not being mentioned here. -/
def projectDeclarations (env : Environment) : Array Name :=
  env.constants.fold (init := #[]) fun acc n _ =>
    if (`GroupApproximation).isPrefixOf n then acc.push n else acc

/-- The union of the transitive axiom closures of `roots`. -/
def axiomClosure (roots : Array Name) : CommandElabM (Array Name) := do
  let mut result := #[]
  for n in roots do
    let axioms ← collectAxioms n
    for a in axioms do
      unless result.contains a do
        result := result.push a
  return result

def disallowed (axioms : Array Name) : Array Name :=
  axioms.filter fun a => !allowedAxioms.contains a

run_cmd do
  let env ← getEnv

  for n in headlineTheorems do
    unless env.contains n do
      throwError "audit target `{n}` does not exist in the environment"
    let axioms ← collectAxioms n
    let bad := disallowed axioms
    unless bad.isEmpty do
      throwError "`{n}` depends on disallowed axioms: {bad.toList}"
    logInfo m!"{n} depends on: {axioms.toList}"

  let decls := projectDeclarations env
  if decls.size < 100 then
    throwError "only {decls.size} declarations found in the `GroupApproximation` \
namespace; the audit is not seeing the library"
  let axioms ← axiomClosure decls
  let bad := disallowed axioms
  unless bad.isEmpty do
    throwError "the `GroupApproximation` namespace depends on disallowed \
axioms: {bad.toList}"
  logInfo m!"audited {decls.size} declarations; no disallowed axioms"

/-! ## 3. The environment scans

`Audit.Scan` carries the detectors and `scripts/Calibrate.lean` proves they can
fire; this section runs them on the real corpus and decides the exit code.

**There are no budgets: any finding, under any tag, fails the run.**  Nothing
here is report-only and nothing is a ratchet, so there is no number a reviewer
can raise instead of fixing the corpus, and a scan cannot be quietened by
editing this file.  The list below is a reporting roster, not a gate: it exists
so that a passing log records a count for every detector, since a scan that has
silently stopped firing is otherwise indistinguishable from a clean corpus.  A
finding under a tag missing from the roster still fails, and is still named. -/

def scanTags : List String :=
  [ "AXIOM"                 -- anything here is a trust bypass
  , "TAUTOLOGY"             -- a proof that is its own premise is never intended
  , "EMPTY_PREMISE"         -- a vacuously true theorem is never intended
  , "UNCONDITIONAL"
  -- Structural `[Nonempty ...]` inputs used to obtain positive finite
  -- cardinalities or select an index.  Fixed at the declaration, not tolerated
  -- by a count here.
  , "ASSUMPTION_INSTANCE"
  , "UNUSED"
  , "TRIVIAL"
  , "DUPLICATE"
  , "RFL"
  -- Prose calling a result conditional on a statement with no Prop premise.
  -- Lives here rather than in `check.py` because only the environment can see
  -- both the docstring and the type; see `Scan.disclaimerPhrases`.
  , "STALE_DISCLAIMER"
  -- A premise or embedded conclusion mentioning a tagged transcription of an
  -- unproved literature theorem; the roster is `literatureInputNames` above.
  , "LITERATURE_INPUT" ]

/-- Keep this high enough that a failing log names every hit rather than a
sample of them. -/
def examplesPerTag : Nat := 64

run_cmd do
  let env ← getEnv
  let findings ← liftTermElabM <|
    Audit.allScans env `GroupApproximation allowedAxioms
  let findings := findings ++
    Audit.literatureScan env `GroupApproximation literatureInputNames

  for tag in scanTags do
    logInfo m!"{tag}: {(findings.filter (fun f => f.tag == tag)).size}"

  -- Once per tag, not once per finding: a renamed tag produced one line of
  -- signal and 255 lines of repetition the first time this fired.
  let mut failures : Array String := #[]
  let mut reported : Array String := #[]
  for f in findings do
    unless reported.contains f.tag do
      reported := reported.push f.tag
      let hits := findings.filter (fun g => g.tag == f.tag)
      let examples :=
        (hits.map (fun h => s!"{h.decl}: {h.detail}")).toList.take examplesPerTag
      let roster := if scanTags.contains f.tag then "" else " (tag not on the roster)"
      failures := failures.push
        s!"{f.tag}: {hits.size} findings{roster}; e.g. {examples}"

  unless failures.isEmpty do
    throwError "audit failed:{Format.line}{Format.joinSep failures.toList Format.line}"

end GroupApproximation.Audit
