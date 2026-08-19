import GroupApproximation
import Audit.Scan
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Kernel audit of the headline theorems

`lake build` establishes that every module elaborates.  It does **not**
establish what the resulting proof terms depend on: an admitted proof
elaborates and contributes an admission axiom to the closure of anything that
uses it; compiler-backed decision shortcuts contribute `Lean.ofReduceBool`.

This file is run by CI with `lake env lean scripts/Audit.lean` after the build.
It fails, with a nonzero exit code, if either check below fails:

1. **Statement pinning.**  The `example`s restate the principal headline
   theorems verbatim.  The complete manuscript-mapped surface is pinned by
   `scripts/Signatures.lean` and `metadata/CLAIM_SIGNATURES.md`; if a mapped
   statement is weakened or gains a premise, that signature gate changes.
2. **Transitive axiom closure.**  Every declaration in the
   `GroupApproximation` namespace is traversed through the *kernel*
   environment, and the accumulated axiom set must be contained in the three
   axioms of classical Lean.  Admission axioms, `Lean.ofReduceBool`,
   `Lean.trustCompiler` and any hand-declared `axiom` are all rejected here.
-/

open Lean Elab Command
open Filter Set Topology
open scoped Topology

namespace GroupApproximation.Audit

universe u

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

example :
    ¬ IsOperatorMF MarkedCompression.Explicit.theGroup :=
  ChosenNonMFTheorem.countableWitness_not_isOperatorMF

example :
    ∃ (E : Type) (_ : Group E),
      Group.IsFinitelyPresented E ∧ ¬ IsOperatorMF E :=
  ChosenNonMFTheorem.exists_finitelyPresented_not_isOperatorMF

example :
    ∃ (E : Type) (_ : Group E),
      Countable E ∧ Group.IsFinitelyPresented E ∧ ¬ IsOperatorMF E :=
  ChosenNonMFTheorem.exists_countable_finitelyPresented_not_isOperatorMF

example : ¬ (∀ (E : Type) [Group E] [Countable E], IsOperatorMF E) :=
  ChosenNonMFTheorem.not_every_countable_group_isOperatorMF

example : ¬ (∀ (E : Type) [Group E], IsOperatorMF E) :=
  ChosenNonMFTheorem.not_every_group_isOperatorMF

example :
    ¬ (∀ (E : Type) [Group E] [Group.IsFinitelyPresented E],
      IsOperatorMF E) :=
  ChosenNonMFTheorem.not_every_finitelyPresented_group_isOperatorMF

example : ¬ IsMixedApproximable SimultaneousStabilitySeed :=
  simultaneousStabilitySeed_not_isMixedApproximable

example (G : Type) [Group G] [Countable G] :
    IsPurelyPermutationField G → IsOperatorMF G :=
  IsPurelyPermutationField.isOperatorMF

example :
    FailsEveryStandardMFConvention LiteralNonMFPresentation.MarkedGroup :=
  LiteralNonMFEndpoint.literal_failsEveryStandardMFConvention

example (G : Type) [Group G] [Countable G] :
    IsOperatorMF G ↔ IsNormApproximable G 1 :=
  OperatorMFLocalNormalization.isOperatorMF_iff_isNormApproximable_one

example (k : ℕ) :
    IsClosed (MarkedGroupSpace.operatorMFLocus k) :=
  MarkedGroupSpace.isClosed_operatorMFLocus

example (k : ℕ) :
    IsOpen (MarkedGroupSpace.operatorMFLocus k)ᶜ :=
  MarkedGroupSpace.isOpen_compl_operatorMFLocus

example {k : ℕ} (M : MarkedGroupSpace k)
    (hM : ¬ IsOperatorMF M.Quotient) :
    ∃ R : ℕ, MarkedGroupSpace.cylinder M
      (MarkedGroupSpace.wordBall k R) ⊆
        (MarkedGroupSpace.operatorMFLocus k)ᶜ :=
  MarkedGroupSpace.exists_wordBall_cylinder_subset_compl_operatorMFLocus M hM

example {A : Type} [Ring A] [StarRing A]
    (D : ProperProjectionCompression A) :
    ∃ a b : A, b * a = 1 ∧ ¬ IsUnit a :=
  D.exists_leftInvertible_not_isUnit

example {A : Type} [Ring A] [StarRing A]
    (D : ProperProjectionCompression A) :
    ¬ IsDedekindFiniteMonoid A :=
  D.not_isDedekindFiniteMonoid

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

/-! ### The genuine C-star-corona target

These pins deliberately expand the opaque public target and the CDE predicate.
Pinning only their names would allow either definition to drift while every
downstream theorem continued to elaborate against the changed abbreviation. -/

noncomputable example (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] :
    NormMatrixCStarCorona (fun n ↦ X n) =
      (BoundedMatrixSequence (fun n ↦ X n) ⧸
        nullMatrixSequenceIdeal (fun n ↦ X n) Filter.cofinite) :=
  rfl

noncomputable example (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] :
    CompleteSpace (NormMatrixCStarCorona (fun n ↦ X n)) :=
  inferInstance

noncomputable example (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] :
    NormedRing (NormMatrixCStarCorona (fun n ↦ X n)) :=
  inferInstance

noncomputable example (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] :
    NormedAlgebra ℂ (NormMatrixCStarCorona (fun n ↦ X n)) :=
  inferInstance

noncomputable example (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] :
    StarModule ℂ (NormMatrixCStarCorona (fun n ↦ X n)) :=
  inferInstance

noncomputable example (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] :
    CStarRing (NormMatrixCStarCorona (fun n ↦ X n)) :=
  inferInstance

noncomputable example (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] :
    CStarAlgebra (NormMatrixCStarCorona (fun n ↦ X n)) :=
  inferInstance

noncomputable example (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] :
    NormMatrixCoronaUnitary X ≃*
      unitary (NormMatrixCStarCorona (fun n ↦ X n)) :=
  normMatrixCoronaUnitaryEquiv X

noncomputable example (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (q : NormMatrixCoronaUnitary X) :
    normMatrixCoronaUnitaryEquiv X q =
      unitaryCoronaToCStarCoronaUnitary X q :=
  rfl

example (G : Type u) [Group G] [Countable G] :
    (∃ d : ℕ → ℕ, ∃ hd : ∀ n, 0 < d n,
      letI : ∀ n, Nonempty (naturalFiniteModel (d n)) := fun n ↦
        Fintype.card_pos_iff.mp (by simpa using hd n)
      StrictMono d ∧
        ∃ rho : G →* unitary (NormMatrixCStarCorona
          (fun n ↦ naturalFiniteModel (d n))), Function.Injective rho) ↔
      IsOperatorMF G := by
  simpa only [IsCDEOperatorMF] using isCDEOperatorMF_iff_isOperatorMF G

example {Gamma E : Type} [Group Gamma] [Group E] [Countable E]
    (C : KazhdanCompressionCore Gamma E)
    (F : Subgroup E) [Finite F] [F.Normal]
    (hF : F ≤ C.defectNormal)
    (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n)) :
    let hne : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (hX n)
    letI := hne
    ∀ rho : E →* unitary (NormMatrixCStarCorona (fun n ↦ X n)),
      F ≤ rho.ker := by
  dsimp only
  intro rho
  exact C.finiteNormal_le_normMatrixCStarCoronaKernel F hF X hX rho

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
its type: delete it, or prove its antecedent in the corpus and remove that
antecedent from the public statement.

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
   ``ChosenNonMFTheorem.exists_countable_finitelyPresented_not_isOperatorMF,
   ``ChosenNonMFTheorem.not_every_countable_group_isOperatorMF,
   ``ChosenNonMFTheorem.not_every_group_isOperatorMF,
   ``ChosenNonMFTheorem.not_every_finitelyPresented_group_isOperatorMF,
   ``ChosenMarkedPresentation.chosenFinitelyPresented_markedPackage,
   ``ChosenNonMFEndpoint.chosenFinitelyPresented_inclusionPackage,
   ``KazhdanCompressionCore.manuscriptCentralSignCriterion,
   ``LiteralP13HodgeCertificate.cleanP13Certificate,
   ``LiteralP13HodgeCertificate.p13_hodge_gap,
   ``LiteralP13HodgeCertificate.p13_generatorLaplacian_quadratic_gap,
   ``LiteralP13HodgeCertificate.manuscriptP13PropertyT,
   ``LiteralBaseP13PropertyTBridge.manuscriptBaseHasKazhdanPropertyT,
   ``LiteralNonMFEndpoint.mark_eq_compressionDefect_sq,
   ``LiteralNonMFEndpoint.kazhdanPinning,
   ``LiteralNonMFEndpoint.literal_mark_mem_manuscriptCoronaMFResidual,
   ``LiteralNonMFEndpoint.cliffordSign_blackHole,
   ``LiteralNonMFEndpoint.literal_failsEveryStandardMFConvention,
   ``LiteralNonMFEndpoint.literal_maximalGroupCStar_not_hasMFEmbedding,
   ``LiteralNonMFEndpoint.literal_maximalGroupCStar_not_isMFAlgebra,
   ``LiteralNonMFEndpoint.literal_reducedGroupCStar_not_hasMFEmbedding,
   ``LiteralNonMFEndpoint.literal_reducedGroupCStar_not_isMFAlgebra,
   ``LiteralNonMFEndpoint.manuscriptTheoremA,
   ``LiteralSixGenerator.literal_sixGenerated_finitelyPresented_nonMF,
   ``LiteralMarkedCylinder.literal_nonempty_clopen_nonMF_cylinder,
   ``LiteralWitnessConsequences.literalWitness_locallyFiniteKernel_nonMF,
   ``NonMFImpact.witness_reducedGroupCStar_stablyFinite_nonMF,
   ``NonMFImpact.affineBase_residuallyFinite_sofic_MF,
   ``NonMFImpact.scalingFamily_finitelyPresented_nonMF,
   ``NonMFImpact.cyclicBase_exactModel_obstruction,
   ``OperatorMFQuotientNonclosure.operatorMF_not_closed_under_this_quotient,
   ``LiteralUniformObstruction.literal_uniform_operatorNorm_obstruction,
   ``NonMFImpact.finiteNormal_obstruction_is_trivial_in_torsionFree_groups,
   ``NonMFImpact.sofic_nonMF_is_hyperlinear_nonMF,
   ``ManuscriptExactWrappers.manuscriptRadicalPortability,
   -- The collapse family.  These back printed theorems, so they belong on
   -- the roster the independent kernel re-check takes as roots; the
   -- namespace-wide axiom sweep below reaches them either way.
   ``ManuscriptExactWrappers.manuscriptInvolutiveCollapse,
   ``ManuscriptExactWrappers.manuscriptNormalKazhdanObstruction,
   ``ManuscriptExactWrappers.manuscriptAbstractNormalKazhdanObstruction,
   ``ManuscriptExactWrappers.manuscriptDefectSaturation,
   ``KazhdanCliffordConstruction.kazhdanCliffordConstruction,
   ``LiteralNonMFEndpoint.manuscriptTheoremD,
   ``LiteralBaseP13Replay.yFromUZXY_eq,
   ``LiteralBaseP13Replay.closure_Z_XY_eq_top,
   ``ExactHodgeCertificate.Certificate.hodge_gap,
   ``ExactHodgeCertificate.Certificate.isKazhdanPair,
   ``ExactHodgeCertificate.Certificate.hasKazhdanPropertyT,
   ``LiteralBaseP13RotationQuotient.p13GeneratorToRotation_kills,
   ``LiteralBaseP13RotationQuotient.p13ToRotation_surjective,
   ``KazhdanCompressionCore.finiteNormal_le_normMFResidual,
   ``KazhdanCompressionCore.finiteNormal_le_coronaMFResidual,
   ``KazhdanCompressionCore.finiteNormal_le_normMatrixCoronaKernel,
   ``normMatrixCStarCoronaQuotient,
   ``normMatrixCStarCoronaMk_eq_zero_iff,
   ``normMatrixCStarCoronaMk_surjective,
   ``normMatrixCStarCoronaCStarAlgebra,
   ``maximalGroupCStarUnitaryHom_injective,
   ``maximalGroupCStar_existsUnique_lift,
   ``maximalGroupCStar_not_hasMFEmbedding_of_not_isOperatorMF,
   ``maximalGroupCStar_not_isMFAlgebra_of_not_isOperatorMF,
   ``normMatrixCoronaUnitaryEquiv,
   ``unitaryCoronaToCStarCoronaUnitary_injective,
   ``unitaryCoronaToCStarCoronaUnitary_surjective,
   ``isCDEOperatorMF_iff_isOperatorMF,
   ``KazhdanCompressionCore.finiteNormal_le_normMatrixCStarCoronaKernel,
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
   ``OperatorNormAmplification.exists_tensorPower_pair_far,
   ``OperatorMFLocalNormalization.isOperatorMF_iff_isNormApproximable_one,
   ``MarkedGroupSpace.exists_wordBall_cylinder_subset_compl_operatorMFLocus,
   ``MarkedGroupSpace.isClosed_operatorMFLocus,
   ``MarkedGroupSpace.isOpen_compl_operatorMFLocus,
   ``MarkedGroupSpace.isOperatorMF_of_tendsto,
   ``not_injective_of_coronaMFInvisible,
   ``KazhdanCompressionCore.finiteNormal_uniform_invisibility,
   ``KazhdanCompressionCore.finiteNormal_uniform_invisibility_positiveModel,
   ``KazhdanCompressionCore.normalKazhdan_le_coronaMFResidual,
   ``FaithfulTracialState.matrix_mul_star_eq_one_of_star_mul_eq_one,
   ``ProperProjectionCompression.star_isometry_mul_eq_one_and_reverse_ne,
   ``ProperProjectionCompression.exists_leftInvertible_not_isUnit,
   ``ProperProjectionCompression.not_isDedekindFiniteMonoid,
   ``ProperProjectionCompression.not_isStablyFiniteRing,
   ``ProperProjectionCompression.no_faithfulTracialState,
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
   ``KunSpectral.no_uniform_spectral_gap,
   -- The undecidability endpoints.  The namespace sweep below already refuses a
   -- disallowed axiom in any of these, so adding them buys no new *safety*; what
   -- it buys is the per-theorem `logInfo` line above, which is the only place a
   -- CI log states what an individual endpoint rests on.  These six carry the
   -- claim that they are unconditional, and a bulk "no disallowed axioms" over
   -- the namespace is not that claim: it would read the same if one of them
   -- rested on an admission that some *other* declaration also carried.  The
   -- reported closure is the machine's form of the sentence each of them makes.
   ``Computability.not_computablePred_wordProblemPred,
   ``Computability.operatorMF_recognition_not_computable,
   ``WordProblemRE.rePred_wordProblemPred,
   ``WordProblemRE.not_rePred_compl_wordProblemPred,
   ``WordProblemRE.operatorMF_negative_side_not_re,
   ``CliffordBSAmenableMF.manuscriptSharpnessOfKazhdanHypothesis]

/-- Advertised closed endpoints.  A declaration on this list must have an
empty outer telescope.  Universally quantified mathematics belongs inside a
named `Prop`; the theorem itself may not accept data, typeclass instances, or
hypotheses from its caller. -/
def zeroInputEndpoints : List Name :=
  [``KazhdanCompressionCore.manuscriptCentralSignCriterion,
   ``KazhdanCliffordConstruction.kazhdanCliffordConstruction,
   ``LiteralNonMFEndpoint.manuscriptTheoremA,
   ``LiteralNonMFEndpoint.manuscriptTheoremD,
   ``LiteralSixGenerator.literal_sixGenerated_finitelyPresented_nonMF,
   ``LiteralMarkedCylinder.literal_nonempty_clopen_nonMF_cylinder,
   ``LiteralWitnessConsequences.literalWitness_locallyFiniteKernel_nonMF,
   ``NonMFImpact.witness_reducedGroupCStar_stablyFinite_nonMF,
   ``NonMFImpact.affineBase_residuallyFinite_sofic_MF,
   ``NonMFImpact.scalingFamily_finitelyPresented_nonMF,
   ``NonMFImpact.cyclicBase_exactModel_obstruction,
   ``OperatorMFQuotientNonclosure.operatorMF_not_closed_under_this_quotient,
   ``LiteralUniformObstruction.literal_uniform_operatorNorm_obstruction,
   ``NonMFImpact.finiteNormal_obstruction_is_trivial_in_torsionFree_groups,
   ``NonMFImpact.sofic_nonMF_is_hyperlinear_nonMF,
   -- The trace-class consequences.  `#print axioms` cannot see a premise that
   -- lives in the *statement* rather than the proof term, so the endpoints
   -- that the manuscript badges at `lem:mftrace-group` and `thm:trace` are
   -- routed through this semantic check, which reads the elaborated type and
   -- so also catches a section `variable` that the printed header does not
   -- show.
   ``LiteralTraceConsequence.markedGroup_canonicalMaximalTrace_not_isMFTrace,
   ``LiteralTraceConsequence.markedGroup_separable_tracialState_not_isMFTrace,
   ``LiteralTraceConsequence.markedGroup_not_isMFRegularCharacter,
   ``LiteralTraceConsequence.markedGroup_canonicalTrace_isHyperlinearTrace_not_isMFTrace,
   ``LiteralTraceConsequence.markedGroup_separable_canonicalTrace_hyperlinear_not_isMFTrace,
   ``GroupApproximation.manuscriptMFTraceGroupBridge,
   ``ShulmanTrace.canonicalMaximalTrace_isHyperlinearTrace_of_isSofic]

/-- Does an elaborated declaration type still expose an outer input? -/
def hasLeadingInput : Expr → Bool
  | .forallE .. => true
  | .mdata _ body => hasLeadingInput body
  | _ => false

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

  for n in zeroInputEndpoints do
    let some ci := env.find? n
      | throwError "zero-input endpoint `{n}` does not exist in the environment"
    if hasLeadingInput ci.type then
      throwError "advertised endpoint `{n}` has a leading declaration input; \
route its universal sentence through a named closed proposition"

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

/-! ## 2b. Route guards: printed-route proofs must stay printed-route

A ledger row that grades a proof `EXACT` is a claim about the *route*, not
only the type: the cited endpoint traverses the manuscript's printed
argument.  Nothing above checks that.  The axiom sweep would stay green, and
every type-level gate would stay green, if a refactor re-proved an endpoint
through an alternate route while leaving its statement byte-identical -- the
exact silent regression the ledger's route rows exist to prevent, performed
by accident.

Each pair below pins an endpoint to a declaration its proof must reach: the
dependency closure of the endpoint (types and proof terms, the same notion
the kernel's axiom collector walks) must contain the pinned declaration.  A
pair is added when a ledger row records that an endpoint travels a printed
route through a named declaration, and retired only together with that row.
The guard is one-sided by design: it cannot certify that a proof *is* the
printed argument -- that judgment stays human, in the ledger -- but it makes
the recorded judgment refutable by machine when the dependency disappears. -/

/-- The pinned (endpoint, required-dependency) pairs.  Sources: the `FN.03`
and `TA.11` ledger rows, whose notes record that these endpoints travel the
printed ultraproduct transport rather than the finite-stage corner. -/
def routeGuards : List (Name × Name) :=
  [ -- FN.03: the pinning endpoint consumes the printed-route seam ...
    (`GroupApproximation.LiteralNonMFEndpoint.kazhdanPinning,
     `GroupApproximation.UltraproductRigidityRoute.compressionDefects_hsTrivial_literal),
    -- ... and through it the printed `thm:kazhdan-transport` itself.
    (`GroupApproximation.LiteralNonMFEndpoint.kazhdanPinning,
     `GroupApproximation.KazhdanAsymptoticCommutant.manuscriptKazhdanTransport),
    -- TA.11: the negative-corner contradiction shares that transport step.
    (`GroupApproximation.LiteralNonMFEndpoint.negativeCorner_kazhdanTransport_contradiction,
     `GroupApproximation.KazhdanAsymptoticCommutant.manuscriptKazhdanTransport),
    -- PRE.11: the manuscript lifting wrapper travels the printed four-move
    -- patching route rather than the corona-quotient surjection.
    (`GroupApproximation.ManuscriptExactWrappers.manuscriptUnitaryLifting,
     `GroupApproximation.PrintedLiftingSteps.exists_boundedLift_polarPatch),
    -- KC.02: the general Kazhdan-Clifford construction's negative corner
    -- reaches its rigidity through the printed transport ...
    (`GroupApproximation.KazhdanCliffordConstruction.negativeCorner_kazhdanTransport_contradiction,
     `GroupApproximation.KazhdanAsymptoticCommutant.manuscriptKazhdanTransport),
    -- ... and so, now, does the row's cited headline.  Its rigidity arrives
    -- through the central-sign criterion, and the criterion it travels is the
    -- printed-route inhabitant of that closed proposition, not the
    -- finite-stage one.  Both pins are kept: the second is the row's subject,
    -- the first is the sentence the row quotes.
    (`GroupApproximation.KazhdanCliffordConstruction.kazhdanCliffordConstruction,
     `GroupApproximation.PrintedCentralSign.manuscriptCentralSignCriterionPrinted),
    (`GroupApproximation.KazhdanCliffordConstruction.kazhdanCliffordConstruction,
     `GroupApproximation.KazhdanAsymptoticCommutant.manuscriptKazhdanTransport),
    -- PA.05: the literal application of the criterion instantiates the printed
    -- inhabitant of it, not the finite-stage one.  The row grades the
    -- instantiation and its data, which the swap leaves untouched; this pins
    -- which inhabitant is instantiated.
    (`GroupApproximation.LiteralNonMFEndpoint.literal_centralSignCriterion,
     `GroupApproximation.PrintedCentralSign.manuscriptCentralSignCriterionPrinted),
    -- ID.06: the printed reverse step of `cor:generaltransport` is the exact
    -- identity `P = VPV* ⟹ V*PV = P`, so the reverse-transport endpoint must
    -- depend on it and not only on the approximate leakage bound ...
    (`GroupApproximation.KazhdanAsymptoticCommutant.transport_star_printed,
     `GroupApproximation.PrintedReverseTransport.star_conj_eq_of_conj_eq),
    -- ... and the corollary's own shape, which a badge would cite, likewise.
    (`GroupApproximation.KazhdanAsymptoticCommutant.compressionGroup_transport_both_printed,
     `GroupApproximation.PrintedReverseTransport.star_conj_eq_of_conj_eq),
    -- TR.05: the trace theorem's printed intermediate object is the tracial
    -- quotient along a free ultrafilter, and the extension step is the printed
    -- universal property rather than a second construction.
    (`GroupApproximation.ShulmanTrace.canonicalMaximalTrace_factorsThrough_tracialUltraproduct,
     `GroupApproximation.canonicalMaximalTrace_factorsThrough),
    -- INT.03: the row's complaint was that no single declaration carried both
    -- the printed `ω` route and the any-universe statement, so one declaration
    -- is pinned to both properties.  The route: its ambient is the weighted
    -- `B_ω` model built from the theorem's own data, not the cofinite corona ...
    (`GroupApproximation.OmegaRouteManuscriptTransport.manuscriptKazhdanTransport_omegaRoute_anyUniverse,
     `GroupApproximation.OmegaWeightedAmbient.omegaWeightedAmbient),
    -- ... and the universes: the Kazhdan source is freed through countability
    -- of a property-`(T)` group, which is what lets it be moved to its `Type 0`
    -- model rather than assumed to live there.
    (`GroupApproximation.OmegaRouteManuscriptTransport.manuscriptKazhdanTransport_omegaRoute_anyUniverse,
     `GroupApproximation.countable_of_hasKazhdanPropertyTComplex),
    -- KT.01: the printed proof of `thm:kazhdan-transport` opens by
    -- contradiction -- "suppose the conclusion fails: there are `γ₀`, `δ > 0`
    -- and an infinite `I` with the commutator at least `δ` on `I`" -- and the
    -- badged theorem used to reach the same conclusion directly, through the
    -- generic skeleton, leaving that opening stated and unconsumed.  It is
    -- consumed now, at the printed objects ...
    (`GroupApproximation.KazhdanAsymptoticCommutant.manuscriptKazhdanTransport,
     `GroupApproximation.PrintedTransportOpening.exists_gamma_infinite_commutator_defect),
    -- ... and so is the sentence after it, "fix a free ultrafilter `ω` on `ℕ`
    -- with `I ∈ ω`", which is where the printed proof's `ω` comes from.  Both
    -- pins are kept: the contradiction is the route, and the choice of `ω` is
    -- what makes it a contradiction rather than a second direct argument.
    (`GroupApproximation.KazhdanAsymptoticCommutant.manuscriptKazhdanTransport,
     `GroupApproximation.UltrafilterLimit.exists_freeUltrafilter_mem),
    -- CO.04/CO.20/CO.21/CO.21b: the manuscript projection-collapse theorem is
    -- proved by the printed corona route -- the join of the displacement
    -- supports, the rank-normalized `Λ`, the displacement cocycle, and the
    -- Delorme--Guichardet contradiction -- rather than by bootstrapping the
    -- finite-stage involutive endpoint through the sign `w = 1 - 2p` ...
    (`GroupApproximation.ProjectionCompressionCollapse.corona_projection_collapse,
     `GroupApproximation.CollapsePrintedProjectionCollapse.printed_projection_collapse),
    -- ... whose contradiction is the printed one, with ideal membership held
    -- only where the print proves it ...
    (`GroupApproximation.ProjectionCompressionCollapse.corona_projection_collapse,
     `GroupApproximation.CollapseKqAlmostRep.collapse_contradiction_localized_Kq),
    -- CO.21/CO.21b: and it runs there, on the printed closed invariant
    -- subspace, not on the ambient `K_ω`.  Pinning `Kq` itself is what makes
    -- "the printed space" a checked claim rather than a described one.
    (`GroupApproximation.ProjectionCompressionCollapse.corona_projection_collapse,
     `GroupApproximation.CollapseInvariantSubspace.Kq),
    -- ... and whose last paragraph is the Delorme form with the coboundary
    -- proved from property (T), `htransport` proved, and `π` built.
    (`GroupApproximation.ProjectionCompressionCollapse.corona_projection_collapse,
     `GroupApproximation.CollapseTransportEndpoint.transport_corona),
    -- CO.04: the badged `thm:collapse` travels the printed derivation --
    -- `p = ½(1 − Θ(k))`, then `thm:projection-collapse` -- rather than the
    -- finite-stage involutive endpoint, so the printed logical order is the
    -- formal dependency order.
    (`GroupApproximation.ManuscriptExactWrappers.manuscriptInvolutiveCollapse,
     `GroupApproximation.ProjectionCompressionCollapse.corona_projection_collapse),
    -- LI.19: the printed sentence "thm:kazhdan-transport uses finite
    -- dimensionality of M_d twice, for the conjugation action on
    -- L²(M_d, tr_d) and for finiteness of the norm ultraproduct".  Which facts
    -- a proof consumes is not a proposition, so it is pinned rather than
    -- stated: these two pairs are that sentence, machine-checked, and a
    -- re-route turns the audit red instead of leaving the sentence asserted.
    -- The conjugation action, realized at the doubled index `Y × Y` that is
    -- finite exactly because `Y` is ...
    (`GroupApproximation.KazhdanAsymptoticCommutant.manuscriptKazhdanTransport,
     `GroupApproximation.UltraproductModelConstruction.rowMat_conjDouble_mulVec),
    -- ... and finiteness, consumed where the compression step needs a
    -- Dedekind-finite ambient.  `Analysis/PrintedFiniteDimensionalUses` proves
    -- that neither survives the replacement Question 5 proposes.
    (`GroupApproximation.KazhdanAsymptoticCommutant.manuscriptKazhdanTransport,
     `GroupApproximation.ProperProjectionCompression.unitary_conjugate_eq_of_absorbs) ]

/-- Does the dependency closure of `root` contain `target`?  A depth-first
walk over `ConstantInfo.getUsedConstantsAsSet`, which visits types and proof
terms alike -- the same reachability the kernel's axiom collector uses. -/
partial def closureContainsGo (env : Environment) (target : Name)
    (visited : NameSet) : List Name → Bool
  | [] => false
  | n :: rest =>
    if n == target then true
    else if visited.contains n then closureContainsGo env target visited rest
    else
      let visited := visited.insert n
      match env.find? n with
      | some ci =>
          closureContainsGo env target visited
            (ci.getUsedConstantsAsSet.toList ++ rest)
      | none => closureContainsGo env target visited rest

def closureContains (env : Environment) (root target : Name) : Bool :=
  closureContainsGo env target {} [root]

run_cmd do
  let env ← getEnv
  for (endpoint, required) in routeGuards do
    unless env.contains endpoint do
      throwError "route guard: endpoint `{endpoint}` does not exist in the \
environment"
    unless env.contains required do
      throwError "route guard: required dependency `{required}` does not \
exist in the environment"
    unless closureContains env endpoint required do
      throwError "route guard: `{endpoint}` no longer depends on \
`{required}`.  Its statement may be unchanged, but the proof no longer \
travels the printed route the ledger records for it; restore the route, or \
regrade the ledger row and retire this pair in the same commit"
  logInfo m!"route guards: {routeGuards.length} dependency pin(s) hold"

/-! ### The literature quarantine

`literatureInputNames` refuses a *tagged* premise anywhere in the corpus, and
it is empty because nothing in the corpus is tagged.  It cannot express the
rule that actually governs here.  Several modules formalize a printed route by
taking the external theorem it cites as a typed **package** -- a structure, or
a `Prop`, whose content is a theorem this repository does not prove -- and
proving everything downstream of it.  `Sofic/FournierFacioUniversalGroup`
takes Fournier-Facio's group apart into two such packages and proves the step
that joins them; that is worth more than an opaque citation, not less, and
tagging the packages would make it illegal.  The rule is narrower and sharper:
such a package may exist in the tree, and must never appear in the *statement*
of anything this development advertises as a result.

That is what the roster and the walk below enforce.  The walk is over the
**type**, not the proof term, and this is the load-bearing choice.  Reaching a
package from a proof term is not a defect: a closed theorem whose proof
mentions one must have *built* one, and the kernel already guarantees the
conclusion.  Reaching one from a statement is the defect, because that is a
conditional result wearing a clean axiom report -- the implication is
genuinely proved, and it assumes the citation anyway.

What this catches that `zeroInputEndpoints` does not: that check refuses a
leading binder, so it sees `DefectRoutingData D -> P` and does not see a
statement that mentions a *named* `Prop` which itself quantifies over one.
The walk unfolds through definitions, so the name buys no cover. -/

/-- Corpus-defined packages whose content is a theorem of the literature this
repository does not prove.  Each entry names the paper it transcribes.

The roster is under the same custody as `allowedAxioms` and
`literatureInputNames`: it lives in the lint, so the corpus cannot quietly
remove its own quarantine.  **An entry is retired only by proving it**, in
which case the same commit deletes the line; an entry that stops existing in
the environment fails the run rather than being skipped. -/
def literaturePackages : List Name :=
  [-- Tikuisis--White--Winter, Ann. of Math. (2) 185 (2017) 229--284, and the
   -- two inputs its group-level corollary needs: Lance (nuclearity of the
   -- reduced algebra of an amenable group) and Tu (the UCT for it).
   ``QuasidiagonalMF.TikuisisWhiteWinterInput,
   ``QuasidiagonalMF.AmenableNuclearInput,
   ``QuasidiagonalMF.AmenableUCTInput,
   ``QuasidiagonalMF.AmenableMFInput,
   ``CyclicBaseCalibration.AmenableImpliesMF,
   -- Fournier-Facio's universal finitely presented torsion-free property-(T)
   -- group, arXiv:2608.02025 sec. 2, and the two theorems it is built from:
   -- Chiodo/Belegradek (the universal torsion-free host) and Osin (small
   -- cancellation over a relatively hyperbolic pair).
   ``ContainsSquareWitness.UniversalFPTorsionFree,
   ``FournierFacioUniversal.UniversalKazhdanGroup,
   ``FournierFacioUniversal.UniversalTorsionFreeHost,
   ``FournierFacioUniversal.KazhdanEnvelope,
   ``SmallCancellationEnvelope.HyperbolicKazhdanPartner,
   -- Greendlinger's lemma for C'(1/6).  The one entry here that is a
   -- self-contained combinatorial theorem rather than a research programme:
   -- `Sofic/Greendlinger*` proves it for expressions with at most two
   -- conjugate factors, and the three-factor induction is what is left.
   ``SmallCancellationRouter.GreendlingerGate,
   ``SmallCancellationRouter.RoutingLemmaData,
   -- Hull's common-quotient theorem (Groups Geom. Dyn. 10 (2016) 1077--1119)
   -- and Osin (Trans. AMS 368 (2016) 851--888), as the routing data the
   -- full-MF-radical endpoints quantify over.
   ``DefectRoutingData,
   ``OrderPreservingRoutingData,
   ``FiveConditionRoutingData,
   ``RelativeCommonQuotientData,
   ``FournierFacioDefectData,
   -- Kun--Thom and Shulman, as the double-construction datum.
   ``KunThomShulmanDoubleData,
   -- Adian--Rabin, as reduction data for the C*-recognition consequences.
   ``CStarRecognitionConsequences.GroupCStarAdianRabinReductions]

/-- Every constant reachable from `seeds`, unfolding through the type *and*
the value of everything it meets.  Same reachability as `closureContainsGo`;
what differs is where the quarantine seeds it -- see `statementConstants`. -/
partial def reachableFrom (env : Environment) (visited : NameSet) :
    List Name → NameSet
  | [] => visited
  | n :: rest =>
    if visited.contains n then reachableFrom env visited rest
    else
      let visited := visited.insert n
      match env.find? n with
      | some ci =>
          -- A structure's own `ConstantInfo` mentions only the constants of
          -- its *sort*, so a package reached only through a field would be
          -- invisible without this: the fields live in the constructor's
          -- type.  `MainTheoremData D` names `FournierFacioDefectData` this
          -- way and no other.
          let ctors := match ci with
            | .inductInfo iv => iv.ctors
            | _ => []
          reachableFrom env visited
            (ci.getUsedConstantsAsSet.toList ++ ctors ++ rest)
      | none => reachableFrom env visited rest

/-- The constants of a declaration's **type**, which is where the quarantine
walk starts.  Seeding at the declaration itself would drag in its proof term,
and a proof term is allowed to mention a package: it would have had to build
one, and the kernel has already checked the conclusion. -/
def statementConstants (env : Environment) (n : Name) : List Name :=
  match env.find? n with
  | some ci => ci.type.getUsedConstants.toList
  | none => []

run_cmd do
  let env ← getEnv
  for pkg in literaturePackages do
    unless env.contains pkg do
      throwError "literature quarantine: `{pkg}` does not exist in the \
environment.  A quarantine roster cannot outlive the name it quarantines: \
either restore the package, or delete this line together with whatever \
replaced it"
  let roots := headlineTheorems ++ zeroInputEndpoints
  let mut breaches : Array String := #[]
  for r in roots do
    unless env.contains r do
      throwError "literature quarantine: advertised result `{r}` does not \
exist in the environment"
    let reachable := reachableFrom env {} (statementConstants env r)
    let hits := literaturePackages.filter (fun p => reachable.contains p)
    unless hits.isEmpty do
      breaches := breaches.push s!"{r} states: {hits}"
  unless breaches.isEmpty do
    throwError "literature quarantine breached: the statement of an \
advertised result mentions a package this repository does not prove.  Such a \
result is conditional on a citation however clean its axiom report; either it \
must stop being advertised, or its premise must be proved in the corpus and \
removed from the statement:{Format.line}\
{Format.joinSep breaches.toList Format.line}"
  logInfo m!"literature quarantine: {literaturePackages.length} unproved \
package(s), none named by the statement of any of the {roots.length} \
advertised result(s)"

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

/-- The verdict, factored out of the scan commands.  Each scan command below
reports its own findings through this; a finding anywhere is a failure, which
is the same verdict the single command used to reach. -/
def reportFindings (label : String) (findings : Array Audit.Finding) :
    CommandElabM Unit := do
  for tag in scanTags do
    logInfo m!"{label} {tag}: {(findings.filter (fun f => f.tag == tag)).size}"

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

/-- How many commands the declaration scan is split across.

The scan is one pass over every theorem in the corpus, doing a
`forallTelescope` and an `inferType` per binder, and its cost grows with the
corpus.  At ~45k declarations it exceeded the 200000-heartbeat budget of a
single elaboration command and the whole audit died at `whnf`, with the
route guards and the allowed-constant check already green, so the failure
was in the finding scan and not in the mathematics.  Heartbeats are charged per command,
so splitting the pass across several commands gives each slice its own budget
and changes nothing about what is checked.  Raising `maxHeartbeats` instead is
both blocked by `scripts/check.py` and the wrong fix: the cost is real and
grows, and a bigger budget only moves the cliff. -/
def declScanChunks : Nat := 6

run_cmd do
  let env ← getEnv
  let findings := Audit.axiomScan env
      (Audit.corpusNames env `GroupApproximation) allowedAxioms
    ++ Audit.literatureScan env `GroupApproximation literatureInputNames
  reportFindings "axiom+literature" findings

run_cmd do
  let env ← getEnv
  let names := Audit.corpusNames env `GroupApproximation
  let width := names.size / declScanChunks + 1
  let slice := names.extract (0 * width) (min ((0 + 1) * width) names.size)
  unless slice.isEmpty do
    let findings ← liftTermElabM <| Audit.declScan env slice
    reportFindings "decl[0]" findings

run_cmd do
  let env ← getEnv
  let names := Audit.corpusNames env `GroupApproximation
  let width := names.size / declScanChunks + 1
  let slice := names.extract (1 * width) (min ((1 + 1) * width) names.size)
  unless slice.isEmpty do
    let findings ← liftTermElabM <| Audit.declScan env slice
    reportFindings "decl[1]" findings

run_cmd do
  let env ← getEnv
  let names := Audit.corpusNames env `GroupApproximation
  let width := names.size / declScanChunks + 1
  let slice := names.extract (2 * width) (min ((2 + 1) * width) names.size)
  unless slice.isEmpty do
    let findings ← liftTermElabM <| Audit.declScan env slice
    reportFindings "decl[2]" findings

run_cmd do
  let env ← getEnv
  let names := Audit.corpusNames env `GroupApproximation
  let width := names.size / declScanChunks + 1
  let slice := names.extract (3 * width) (min ((3 + 1) * width) names.size)
  unless slice.isEmpty do
    let findings ← liftTermElabM <| Audit.declScan env slice
    reportFindings "decl[3]" findings

run_cmd do
  let env ← getEnv
  let names := Audit.corpusNames env `GroupApproximation
  let width := names.size / declScanChunks + 1
  let slice := names.extract (4 * width) (min ((4 + 1) * width) names.size)
  unless slice.isEmpty do
    let findings ← liftTermElabM <| Audit.declScan env slice
    reportFindings "decl[4]" findings

run_cmd do
  let env ← getEnv
  let names := Audit.corpusNames env `GroupApproximation
  let width := names.size / declScanChunks + 1
  let slice := names.extract (5 * width) (min ((5 + 1) * width) names.size)
  unless slice.isEmpty do
    let findings ← liftTermElabM <| Audit.declScan env slice
    reportFindings "decl[5]" findings

end GroupApproximation.Audit
