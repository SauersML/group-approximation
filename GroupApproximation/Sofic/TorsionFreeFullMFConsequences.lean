import GroupApproximation.Sofic.TorsionFreeFullMFRadical
import GroupApproximation.Algebra.TwoGeneratedFreeQuotient
import GroupApproximation.Criterion.CriterionAssembly
import GroupApproximation.Sofic.SoficTransfer
import GroupApproximation.Sofic.FreeGroupResiduallyFinite
import GroupApproximation.Monsters.TwoConjugacyClasses

/-!
# Consequences of the torsion-free full-MF-radical construction

This file formalizes the group-theoretic applications which can be stated in
the present library.  The external construction theorems are represented by
proof-carrying data, never by axioms:

* `NonsoficCriterionData` is the precise Fournier--Facio compression setup and
  non-LEF witness consumed by the already formalized nonsoficity criterion;
* `TwoConjugacyClassQuotientData` records the output of Hull's two-conjugacy-
  class quotient construction;
* `SimpleEnvelopeData` records the embedding into a simple torsion-free
  envelope;
* `UniversalContainerData` records an SQ-universal quotient which contains
  both a requested countable group and a copy of the original routed group.

The theorems below prove all radical, property-`(T)`, simplicity, and
nonsoficity conclusions from those interfaces.  Existence of the interfaces
is exactly the acylindrical-small-cancellation boundary absent from Mathlib.
-/

namespace GroupApproximation

universe u v w

namespace DefectRoutingData

variable {P : Type} {E : Type u} [Group P] [Group E]
    {D : FournierFacioDefectData P E}
    (R : DefectRoutingData.{u} D)

local instance nonsoficRoutingQuotientGroup : Group R.Quotient := R.groupQuotient

/-! ## The Fournier--Facio nonsoficity endpoint -/

/-- The exact input needed to apply the formalized compression criterion to
the routed quotient.  In the manuscript, `Gamma` is the image of the Kazhdan
base and `J` is the conjugate of the embedded infinite simple group. -/
structure NonsoficCriterionData where
  Gamma : Type
  J : Type
  [groupGamma : Group Gamma]
  [groupJ : Group J]
  [countableGamma : Countable Gamma]
  [countableJ : Countable J]
  setup : CompressionSetup R.Quotient Gamma J
  gammaKazhdan : HasKazhdanPropertyT.{0, 0} Gamma
  witness_not_isLEF : ¬ IsLEF J

namespace NonsoficCriterionData

/-- The Fournier--Facio criterion makes the routed quotient nonsofic. -/
theorem not_isSofic (N : NonsoficCriterionData R) : ¬ IsSofic R.Quotient := by
  letI : Group N.Gamma := N.groupGamma
  letI : Group N.J := N.groupJ
  letI : Countable N.Gamma := N.countableGamma
  letI : Countable N.J := N.countableJ
  letI : Countable R.Quotient := R.quotientCountable
  exact not_isSofic_of_not_isLEF
    (NonsoficCriterionData.setup N) R.kazhdan
    (NonsoficCriterionData.gammaKazhdan N)
    (NonsoficCriterionData.witness_not_isLEF N)

end NonsoficCriterionData

/-- Complete proof-carrying input for the part of the manuscript's main
theorem expressible in the current library.  Acylindrical hyperbolicity is not
included because it has no definition in Mathlib. -/
structure MainTheoremData (D : FournierFacioDefectData P E) where
  routing : DefectRoutingData D
  nonsofic : NonsoficCriterionData routing

namespace MainTheoremData

variable (M : MainTheoremData D)

local instance mainTheoremQuotientGroup : Group M.routing.Quotient :=
  M.routing.groupQuotient
local instance mainTheoremQuotientCountable : Countable M.routing.Quotient :=
  M.routing.quotientCountable

/-- The combined main-theorem package: finite presentation, two-generation,
torsion-freeness, property `(T)`, full group-element MF radical, failure of
group-element MF, and nonsoficity. -/
theorem consequence_package :
    Group.IsFinitelyPresented M.routing.Quotient ∧
      IsTwoGenerated M.routing.Quotient ∧
      IsPowerTorsionFree M.routing.Quotient ∧
      HasKazhdanPropertyT.{0, 0} M.routing.Quotient ∧
      cdeMFResidual M.routing.Quotient = ⊤ ∧
      ¬ IsOperatorMF M.routing.Quotient ∧
      ¬ IsCDEOperatorMF M.routing.Quotient ∧
      ¬ IsSofic M.routing.Quotient := by
  have hcore := M.routing.consequence_package
  exact ⟨hcore.1, hcore.2.1, hcore.2.2.1, hcore.2.2.2.1,
    hcore.2.2.2.2.1, hcore.2.2.2.2.2.1,
    hcore.2.2.2.2.2.2,
    M.nonsofic.not_isSofic⟩

end MainTheoremData

/-! ## The two-generator free-group quotient -/

/-- The map from the rank-two free group determined by the two routed
generators. -/
def freeGroupTwoQuotientMap : FreeGroup (Fin 2) →* R.Quotient :=
  twoGeneratorFreeGroupMap R.generatorOne R.generatorTwo

/-- The rank-two free-group map is onto because the selected pair generates
the routed quotient. -/
theorem freeGroupTwoQuotientMap_surjective :
    Function.Surjective R.freeGroupTwoQuotientMap :=
  twoGeneratorFreeGroupMap_surjective R.generates

/-- Operator-MF is not quotient-closed even with the rank-two free group as
source and a finitely presented torsion-free target. -/
theorem freeGroupTwo_operatorMF_quotient_package :
    IsOperatorMF (FreeGroup (Fin 2)) ∧
      Function.Surjective R.freeGroupTwoQuotientMap ∧
      Group.IsFinitelyPresented R.Quotient ∧
      IsPowerTorsionFree R.Quotient ∧
      ¬ IsOperatorMF R.Quotient :=
  ⟨isOperatorMF_of_residuallyFinite,
    R.freeGroupTwoQuotientMap_surjective, R.finitelyPresented,
    R.torsionFree, R.not_isOperatorMF⟩

/-! ## Hull's two-conjugacy-class quotient -/

/-- Proof-carrying output of the two-conjugacy-class quotient construction. -/
structure TwoConjugacyClassQuotientData where
  Carrier : Type
  [groupCarrier : Group Carrier]
  quotient : R.Quotient →* Carrier
  quotient_surjective : Function.Surjective quotient
  infinite : Infinite Carrier
  twoConjugacyClasses : Monsters.HasTwoConjugacyClasses Carrier
  twoGenerated : IsTwoGenerated Carrier
  torsionFree : IsPowerTorsionFree Carrier

namespace TwoConjugacyClassQuotientData

variable (C : TwoConjugacyClassQuotientData R)

local instance twoClassCarrierGroup : Group C.Carrier := C.groupCarrier
local instance twoClassCarrierInfinite : Infinite C.Carrier := C.infinite
local instance twoClassSourceCountable : Countable R.Quotient :=
  R.quotientCountable
local instance twoClassCarrierCountable : Countable C.Carrier :=
  C.quotient_surjective.countable

/-- Property `(T)` passes to the two-conjugacy-class quotient. -/
theorem kazhdan : HasKazhdanPropertyT.{0, 0} C.Carrier :=
  HasKazhdanPropertyT.of_surjective C.quotient C.quotient_surjective R.kazhdan

/-- The quotient again has full corona MF radical. -/
theorem coronaMFResidual_eq_top : coronaMFResidual C.Carrier = ⊤ :=
  R.quotient_coronaMFResidual_eq_top C.quotient C.quotient_surjective

/-- Literal CDE-corona radical form of the quotient theorem. -/
theorem cdeMFResidual_eq_top : cdeMFResidual C.Carrier = ⊤ := by
  rw [cdeMFResidual_eq_coronaMFResidual]
  exact C.coronaMFResidual_eq_top

/-- A group with exactly two conjugacy classes is simple. -/
theorem isSimpleGroup : IsSimpleGroup C.Carrier :=
  C.twoConjugacyClasses.isSimpleGroup

/-- The infinite two-conjugacy-class quotient is non-MF. -/
theorem not_isOperatorMF : ¬ IsOperatorMF C.Carrier := by
  letI : Nontrivial C.Carrier := C.twoConjugacyClasses.nontrivial
  exact R.quotient_not_isOperatorMF C.quotient C.quotient_surjective

/-- Literal CDE formulation for the two-conjugacy-class quotient. -/
theorem not_isCDEOperatorMF : ¬ IsCDEOperatorMF C.Carrier := by
  letI : Nontrivial C.Carrier := C.twoConjugacyClasses.nontrivial
  exact R.quotient_not_isCDEOperatorMF C.quotient C.quotient_surjective

/-- The formally verified package attached to Hull's quotient output. -/
theorem consequence_package :
    IsSimpleGroup C.Carrier ∧
      IsTwoGenerated C.Carrier ∧
      IsPowerTorsionFree C.Carrier ∧
      HasKazhdanPropertyT.{0, 0} C.Carrier ∧
      cdeMFResidual C.Carrier = ⊤ ∧
      ¬ IsOperatorMF C.Carrier ∧
      ¬ IsCDEOperatorMF C.Carrier :=
  ⟨C.isSimpleGroup, C.twoGenerated, C.torsionFree, C.kazhdan,
    C.cdeMFResidual_eq_top, C.not_isOperatorMF, C.not_isCDEOperatorMF⟩

end TwoConjugacyClassQuotientData

/-! ## Simple torsion-free envelopes -/

/-- Proof-carrying output of a relative simple-envelope theorem. -/
structure SimpleEnvelopeData where
  Envelope : Type
  [groupEnvelope : Group Envelope]
  [countableEnvelope : Countable Envelope]
  [simpleEnvelope : IsSimpleGroup Envelope]
  embedding : R.Quotient →* Envelope
  embedding_injective : Function.Injective embedding
  finitelyGenerated : Group.FG Envelope
  torsionFree : IsPowerTorsionFree Envelope

namespace SimpleEnvelopeData

variable (S : SimpleEnvelopeData R)

local instance simpleEnvelopeGroup : Group S.Envelope := S.groupEnvelope
local instance simpleEnvelopeCountable : Countable S.Envelope :=
  S.countableEnvelope
local instance simpleEnvelopeSimple : IsSimpleGroup S.Envelope :=
  S.simpleEnvelope

/-- The simple envelope has full norm-MF residual.  Functoriality first gives
a nontrivial invisible element; simplicity then saturates the residual. -/
theorem normMFResidual_eq_top : normMFResidual S.Envelope = ⊤ := by
  letI : Countable R.Quotient := R.quotientCountable
  have hs : R.quotient D.s ∈ normMFResidual R.Quotient := by
    rw [R.normMFResidual_eq_top]
    exact Subgroup.mem_top _
  have himage : S.embedding (R.quotient D.s) ∈ normMFResidual S.Envelope :=
    map_normMFResidual_le S.embedding ⟨R.quotient D.s, hs, rfl⟩
  have hne : S.embedding (R.quotient D.s) ≠ 1 := by
    intro h
    apply R.protected_ne_one
    apply S.embedding_injective
    simpa using h
  exact normMFResidual_eq_top_of_simple himage hne

/-- The same full radical stated directly with genuine CDE coronas. -/
theorem cdeMFResidual_eq_top : cdeMFResidual S.Envelope = ⊤ := by
  rw [cdeMFResidual_eq_normMFResidual]
  exact S.normMFResidual_eq_top

/-- The simple envelope is non-MF. -/
theorem not_isOperatorMF : ¬ IsOperatorMF S.Envelope := by
  letI : Nontrivial S.Envelope :=
    ⟨⟨S.embedding (R.quotient D.s), 1, by
      intro h
      apply R.protected_ne_one
      apply S.embedding_injective
      simpa using h⟩⟩
  intro hMF
  have hbot : normMFResidual S.Envelope = ⊥ :=
    normMFResidual_eq_bot_of_isOperatorMF hMF
  have htopbot : (⊤ : Subgroup S.Envelope) = ⊥ := by
    rw [← S.normMFResidual_eq_top]
    exact hbot
  exact top_ne_bot htopbot

/-- Literal CDE formulation for the simple envelope. -/
theorem not_isCDEOperatorMF : ¬ IsCDEOperatorMF S.Envelope := by
  rw [isCDEOperatorMF_iff_isOperatorMF]
  exact S.not_isOperatorMF

/-- A nonsofic routed group cannot embed into a sofic envelope. -/
theorem not_isSofic (hR : ¬ IsSofic R.Quotient) : ¬ IsSofic S.Envelope := by
  intro hS
  exact hR (isSofic_of_injective S.embedding S.embedding_injective hS)

/-- The verified simple-envelope package. -/
theorem consequence_package :
    Group.FG S.Envelope ∧
      IsPowerTorsionFree S.Envelope ∧
      IsSimpleGroup S.Envelope ∧
      cdeMFResidual S.Envelope = ⊤ ∧
      ¬ IsOperatorMF S.Envelope ∧
      ¬ IsCDEOperatorMF S.Envelope :=
  ⟨S.finitelyGenerated, S.torsionFree, S.simpleEnvelope,
    S.cdeMFResidual_eq_top, S.not_isOperatorMF, S.not_isCDEOperatorMF⟩

end SimpleEnvelopeData

/-! ## SQ-universal containers -/

/-- Data supplied by SQ-universality for a requested group `L`.  The
container is a quotient of the routed group, while separately containing
copies of both `L` and the routed group. -/
structure UniversalContainerData (L : Type v) [Group L] where
  Container : Type w
  [groupContainer : Group Container]
  quotient : R.Quotient →* Container
  quotient_surjective : Function.Surjective quotient
  requestedEmbedding : L →* Container
  requestedEmbedding_injective : Function.Injective requestedEmbedding
  sourceEmbedding : R.Quotient →* Container
  sourceEmbedding_injective : Function.Injective sourceEmbedding
  twoGenerated : IsTwoGenerated Container

namespace UniversalContainerData

variable {L : Type v} [Group L] (U : UniversalContainerData R L)

local instance universalContainerGroup : Group U.Container := U.groupContainer
local instance universalContainerSourceCountable : Countable R.Quotient :=
  R.quotientCountable
local instance universalContainerCountable : Countable U.Container :=
  U.quotient_surjective.countable

/-- The universal container inherits property `(T)` from its quotient map. -/
theorem kazhdan : HasKazhdanPropertyT.{0, 0} U.Container :=
  HasKazhdanPropertyT.of_surjective U.quotient U.quotient_surjective R.kazhdan

/-- The universal container has full corona MF radical. -/
theorem coronaMFResidual_eq_top : coronaMFResidual U.Container = ⊤ :=
  R.quotient_coronaMFResidual_eq_top U.quotient U.quotient_surjective

/-- The universal container has full literal CDE MF radical. -/
theorem cdeMFResidual_eq_top : cdeMFResidual U.Container = ⊤ := by
  rw [cdeMFResidual_eq_coronaMFResidual]
  exact U.coronaMFResidual_eq_top

/-- If the routed source is nonsofic, so is every such container. -/
theorem not_isSofic (hR : ¬ IsSofic R.Quotient) : ¬ IsSofic U.Container := by
  intro hU
  exact hR (isSofic_of_injective U.sourceEmbedding
    U.sourceEmbedding_injective hU)

/-- The requested group embeds in the universal container. -/
theorem requested_embeds : ∃ f : L →* U.Container, Function.Injective f :=
  ⟨U.requestedEmbedding, U.requestedEmbedding_injective⟩

/-- The verified SQ-universal-container package. -/
theorem consequence_package :
    IsTwoGenerated U.Container ∧
      HasKazhdanPropertyT.{0, 0} U.Container ∧
      cdeMFResidual U.Container = ⊤ :=
  ⟨U.twoGenerated, U.kazhdan, U.cdeMFResidual_eq_top⟩

end UniversalContainerData

/-! ## Universal finitely presented torsion-free Kazhdan groups -/

/-- Proof-carrying form of a universal finitely presented torsion-free
Kazhdan group.  Universality is stated only for the precise class used in the
manuscript. -/
structure UniversalFinitelyPresentedKazhdanData where
  Carrier : Type
  [groupCarrier : Group Carrier]
  [finitelyPresented : Group.IsFinitelyPresented Carrier]
  kazhdan : HasKazhdanPropertyT.{0, 0} Carrier
  torsionFree : IsPowerTorsionFree Carrier
  embedsFinitelyPresentedTorsionFree :
    ∀ (L : Type) [Group L] [Group.IsFinitelyPresented L],
      IsPowerTorsionFree L → ∃ f : L →* Carrier, Function.Injective f

namespace UniversalFinitelyPresentedKazhdanData

variable (U : UniversalFinitelyPresentedKazhdanData)

local instance universalKazhdanCarrierGroup : Group U.Carrier := U.groupCarrier
local instance universalKazhdanCarrierFinitelyPresented :
    Group.IsFinitelyPresented U.Carrier := U.finitelyPresented

/-- The routed quotient embeds by universality. -/
theorem source_embeds :
    ∃ f : R.Quotient →* U.Carrier, Function.Injective f := by
  letI : Group.IsFinitelyPresented R.Quotient := R.finitelyPresented
  exact U.embedsFinitelyPresentedTorsionFree R.Quotient R.torsionFree

/-- A universal group containing the routed non-MF group is itself non-MF. -/
theorem not_isOperatorMF (R : DefectRoutingData D) :
    ¬ IsOperatorMF U.Carrier := by
  obtain ⟨f, hf⟩ := U.source_embeds R
  intro hU
  exact R.not_isOperatorMF (hU.comap f hf)

/-- If the routed source is nonsofic, the universal group is nonsofic. -/
theorem not_isSofic (hR : ¬ IsSofic R.Quotient) : ¬ IsSofic U.Carrier := by
  obtain ⟨f, hf⟩ := U.source_embeds R
  intro hU
  exact hR (isSofic_of_injective f hf hU)

end UniversalFinitelyPresentedKazhdanData

end DefectRoutingData

end GroupApproximation
