import GroupApproximation.Endpoint.MainResults
import GroupApproximation.Algebra.GroupTorsionFree
import GroupApproximation.Monsters.UniversalFinitelyPresentedGroup
import GroupApproximation.Sofic.ChosenNonMFTheorem
import GroupApproximation.Sofic.NormMFPrintedConsequences
import GroupApproximation.Sofic.OperatorMFPositiveControls

/-!
# An unconditional universal MF event horizon

This is the strongest subgroup-universal statement currently obtainable from
the repository's fully constructed, axiom-clean inputs.  The concrete
countable group `UniversalFinitelyPresentedGroup` contains every finitely
presented group.  In particular it contains the chosen finitely presented
non-MF group and hence a fixed nontrivial MF-invisible element.

Consequently every homomorphism from the universal group to every operator-MF
group kills that same nontrivial element.  Thus no such homomorphism is
injective, even though every finitely presented MF group (and every finite
group) occurs inside the source.

Unlike a full MF black hole, this theorem does not claim that every outgoing
homomorphism is trivial.  That stronger conclusion requires an unconditional
simple-envelope or full-radical construction, neither of which is presently
formalized in Mathlib or in this repository.
-/

namespace GroupApproximation.Monsters

open GroupApproximation
open ChosenMarkedPresentation ChosenNonMFTheorem

abbrev UniversalMFEventHorizon := UniversalFinitelyPresentedGroup

/-- A fixed embedding of the chosen finitely presented non-MF group into the
universal free product.  Choice only selects an embedding from the proved
existence theorem. -/
noncomputable def chosenNonMFEmbedding :
    MarkedGroup →* UniversalMFEventHorizon :=
  Classical.choose (embeds_universalFinitelyPresentedGroup MarkedGroup)

/-- The selected embedding is injective. -/
theorem chosenNonMFEmbedding_injective :
    Function.Injective chosenNonMFEmbedding :=
  Classical.choose_spec
    (embeds_universalFinitelyPresentedGroup MarkedGroup)

/-- The universal group's fixed MF-invisible element. -/
noncomputable def eventHorizonMark : UniversalMFEventHorizon :=
  chosenNonMFEmbedding mark

/-- The fixed event-horizon mark is nontrivial. -/
theorem eventHorizonMark_ne_one : eventHorizonMark ≠ 1 := by
  intro h
  apply ChosenMarkedPresentation.mark_ne_one
  apply chosenNonMFEmbedding_injective
  simpa [eventHorizonMark] using h

/-- The event-horizon mark still has order two after it is embedded in the
universal group.  This is the precise obstruction to obtaining a
torsion-free event horizon merely by restricting the carrier or by passing
to its universal torsion-free quotient. -/
theorem eventHorizonMark_sq : eventHorizonMark ^ 2 = 1 := by
  rw [eventHorizonMark, ← map_pow, ChosenMarkedPresentation.mark_sq, map_one]

/-- Every homomorphism from the event horizon to a torsion-free group kills
the event-horizon mark.  This statement uses only the proved order-two
relation; no MF input is involved. -/
theorem map_eventHorizonMark_eq_one_to_torsionFree
    {T : Type*} [Group T] (hT : IsPowerTorsionFree T)
    (f : UniversalMFEventHorizon →* T) :
    f eventHorizonMark = 1 := by
  apply hT (f eventHorizonMark) 2 (by decide)
  rw [← map_pow, eventHorizonMark_sq, map_one]

/-- In particular, the existing universal MF event horizon is not itself
torsion-free. -/
theorem universalMFEventHorizon_not_torsionFree :
    ¬ IsPowerTorsionFree UniversalMFEventHorizon := by
  intro htf
  exact eventHorizonMark_ne_one
    (map_eventHorizonMark_eq_one_to_torsionFree htf
      (MonoidHom.id UniversalMFEventHorizon))

/-- The fixed event-horizon mark is invisible in every operator-norm matrix
ultraproduct. -/
theorem eventHorizonMark_normMFInvisible :
    NormMFInvisible eventHorizonMark :=
  ChosenNonMFTheorem.mark_normMFInvisible.map chosenNonMFEmbedding

/-- Equivalently, the mark is killed by every representation into every
standard cofinite norm-matrix corona. -/
theorem eventHorizonMark_coronaMFInvisible :
    CoronaMFInvisible eventHorizonMark :=
  eventHorizonMark_normMFInvisible.toCoronaMFInvisible

/-- **Universal MF event horizon.**  Every homomorphism from the universal
group to any operator-MF group kills one fixed nonidentity element. -/
theorem map_eventHorizonMark_eq_one_to_isOperatorMF
    {M : Type*} [Group M] (hM : IsOperatorMF M)
    (f : UniversalMFEventHorizon →* M) :
    f eventHorizonMark = 1 := by
  obtain ⟨X, hX, j, hj⟩ := hM
  apply hj
  simpa using
    eventHorizonMark_coronaMFInvisible X hX (j.comp f)

/-- No homomorphism from the universal group to an operator-MF group can be
faithful. -/
theorem no_injective_map_to_isOperatorMF
    {M : Type*} [Group M] (hM : IsOperatorMF M)
    (f : UniversalMFEventHorizon →* M) :
    ¬ Function.Injective f :=
  not_injective_to_isOperatorMF eventHorizonMark_coronaMFInvisible
    eventHorizonMark_ne_one hM f

/-- The universal group itself is not operator-MF. -/
theorem universalMFEventHorizon_not_isOperatorMF :
    ¬ IsOperatorMF UniversalMFEventHorizon := by
  intro hMF
  exact no_injective_map_to_isOperatorMF hMF
    (MonoidHom.id UniversalMFEventHorizon) Function.injective_id

/-- Every map from the universal group to a finite group kills the same fixed
nontrivial element. -/
theorem map_eventHorizonMark_eq_one_to_finite
    (F : Type) [Group F] [Finite F]
    (f : UniversalMFEventHorizon →* F) :
    f eventHorizonMark = 1 :=
  map_eventHorizonMark_eq_one_to_isOperatorMF
    (isOperatorMF_of_finite_standard F) f

/-- Hence no homomorphism from the universal group to a finite group is
injective. -/
theorem no_injective_map_to_finite
    (F : Type) [Group F] [Finite F]
    (f : UniversalMFEventHorizon →* F) :
    ¬ Function.Injective f :=
  no_injective_map_to_isOperatorMF
    (isOperatorMF_of_finite_standard F) f

/-- The universal event horizon is nonsofic because it contains a finitely
presented nonsofic group. -/
theorem universalMFEventHorizon_not_isSofic :
    ¬ IsSofic UniversalMFEventHorizon := by
  obtain ⟨G, groupG, hfp, hns⟩ :=
    GroupApproximation.exists_finitelyPresented_nonsofic_group
  letI : Group G := groupG
  letI : Group.IsFinitelyPresented G := hfp
  obtain ⟨i, hi⟩ := embeds_universalFinitelyPresentedGroup G
  intro hU
  exact hns (isSofic_of_injective i hi hU)

/-- The full unconditional package: countability, infinitude, subgroup
universality, a fixed outgoing MF obstruction, and nonsoficity. -/
theorem universalMFEventHorizon_package :
    Countable UniversalMFEventHorizon ∧
      Infinite UniversalMFEventHorizon ∧
      (∀ (G : Type) [Group G] [Group.IsFinitelyPresented G],
        ∃ f : G →* UniversalMFEventHorizon, Function.Injective f) ∧
      eventHorizonMark ≠ 1 ∧
      (∀ (M : Type) [Group M], IsOperatorMF M →
        ∀ f : UniversalMFEventHorizon →* M,
          f eventHorizonMark = 1) ∧
      ¬ IsOperatorMF UniversalMFEventHorizon ∧
      ¬ IsSofic UniversalMFEventHorizon := by
  refine ⟨inferInstance, inferInstance, ?_, eventHorizonMark_ne_one,
    ?_, universalMFEventHorizon_not_isOperatorMF,
    universalMFEventHorizon_not_isSofic⟩
  · intro G _ _
    exact embeds_universalFinitelyPresentedGroup G
  · intro M _ hM f
    exact map_eventHorizonMark_eq_one_to_isOperatorMF hM f

/-- The finite-group paradox in its exact unconditional form: every finite
group enters, while every outgoing map to a finite group kills one fixed
nontrivial element and is therefore noninjective. -/
theorem every_finite_group_enters_no_faithful_finite_map_leaves :
    (∀ (F : Type) [Group F] [Finite F],
      ∃ f : F →* UniversalMFEventHorizon, Function.Injective f) ∧
    (∀ (F : Type) [Group F] [Finite F],
      ∀ f : UniversalMFEventHorizon →* F,
        f eventHorizonMark = 1 ∧ ¬ Function.Injective f) := by
  constructor
  · intro F _ _
    exact embeds_universalFinitelyPresentedGroup_of_finite F
  · intro F _ _ f
    exact ⟨map_eventHorizonMark_eq_one_to_finite F f,
      no_injective_map_to_finite F f⟩

end GroupApproximation.Monsters
