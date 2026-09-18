import GroupApproximation.Manuscript.NonMFSentences.ChainCoreOpeningSentence
import GroupApproximation.Dynamics.ItineraryCoreCycleCondition
import GroupApproximation.Dynamics.CoreSubshiftCycle
import GroupApproximation.Meta.AxiomGuard

/-!
# `sec:chain-core` opening and the itinerary intersection (tex 1341, 1439–1441)

`non_mf_groups_exist.tex`, tex 1341–1342:

"The torsion-defect argument can identify the whole MF radical even when the defect ideal is
proper."

`non_mf_groups_exist.tex`, proof of `lem:chain-core-models`, tex 1439–1441:

"The sets on its right decrease and satisfy the cycle condition; finite language stabilization
proves that their intersection does too."

Proof route.

* **tex 1341.** Reuse the closed `printedChainCoreOpening_closed`. Take any nonempty compact
  metrizable zero-dimensional `X` and homeomorphism `T`. Over every finite field the defect ideal
  equals the transient ideal and is proper, because `CR(T) ≠ ∅`. Over `F₂` the MF radicals of
  `GL_n(R_X)` for `n ≥ 3` and of `EL_n(R_X)` for `n ≥ 4` are the relative elementary groups over
  that proper ideal.
* **tex 1439–1441.** "Its right" is `⋂_{l ≥ m} ρ_lm(Y_l)`, where `Y_l = itineraryCore T (S l)`.
  - The sets decrease: `oneBlock_image_antitone`, with `ρ_lm(Y_l) ⊆ Y_m` from
    `oneBlock_image_itineraryCore_subset`.
  - Each set has the cycle condition. Every `Y_l` does, by `cycleCondition_coreSubshift`, and
    one-block images preserve it (`cycleCondition_oneBlock_image`).
  - The intersection equals `π_m(Y_*)` (`itinerary_image_generalCore`). Language stabilization
    gives it the cycle condition (`cycleCondition_iInter_oneBlock_image`).
-/

namespace GroupApproximation.Manuscript.NonMF.ChainA

open GroupApproximation.ChainCore GroupApproximation.WordGraph

/-- **tex 1341.** "The torsion-defect argument can identify the whole MF radical even when the
defect ideal is proper."

For every nonempty compact metrizable zero-dimensional `X` and homeomorphism `T`:
* over every finite field, the defect ideal is the transient ideal and is proper;
* over `F₂`, `Rad_MF(GL_n(R_X)) = EL_n(R_X, I)` for `n ≥ 3`;
* over `F₂`, `Rad_MF(EL_n(R_X)) = EL_n(R_X, I)` for `n ≥ 4`. -/
theorem manuscriptSentence_torsionDefectIdentifiesWholeMFRadical :
    GroupApproximation.ChainCore.DynamicRankBudget.PrintedChainCoreOpening :=
  GroupApproximation.ChainCore.DynamicRankBudget.printedChainCoreOpening_closed

#audit_axioms GroupApproximation.Manuscript.NonMF.ChainA.manuscriptSentence_torsionDefectIdentifiesWholeMFRadical

/-- **tex 1439–1441.** "The sets on its right decrease and satisfy the cycle condition; finite
language stabilization proves that their intersection does too."

Take a compact `X`, a homeomorphism `T`, and refining finite clopen partitions `S`. Then:
* the sets `ρ_lm(Y_l)` (for `l = m + k`) decrease;
* each set has the cycle condition;
* their intersection is `π_m(Y_*)`;
* the intersection has the cycle condition. -/
theorem manuscriptSentence_itineraryIntersectionCycleCondition {X : Type*} [TopologicalSpace X]
    [CompactSpace X] (T : X ≃ₜ X) (S : ℕ → DiscreteQuotient X) (hS : Antitone S) (m : ℕ) :
    (Antitone fun k : ℕ =>
        oneBlock (hS (Nat.le_add_right m k)) '' itineraryCore T (S (m + k))) ∧
      (∀ (l : ℕ) (h : m ≤ l), CycleCondition (oneBlock (hS h) '' itineraryCore T (S l))) ∧
      (itinerary T (S m) '' generalCore T S =
        ⋂ (l : ℕ) (h : m ≤ l), oneBlock (hS h) '' itineraryCore T (S l)) ∧
      CycleCondition (⋂ (l : ℕ) (h : m ≤ l), oneBlock (hS h) '' itineraryCore T (S l)) := by
  have hcore : ∀ l, CycleCondition (itineraryCore T (S l)) := fun l =>
    cycleCondition_coreSubshift (isClosed_itinerarySubshift T (S l))
      (mapsTo_shift_itinerarySubshift T (S l))
  refine ⟨oneBlock_image_antitone (Y := fun l => itineraryCore T (S l)) hS
      (fun h => oneBlock_image_itineraryCore_subset (T := T) (hS h)) m,
    fun l h => cycleCondition_oneBlock_image (hS h) (hcore l),
    itinerary_image_generalCore T hS m,
    cycleCondition_iInter_oneBlock_image (Y := fun l => itineraryCore T (S l)) hS
      (fun h => oneBlock_image_itineraryCore_subset (T := T) (hS h))
      (fun l => isClosed_itineraryCore T (S l)) hcore m⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.ChainA.manuscriptSentence_itineraryIntersectionCycleCondition

end GroupApproximation.Manuscript.NonMF.ChainA
