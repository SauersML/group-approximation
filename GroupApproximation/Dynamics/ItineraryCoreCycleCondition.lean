import GroupApproximation.Dynamics.OneBlockCycleCondition
import GroupApproximation.Meta.AxiomGuard

/-!
# The cycle condition passes to `π_m(Y_*)`

`non_mf_groups_exist.tex`, lines 1439–1441 (proof of `lem:chain-core-models`, general `X`):
"The sets on its right decrease and satisfy the cycle condition; finite language stabilization
proves that their intersection does too."

"Its right" is the right side of `π_m(Y_*) = ⋂_{l ≥ m} ρ_lm(Y_l)`.  Cyclic edges of length `r + 1`
depend only on the language of length `r + 1` (`isCyclicEdge_congr`).  For a decreasing sequence of
closed sets over a finite alphabet that language stabilizes to the language of the intersection
(chain-subshift's `exists_image_eq_image_iInter_of_antitone`), so the intersection inherits the
cycle condition (`cycleCondition_iInter_of_antitone`).  The sets `ρ_lm(Y_l)`, reindexed by
`l = m + k`, decrease and are closed; each has the cycle condition when `Y_l` does, by
`cycleCondition_oneBlock_image`.

* `wordEdge_congr`, `isCyclicEdge_congr`, `cycleCondition_iInter_of_antitone`;
* `oneBlock_image_antitone`, `isClosed_oneBlock_image`, `iInter_oneBlock_image_eq`;
* `cycleCondition_iInter_oneBlock_image`: `⋂_{l ≥ m} ρ_lm(Y_l)` has the cycle condition;
* `cycleCondition_itinerary_image_generalCore`: `π_m(Y_*)` has the cycle condition once every core
  `Y_l` does.
-/

namespace GroupApproximation
namespace ChainCore

open Set SymbolicDynamics.FullShift GroupApproximation.WordGraph

section Language

variable {A : Type*}

/-- Edges of the word graph of length `r` depend only on the language of length `r + 1`. -/
theorem wordEdge_congr {X X' : Set (ℤ → A)} {r : ℕ}
    (h : language X (r + 1) = language X' (r + 1)) : wordEdge X r = wordEdge X' r := by
  funext u v
  simp only [wordEdge, h]

/-- Cyclic edges of length `r + 1` depend only on the language of length `r + 1`. -/
theorem isCyclicEdge_congr {X X' : Set (ℤ → A)} {r : ℕ}
    (h : language X (r + 1) = language X' (r + 1)) (w : Fin (r + 1) → A) :
    IsCyclicEdge X r w ↔ IsCyclicEdge X' r w := by
  rw [IsCyclicEdge, IsCyclicEdge, wordEdge_congr h, h]

/-- **Finite language stabilization**: the intersection of a decreasing sequence of closed sets of
configurations over a finite alphabet, each with the cycle condition, has the cycle condition. -/
theorem cycleCondition_iInter_of_antitone [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    {Z : ℕ → Set (ℤ → A)} (hZ : Antitone Z) (hcl : ∀ k, IsClosed (Z k))
    (hcyc : ∀ k, CycleCondition (Z k)) : CycleCondition (⋂ k, Z k) := by
  intro r w hw
  obtain ⟨R, hR⟩ := exists_image_eq_image_iInter_of_antitone
    (f := fun x : ℤ → A ↦ word x 0 (r + 1)) (continuous_pi fun _ ↦ continuous_apply _) hZ hcl
  have hL : language (Z R) (r + 1) = language (⋂ k, Z k) (r + 1) := hR R le_rfl
  exact (isCyclicEdge_congr hL w).1 (hcyc R r w (by rw [hL]; exact hw))

end Language

section Itinerary

variable {X : Type*} [TopologicalSpace X] {S : ℕ → DiscreteQuotient X}

/-- The sets on the right decrease: `ρ_{l'm}(Y_{l'}) ⊆ ρ_lm(Y_l)` for `m ≤ l ≤ l'`, indexed by
`l = m + k`. -/
theorem oneBlock_image_antitone (hS : Antitone S) {Y : ∀ m, Set (ℤ → S m)}
    (hcompat : ∀ {l m : ℕ} (h : m ≤ l), oneBlock (hS h) '' Y l ⊆ Y m) (m : ℕ) :
    Antitone fun k ↦ oneBlock (hS (Nat.le_add_right m k)) '' Y (m + k) := by
  intro k k' hkk'
  rintro _ ⟨y, hy, rfl⟩
  have h : m + k ≤ m + k' := Nat.add_le_add_left hkk' m
  exact ⟨oneBlock (hS h) y, hcompat h ⟨y, hy, rfl⟩, oneBlock_oneBlock (hS h) _ y⟩

/-- Each `ρ_lm(Y_l)` is closed when `Y_l` is. -/
theorem isClosed_oneBlock_image [CompactSpace X] {S S' : DiscreteQuotient X} (h : S ≤ S')
    {Z : Set (ℤ → S)} (hZ : IsClosed Z) : IsClosed (oneBlock h '' Z) :=
  (hZ.isCompact.image (continuous_oneBlock h)).isClosed

/-- `⋂_{l ≥ m} ρ_lm(Y_l)`, reindexed by `l = m + k`. -/
theorem iInter_oneBlock_image_eq (hS : Antitone S) (Y : ∀ m, Set (ℤ → S m)) (m : ℕ) :
    ⋂ (l : ℕ) (h : m ≤ l), oneBlock (hS h) '' Y l =
      ⋂ k, oneBlock (hS (Nat.le_add_right m k)) '' Y (m + k) := by
  refine Subset.antisymm (subset_iInter fun k ↦ iInter₂_subset (m + k) (Nat.le_add_right m k)) ?_
  refine subset_iInter₂ fun l h ↦ ?_
  obtain ⟨k, rfl⟩ : ∃ k, l = m + k := ⟨l - m, by omega⟩
  exact iInter_subset _ k

/-- **The intersection satisfies the cycle condition** (`non_mf_groups_exist.tex`,
lines 1439–1441): for a closed family `Y_l` with `ρ_lm(Y_l) ⊆ Y_m`, each with the cycle condition,
`⋂_{l ≥ m} ρ_lm(Y_l)` has the cycle condition. -/
theorem cycleCondition_iInter_oneBlock_image [CompactSpace X] (hS : Antitone S)
    {Y : ∀ m, Set (ℤ → S m)} (hcompat : ∀ {l m : ℕ} (h : m ≤ l), oneBlock (hS h) '' Y l ⊆ Y m)
    (hcl : ∀ m, IsClosed (Y m)) (hcyc : ∀ m, CycleCondition (Y m)) (m : ℕ) :
    CycleCondition (⋂ (l : ℕ) (h : m ≤ l), oneBlock (hS h) '' Y l) := by
  rw [iInter_oneBlock_image_eq hS Y m]
  exact cycleCondition_iInter_of_antitone (oneBlock_image_antitone hS hcompat m)
    (fun k ↦ isClosed_oneBlock_image _ (hcl (m + k)))
    fun k ↦ cycleCondition_oneBlock_image _ (hcyc (m + k))

variable (T : X ≃ₜ X)

/-- `π_m(Y_*)` satisfies the cycle condition once every core `Y_l` does. -/
theorem cycleCondition_itinerary_image_generalCore [CompactSpace X] (hS : Antitone S)
    (hcore : ∀ l, CycleCondition (itineraryCore T (S l))) (m : ℕ) :
    CycleCondition (itinerary T (S m) '' generalCore T S) := by
  rw [itinerary_image_generalCore T hS m]
  exact cycleCondition_iInter_oneBlock_image hS
    (fun h ↦ oneBlock_image_itineraryCore_subset (T := T) (hS h))
    (fun l ↦ isClosed_itineraryCore T (S l)) hcore m

end Itinerary

end ChainCore
end GroupApproximation

#audit_axioms GroupApproximation.ChainCore.wordEdge_congr
#audit_axioms GroupApproximation.ChainCore.isCyclicEdge_congr
#audit_axioms GroupApproximation.ChainCore.cycleCondition_iInter_of_antitone
#audit_axioms GroupApproximation.ChainCore.oneBlock_image_antitone
#audit_axioms GroupApproximation.ChainCore.isClosed_oneBlock_image
#audit_axioms GroupApproximation.ChainCore.iInter_oneBlock_image_eq
#audit_axioms GroupApproximation.ChainCore.cycleCondition_iInter_oneBlock_image
#audit_axioms GroupApproximation.ChainCore.cycleCondition_itinerary_image_generalCore
