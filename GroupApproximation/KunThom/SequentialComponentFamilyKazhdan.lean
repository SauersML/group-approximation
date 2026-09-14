import GroupApproximation.KunThom.SequentialComponentFamilyBlocks
import GroupApproximation.Kun.KunFixedDecomposition
import GroupApproximation.Sofic.SoficTransfer

/-!
# Decompositions and parameters from property (T)

Blueprint step 1 of Kun–Thom Theorem 4.1, in the sequential setting.  For a
countable group `G` with an infinite subgroup `Γ`, both with property (T), and
a sofic approximation `A` of `G`:

* `exists_sequentialDecompositions`: finite symmetric generating sets of `Γ`
  and of `G` carry expander decompositions of `A.restrict Γ` and of `A`, and
  `Γ` has a surjective enumeration.  Feeding the first decomposition and the
  enumeration to `componentFamily` gives the input of the uniform improvement.
* `exists_kazhdanPair_on_generators`: a finite symmetric generating set is a
  Kazhdan set with constant at most one, which is the Kazhdan input of
  `CentralizerNormalizationImprove.ComponentFamily.exists_joint_improvement`
  with `Q = T`.
-/

namespace GroupApproximation
namespace SequentialComponentFamily

/-- **Expander decompositions from property (T).** -/
theorem exists_sequentialDecompositions {G : Type} [Group G] [Countable G]
    {Γ : Subgroup G} [Infinite ↥Γ] (hTG : HasKazhdanPropertyT.{0, 0} G)
    (hTΓ : HasKazhdanPropertyT.{0, 0} ↥Γ) (A : SoficApproximation G)
    (SΓ : Finset ↥Γ) (honeΓ : 1 ∈ SΓ) (hsymmΓ : ∀ g ∈ SΓ, g⁻¹ ∈ SΓ)
    (hgenΓ : Subgroup.closure (SΓ : Set ↥Γ) = ⊤)
    (SG : Finset G) (honeG : 1 ∈ SG) (hsymmG : ∀ g ∈ SG, g⁻¹ ∈ SG)
    (hgenG : Subgroup.closure (SG : Set G) = ⊤) :
    Nonempty (ExpanderDecomposition (A.restrict Γ) SΓ) ∧
      Nonempty (ExpanderDecomposition A SG) ∧
        ∃ enum : ℕ → ↥Γ, Function.Surjective enum := by
  haveI : Infinite G := Infinite.of_injective Γ.subtype Γ.subtype_injective
  exact ⟨KunFixedDecomposition.expanderDecomposition hTΓ SΓ honeΓ hsymmΓ hgenΓ (A.restrict Γ),
    KunFixedDecomposition.expanderDecomposition hTG SG honeG hsymmG hgenG A,
    exists_surjective_nat ↥Γ⟩

/-- **A Kazhdan pair on a generating set.** -/
theorem exists_kazhdanPair_on_generators {K : Type} [Group K]
    (hT : HasKazhdanPropertyT.{0, 0} K) (S : Finset K) (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set K) = ⊤) :
    ∃ κ : ℝ, IsKazhdanPair.{0, 0} K S κ ∧ κ ≤ 1 := by
  obtain ⟨δ, hδ⟩ := KazhdanGenerators.exists_pair_on_generators hT S hsymm hgen
  exact ⟨min δ 1, hδ.shrink (lt_min hδ.1 zero_lt_one) (min_le_left _ _), min_le_right _ _⟩

end SequentialComponentFamily
end GroupApproximation
