import GroupApproximation.Sofic.Normalization
import GroupApproximation.Sofic.SoficErrors
import GroupApproximation.Sofic.SoficTransfer
import GroupApproximation.Matching.ExternalCompressorCrossing
import GroupApproximation.Matching.DecompositionRefinement
import GroupApproximation.Matching.ComponentDivergence
import GroupApproximation.Matching.RepairedComponentBisection

/-!
# Involutions in approximate centralizers act on expander components

Let an ambient sofic approximation be restricted to an embedded subgroup.
If an ambient involution centralizes that subgroup, finite normalization makes
its model permutation an exact involution.  Approximate multiplicativity then
makes it commute with the restricted subgroup away from a negligible set.
Consequently it has negligible crossing and leakage on every expander
decomposition of the restricted approximation, and its dominant-target map on
components is an involution away from negligible vertex mass.

Every input below is algebraic or part of the definitions already formalized
in this development.  In particular, there is no centralizer-normalization or
other external rigidity premise.
-/

namespace GroupApproximation

namespace SoficApproximation

variable {H Γ : Type} [Group H] [Group Γ]

/-- Normalizing at a nontrivial group involution assigns it an exact
involutive permutation on every finite model. -/
theorem normalize_involution_map_mul_self (A : SoficApproximation H)
    {k : H} (hk : k ≠ 1) (hsq : k * k = 1) (n : ℕ) :
    (A.normalize {k}).map n k * (A.normalize {k}).map n k = 1 := by
  rw [A.normalize_map, A.normalizedMap_of_involution {k} n hk (by simp) hsq]
  exact involutionNormalize_mul_self (A.map n k)

end SoficApproximation

namespace ExpanderDecomposition

variable {H Γ : Type} [Group H] [Group Γ]
variable (A : SoficApproximation H) (ι : Γ →* H)
  (hι : Function.Injective ι) (k : H)
variable {T : Finset Γ}

/-- The normalized model involution has negligible crossings of the edited
expander-component graph for the restricted `Γ`-approximation. -/
theorem normalizedCentralizer_crossing_negligible
    (hcomm : ∀ g : Γ, Commute k (ι g))
    (hsymm : ∀ g ∈ T, g⁻¹ ∈ T)
    (hgen : Subgroup.closure (T : Set Γ) = ⊤)
    (D : ExpanderDecomposition ((A.normalize {k}).comap ι hι) T) :
    Negligible
      (fun n ↦ (Fintype.card (((A.normalize {k}).comap ι hι).model n) : ℝ))
      fun n ↦ (((D.modelGraph n).crossingEdges
        (transportedTargetLabel (D.blocks n) ((A.normalize {k}).map n k))).card : ℝ) := by
  apply D.externalGlobalCrossing_negligible
    (fun n ↦ (A.normalize {k}).map n k) id
  · intro g _
    apply Negligible.congr
      ((A.normalize {k}).commutationError_negligible k (ι g) (hcomm g))
    intro n
    rfl
  · exact D.all_almost_invariant hsymm hgen

/-- The normalized centralizing involution loses negligible total vertex mass
when each expander component is sent to its dominant target component. -/
theorem normalizedCentralizer_leakage_negligible
    (hcomm : ∀ g : Γ, Commute k (ι g))
    (hsymm : ∀ g ∈ T, g⁻¹ ∈ T)
    (hgen : Subgroup.closure (T : Set Γ) = ⊤)
    (D : ExpanderDecomposition ((A.normalize {k}).comap ι hι) T) :
    Negligible
      (fun n ↦ (Fintype.card (((A.normalize {k}).comap ι hι).model n) : ℝ))
      fun n ↦ ∑ C : D.componentIndex n,
        (D.componentLeakage (D.blocks n) ((A.normalize {k}).map n k) C : ℝ) := by
  exact D.totalLeakage_negligible_of_crossing
    (fun n ↦ (A.normalize {k}).map n k)
    (normalizedCentralizer_crossing_negligible A ι hι k hcomm hsymm hgen D)

/-- The dominant-target map induced by the normalized centralizing involution
squares to the identity outside a collection of components of negligible
total vertex mass. -/
theorem normalizedCentralizer_nonreciprocalMass_negligible
    (hk : k ≠ 1) (hsq : k * k = 1)
    (hcomm : ∀ g : Γ, Commute k (ι g))
    (hsymm : ∀ g ∈ T, g⁻¹ ∈ T)
    (hgen : Subgroup.closure (T : Set Γ) = ⊤)
    (D : ExpanderDecomposition ((A.normalize {k}).comap ι hι) T) :
    Negligible
      (fun n ↦ (Fintype.card (((A.normalize {k}).comap ι hι).model n) : ℝ))
      fun n ↦ D.nonreciprocalMass ((A.normalize {k}).map n k) := by
  apply D.nonreciprocalMass_negligible_of_totalLeakage
    (fun n ↦ (A.normalize {k}).map n k)
  · exact fun n ↦ A.normalize_involution_map_mul_self hk hsq n
  · exact normalizedCentralizer_leakage_negligible
      A ι hι k hcomm hsymm hgen D

/-- The normalized centralizing involution acts by a genuine bisection of
the asymptotic component groupoid.  The object permutation is the exact
involutive repair of the dominant-target map; its arrows are restrictions of
the model involution on reciprocal components and identities on the
negligible exceptional component mass. -/
noncomputable def normalizedCentralizer_componentBisection
    (hk : k ≠ 1) (hsq : k * k = 1)
    (hcomm : ∀ g : Γ, Commute k (ι g))
    (hsymm : ∀ g ∈ T, g⁻¹ ∈ T)
    (hgen : Subgroup.closure (T : Set Γ) = ⊤)
    (D : ExpanderDecomposition ((A.normalize {k}).comap ι hι) T) :
    FiniteGroupoid.Bisection
      (asymptoticPartialGroupoidPresentation D.ComponentSequence
        (fun n ↦ (Fintype.card (((A.normalize {k}).comap ι hι).model n) : ℝ))
        (fun _ ↦ by positivity) D.componentSequenceModel).Obj :=
  D.repairedComponentBisection
    (fun n ↦ (A.normalize {k}).map n k)
    (fun n ↦ A.normalize_involution_map_mul_self hk hsq n)
    (normalizedCentralizer_leakage_negligible
      A ι hι k hcomm hsymm hgen D)

end ExpanderDecomposition
end GroupApproximation
