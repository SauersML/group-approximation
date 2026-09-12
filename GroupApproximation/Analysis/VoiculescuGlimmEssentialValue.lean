import GroupApproximation.Analysis.VoiculescuGlimmEssentialRange
import GroupApproximation.Analysis.VoiculescuGlimmSeparation

/-!
# (V2) The state's values lie in the joint essential numerical range

The separation says the state's tuple lies in the closed convex **hull** of the
vector-state tuples off each finite-dimensional subspace, one subspace at a
time.  This module removes the hull and the "one at a time" together: the tuple
lies in `essentialRange a`, so it is approximated by an honest vector state off
whichever subspace the consumer names.

## How the hull comes off

Suppose not.  `essentialRange a` is closed and — by the two-vector selection —
convex, so Hahn–Banach separates: a real functional `f` and a level `u` with
`f < u` on the range and `u < f p` at the state's tuple.  Now look at the
slices

    `closure (vectorStateTuples a V) ∩ {y | u ≤ f y}` .

They are compact (the tuples are bounded by the operator norms), closed, and
shrink as `V` grows, since a unit vector orthogonal to a larger subspace is
orthogonal to a smaller one.  Two cases, and both are contradictions.

*Every slice is nonempty.*  Cantor's intersection theorem for a directed family
of nonempty compact closed sets gives a point in all of them at once — a point
of `essentialRange a` with `u ≤ f`, which the separation forbids.

*Some slice is empty.*  Then `f < u` on `closure (vectorStateTuples a V)`, so
`f < u` on its convex hull because a half-space is convex, so `f ≤ u` on the
closed convex hull — which contains the state's tuple.  That contradicts
`u < f p`.

Nothing here normalises the length of a convex combination, so Carathéodory
never appears; the two-vector convexity of the range and `convexHull_min` have
already done that work.
-/

namespace GroupApproximation
namespace ShulmanFill

open scoped InnerProductSpace
open scoped ComplexOrder

noncomputable section

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- **The Cantor step.**  A closed set meeting every `closure (vectorStateTuples
a V)` meets the joint essential numerical range.  The family is directed because
enlarging `V` shrinks the tuples, and compact because the tuples are bounded by
the operator norms. -/
theorem exists_mem_essentialRange_inter {n : ℕ} (a : Fin n → (H →L[ℂ] H))
    {S : Set (Fin n → ℝ)} (hS : IsClosed S)
    (hne : ∀ V : Submodule ℂ H, FiniteDimensional ℂ V →
      (closure (vectorStateTuples a V) ∩ S).Nonempty) :
    (essentialRange a ∩ S).Nonempty := by
  haveI : Nonempty {V : Submodule ℂ H // FiniteDimensional ℂ V} :=
    ⟨⟨⊥, inferInstance⟩⟩
  obtain ⟨y, hy⟩ :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      (fun W : {V : Submodule ℂ H // FiniteDimensional ℂ V} ↦
        closure (vectorStateTuples a W.1) ∩ S)
      (by
        intro W₁ W₂
        haveI := W₁.2
        haveI := W₂.2
        refine ⟨⟨W₁.1 ⊔ W₂.1, inferInstance⟩, ?_, ?_⟩
        · exact Set.inter_subset_inter
            (closure_mono (vectorStateTuples_subset_of_le a le_sup_left))
            (subset_refl S)
        · exact Set.inter_subset_inter
            (closure_mono (vectorStateTuples_subset_of_le a le_sup_right))
            (subset_refl S))
      (fun W ↦ hne W.1 W.2)
      (fun W ↦ (isCompact_closure_vectorStateTuples a W.1).inter_right hS)
      (fun _ ↦ isClosed_closure.inter hS)
  refine ⟨y, (mem_essentialRange_iff a y).mpr fun V hV ↦ ?_, ?_⟩
  · exact (Set.mem_iInter.mp hy ⟨V, hV⟩).1
  · exact (Set.mem_iInter.mp hy ⟨⊥, inferInstance⟩).2

/-- **The hull comes off.**  A tuple lying in the closed convex hull of the
vector-state tuples off *every* finite-dimensional subspace lies in the joint
essential numerical range itself. -/
theorem mem_essentialRange_of_forall_mem_closure_convexHull {n : ℕ}
    (a : Fin n → (H →L[ℂ] H)) (hsa : ∀ i, IsSelfAdjoint (a i))
    (p : Fin n → ℝ)
    (hp : ∀ V : Submodule ℂ H, FiniteDimensional ℂ V →
      p ∈ closure (convexHull ℝ (vectorStateTuples a V))) :
    p ∈ essentialRange a := by
  by_contra hcon
  obtain ⟨f, u, hlt, hgt⟩ := geometric_hahn_banach_closed_point
    (convex_essentialRange a hsa) (isClosed_essentialRange a) hcon
  have hflin : IsLinearMap ℝ (f : (Fin n → ℝ) → ℝ) :=
    ⟨fun x y ↦ map_add f x y, fun c x ↦ map_smul f c x⟩
  by_cases hall : ∀ W : {V : Submodule ℂ H // FiniteDimensional ℂ V},
      (closure (vectorStateTuples a W.1) ∩ {y | u ≤ f y}).Nonempty
  · obtain ⟨y, hyE, hyu⟩ :=
      exists_mem_essentialRange_inter a (isClosed_le continuous_const f.continuous)
        (fun V hV ↦ hall ⟨V, hV⟩)
    exact absurd hyu (not_le.mpr (hlt y hyE))
  · rw [not_forall] at hall
    obtain ⟨W, hWempty⟩ := hall
    have hbelow : ∀ y ∈ closure (vectorStateTuples a W.1), f y < u := by
      intro y hy
      by_contra hle
      exact hWempty ⟨y, hy, not_lt.mp hle⟩
    have hstrict : convexHull ℝ (vectorStateTuples a W.1) ⊆ {y | f y < u} :=
      convexHull_min (fun w hw ↦ hbelow w (subset_closure hw))
        (convex_halfSpace_lt hflin u)
    have hweak : closure (convexHull ℝ (vectorStateTuples a W.1)) ⊆ {y | f y ≤ u} :=
      closure_minimal (fun y hy ↦ show f y ≤ u from le_of_lt (hstrict hy))
        (isClosed_le f.continuous continuous_const)
    exact absurd (hweak (hp W.1 W.2)) (not_le.mpr hgt)

/-- **Glimm's lemma for a self-adjoint family.**  A state of `B(H)` annihilating
the compacts has its values on a self-adjoint family reproduced, to any
tolerance, by a vector state at a unit vector orthogonal to any prescribed
finite-dimensional subspace. -/
theorem exists_unit_vector_of_state
    (ρ : (H →L[ℂ] H) →ₗ[ℂ] ℂ)
    (hpos : ∀ T : H →L[ℂ] H, 0 ≤ T → ∃ r : ℝ, 0 ≤ r ∧ ρ T = r)
    (hone : ρ 1 = 1) (hK : ∀ T : H →L[ℂ] H, IsCompactOperator T → ρ T = 0)
    {n : ℕ} (a : Fin n → (H →L[ℂ] H)) (hsa : ∀ i, IsSelfAdjoint (a i))
    (V : Submodule ℂ H) [FiniteDimensional ℂ V] {ε : ℝ} (hε : 0 < ε) :
    ∃ ξ : H, ξ ∈ Vᗮ ∧ ‖ξ‖ = 1 ∧
      ∀ i, |(⟪a i ξ, ξ⟫_ℂ).re - (ρ (a i)).re| < ε := by
  have hp : (fun i ↦ (ρ (a i)).re) ∈ essentialRange a := by
    refine mem_essentialRange_of_forall_mem_closure_convexHull a hsa _ ?_
    intro W hW
    haveI : FiniteDimensional ℂ W := hW
    exact mem_closure_convexHull_vectorStates ρ hpos hone hK W a hsa
  obtain ⟨x, hxmem, hx⟩ :=
    Metric.mem_closure_iff.mp ((mem_essentialRange_iff a _).mp hp V inferInstance) ε hε
  obtain ⟨ξ, hξV, hξnorm, hξval⟩ := (mem_vectorStateTuples_iff a V x).mp hxmem
  refine ⟨ξ, hξV, hξnorm, fun i ↦ ?_⟩
  have hd := (dist_pi_lt_iff hε).mp hx i
  rw [Real.dist_eq] at hd
  rw [← hξval i, abs_sub_comm]
  exact hd

end

end ShulmanFill
end GroupApproximation
