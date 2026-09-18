/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Bases
import GroupApproximation.PalomarBridges.XXII

/-!
# Problem XXII of Schafhauser, Tikuisis and White: solution

This module proves the two theorems of `Palomar/STWProblemXXIIChallenge.lean`. The shared block
below is a byte-identical copy of the Challenge's definitions.

The witness is the antipodal counterexample of the development. The base algebra `A` is
`GroupApproximation.STW22NegativeSolution.AntipodalCounterexampleAlgebra`, the completion `M` is
`GroupApproximation.STW22.AntipodalCompletionAlgebra`, and `X` is the set
`GroupApproximation.STW22.antipodalDesignatedTraces` of canonical extensions of the traces of `A`.
The development proves, with no hypotheses, that `(M, X)` is factorial tracially complete, that
`X` is exactly the set of `‖·‖_{2,X}`-continuous traces, and that neither form of the trace
problem holds (`GroupApproximation.STW22.antipodalFactorialNegativeSolutionToProblemXXII`).
`GroupApproximation.PalomarBridges.XXII` adds the three facts the presentation clause needs:
restriction is a bijection from `X` onto `T(A)`, `A` is `‖·‖_{2,X}`-dense in `M`, and `A` is
separable.

The Challenge's `TracialState` has the same four fields as the development's, so the section
`Bridges` identifies the two types by an equivalence `toDev`, which is a homeomorphism
`toDevHomeomorph` for the weak⋆ topologies, and transports every definition along it.

The prose of this module was written by Claude (Anthropic).
-/

namespace STWProblemXXII

noncomputable section

-- BEGIN SHARED BLOCK (kept byte-identical in `Palomar/STWProblemXXIIChallenge.lean` and `Palomar/STWProblemXXIISolution.lean`)

open Filter
open scoped ComplexOrder

/-- A tracial state on a unital C⋆-algebra: a linear functional that is unital, nonnegative on
every `x⋆ x`, and invariant under swapping the factors of a product. -/
structure TracialState (A : Type*) [CStarAlgebra A] where
  toLinearMap : A →ₗ[ℂ] ℂ
  map_one : toLinearMap 1 = 1
  map_star_mul_self_nonneg : ∀ x : A, 0 ≤ toLinearMap (star x * x)
  map_mul_comm : ∀ x y : A, toLinearMap (x * y) = toLinearMap (y * x)

/-- The weak⋆ topology on tracial states: the coarsest topology making every evaluation
`τ ↦ τ(a)` continuous. -/
instance tracialStateTopology {A : Type*} [CStarAlgebra A] : TopologicalSpace (TracialState A) :=
  TopologicalSpace.induced (fun (τ : TracialState A) (a : A) ↦ τ.toLinearMap a) inferInstance

/-- The uniform two-norm `‖a‖_{2,X} = sup_{τ ∈ X} τ(a⋆ a)^{1/2}` (CCEGSTW Definition 3.1). -/
def uniformTwoNorm {A : Type*} [CStarAlgebra A] (X : Set (TracialState A)) (a : A) : ℝ :=
  sSup ((fun τ : TracialState A ↦ Real.sqrt (τ.toLinearMap (star a * a)).re) '' X)

/-- `X` is faithful: `a = 0` whenever `τ(a⋆ a) = 0` for every `τ ∈ X`, so `‖·‖_{2,X}` is a norm. -/
def IsFaithfulTraceSet {A : Type*} [CStarAlgebra A] (X : Set (TracialState A)) : Prop :=
  ∀ a : A, (∀ τ ∈ X, τ.toLinearMap (star a * a) = 0) → a = 0

/-- The unit ball is `‖·‖_{2,X}`-complete: every `‖·‖_{2,X}`-Cauchy sequence of norm at most `1`
has a `‖·‖_{2,X}`-limit of norm at most `1`. -/
def UnitBallUniformTwoComplete {A : Type*} [CStarAlgebra A] (X : Set (TracialState A)) : Prop :=
  ∀ x : ℕ → A, (∀ k, ‖x k‖ ≤ 1) →
    (∀ ε > 0, ∃ K : ℕ, ∀ k ≥ K, ∀ l ≥ K, uniformTwoNorm X (x k - x l) < ε) →
      ∃ a : A, ‖a‖ ≤ 1 ∧ Tendsto (fun k ↦ uniformTwoNorm X (x k - a)) atTop (nhds 0)

/-- `X` is convex: a tracial state that is a convex combination of two members of `X` lies in
`X`. -/
def IsConvexTraceSet {A : Type*} [CStarAlgebra A] (X : Set (TracialState A)) : Prop :=
  ∀ σ ∈ X, ∀ τ ∈ X, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ ρ : TracialState A,
    (∀ a : A, ρ.toLinearMap a =
      (t : ℂ) * σ.toLinearMap a + ((1 - t : ℝ) : ℂ) * τ.toLinearMap a) → ρ ∈ X

/-- `X` is a face of `T(A)`: it is convex, and whenever a proper convex combination of two tracial
states lies in `X`, both of them lie in `X`. -/
def IsFaceTraceSet {A : Type*} [CStarAlgebra A] (X : Set (TracialState A)) : Prop :=
  IsConvexTraceSet X ∧ ∀ σ τ : TracialState A, ∀ t : ℝ, 0 < t → t < 1 → ∀ ρ : TracialState A,
    (∀ a : A, ρ.toLinearMap a =
      (t : ℂ) * σ.toLinearMap a + ((1 - t : ℝ) : ℂ) * τ.toLinearMap a) →
      ρ ∈ X → σ ∈ X ∧ τ ∈ X

/-- **CCEGSTW Definition 3.4.** `(A, X)` is a tracially complete C⋆-algebra: `X` is a non-empty
compact convex set of tracial states, `‖·‖_{2,X}` is a norm, and the unit ball of `A` is
`‖·‖_{2,X}`-complete. -/
structure IsTraciallyComplete {A : Type*} [CStarAlgebra A] (X : Set (TracialState A)) : Prop where
  nonempty : X.Nonempty
  isCompact : IsCompact X
  isConvex : IsConvexTraceSet X
  faithful : IsFaithfulTraceSet X
  unitBallComplete : UnitBallUniformTwoComplete X

/-- **CCEGSTW Definition 3.13.** A tracially complete C⋆-algebra `(A, X)` is factorial: `X` is a
closed face of `T(A)`. -/
structure IsFactorialTraciallyComplete {A : Type*} [CStarAlgebra A]
    (X : Set (TracialState A)) : Prop where
  isTraciallyComplete : IsTraciallyComplete X
  isClosed : IsClosed X
  isFace : IsFaceTraceSet X

/-- A tracial state `σ` is `‖·‖_{2,X}`-continuous: `σ(xₖ) → 0` whenever `‖xₖ‖_{2,X} → 0`. -/
def IsUniformTwoContinuous {A : Type*} [CStarAlgebra A] (X : Set (TracialState A))
    (σ : TracialState A) : Prop :=
  ∀ x : ℕ → A, Tendsto (fun k ↦ uniformTwoNorm X (x k)) atTop (nhds 0) →
    Tendsto (fun k ↦ σ.toLinearMap (x k)) atTop (nhds 0)

/-- `α : A → M` presents `(M, X)` as the uniform tracial completion `(Ā^{T(A)}, T(A)~)` of `A`
(CCEGSTW Definition 3.19, Corollary 3.29(i)): `(M, X)` is tracially complete, every tracial state
of `A` is `σ ∘ α` for exactly one `σ ∈ X`, and `α(A)` is `‖·‖_{2,X}`-dense in `M`. -/
structure IsUniformTracialCompletion {A M : Type*} [CStarAlgebra A] [CStarAlgebra M]
    (α : A →⋆ₐ[ℂ] M) (X : Set (TracialState M)) : Prop where
  isTraciallyComplete : IsTraciallyComplete X
  existsUnique_restrict : ∀ τ : TracialState A,
    ∃! σ : TracialState M, σ ∈ X ∧ ∀ a : A, σ.toLinearMap (α a) = τ.toLinearMap a
  dense : ∀ m : M, ∃ x : ℕ → A,
    Tendsto (fun k ↦ uniformTwoNorm X (m - α (x k))) atTop (nhds 0)

-- END SHARED BLOCK

section Bridges

variable {A : Type*} [CStarAlgebra A]

/-- The Challenge's tracial states are the development's: both are structures with the same four
fields. -/
def toDev : TracialState A ≃ GroupApproximation.TracialState A where
  toFun τ := ⟨τ.toLinearMap, τ.map_one, τ.map_star_mul_self_nonneg, τ.map_mul_comm⟩
  invFun σ := ⟨σ.toLinearMap, σ.map_one, σ.map_star_mul_self_nonneg, σ.map_mul_comm⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `toDev` is a homeomorphism: both weak⋆ topologies are induced by evaluation. -/
def toDevHomeomorph : TracialState A ≃ₜ GroupApproximation.TracialState A where
  toEquiv := toDev
  continuous_toFun := continuous_induced_rng.2 continuous_induced_dom
  continuous_invFun := continuous_induced_rng.2 continuous_induced_dom

theorem uniformTwoNorm_preimage (S : Set (GroupApproximation.TracialState A)) :
    uniformTwoNorm (toDev ⁻¹' S) = GroupApproximation.TraciallyComplete.uniformTwoNormOn S := by
  funext a
  change sSup (((fun σ : GroupApproximation.TracialState A ↦
      GroupApproximation.UniformTracialGNSTwoGauge.tracialTwoNorm σ a) ∘ toDev) '' (toDev ⁻¹' S)) =
    sSup ((fun σ : GroupApproximation.TracialState A ↦
      GroupApproximation.UniformTracialGNSTwoGauge.tracialTwoNorm σ a) '' S)
  rw [Set.image_comp, toDev.surjective.image_preimage S]

variable {S : Set (GroupApproximation.TracialState A)}

theorem isFaithfulTraceSet_of (h : GroupApproximation.TraciallyComplete.IsFaithfulTraceSet S) :
    IsFaithfulTraceSet (toDev ⁻¹' S) :=
  fun a ha ↦ h a fun σ hσ ↦
    ha (toDev.symm σ) (by rw [Set.mem_preimage, Equiv.apply_symm_apply]; exact hσ)

theorem isConvexTraceSet_of (h : GroupApproximation.TraciallyComplete.IsConvexTraceSet S) :
    IsConvexTraceSet (toDev ⁻¹' S) := by
  intro σ hσ τ hτ t ht0 ht1 ρ hρ
  have e : toDev ρ =
      GroupApproximation.TraciallyComplete.convexComb t ht0 ht1 (toDev σ) (toDev τ) :=
    GroupApproximation.TraciallyComplete.tracialState_ext fun a ↦ by
      rw [GroupApproximation.TraciallyComplete.convexComb_apply]
      exact hρ a
  show toDev ρ ∈ S
  rw [e]
  exact h _ hσ _ hτ t ht0 ht1

theorem isFaceTraceSet_of (h : GroupApproximation.TraciallyComplete.IsFaceTraceSet S) :
    IsFaceTraceSet (toDev ⁻¹' S) := by
  refine ⟨isConvexTraceSet_of h.isConvex, fun σ τ t ht0 ht1 ρ hρ hmem ↦ ?_⟩
  have e : toDev ρ =
      GroupApproximation.TraciallyComplete.convexComb t ht0.le ht1.le (toDev σ) (toDev τ) :=
    GroupApproximation.TraciallyComplete.tracialState_ext fun a ↦ by
      rw [GroupApproximation.TraciallyComplete.convexComb_apply]
      exact hρ a
  have hmem' :
      GroupApproximation.TraciallyComplete.convexComb t ht0.le ht1.le (toDev σ) (toDev τ) ∈ S := by
    rw [← e]
    exact hmem
  exact h.mem_of_convexComb_mem (toDev σ) (toDev τ) t ht0 ht1 hmem'

theorem unitBallUniformTwoComplete_of
    (h : GroupApproximation.TraciallyComplete.UnitBallUniformTwoComplete S) :
    UnitBallUniformTwoComplete (toDev ⁻¹' S) := by
  intro x hx hc
  rw [uniformTwoNorm_preimage] at hc ⊢
  exact h x hx hc

theorem isUniformTwoContinuous_iff (σ : TracialState A) :
    IsUniformTwoContinuous (toDev ⁻¹' S) σ ↔
      GroupApproximation.TraciallyComplete.IsUniformTwoContinuousOn S (toDev σ) := by
  unfold IsUniformTwoContinuous
  rw [uniformTwoNorm_preimage]
  exact Iff.rfl

theorem isTraciallyComplete_of
    (h : GroupApproximation.TraciallyComplete.IsTraciallyCompletePair S) :
    IsTraciallyComplete (toDev ⁻¹' S) where
  nonempty := by
    obtain ⟨σ, hσ⟩ := h.nonempty
    exact ⟨toDev.symm σ, by rw [Set.mem_preimage, Equiv.apply_symm_apply]; exact hσ⟩
  isCompact := toDevHomeomorph.isCompact_preimage.2 h.isCompact
  isConvex := isConvexTraceSet_of h.isConvex
  faithful := isFaithfulTraceSet_of h.faithful
  unitBallComplete := unitBallUniformTwoComplete_of h.unitBallComplete

theorem isFactorialTraciallyComplete_of
    (h : GroupApproximation.TraciallyComplete.IsFactorialTraciallyCompletePair S) :
    IsFactorialTraciallyComplete (toDev ⁻¹' S) where
  isTraciallyComplete := isTraciallyComplete_of h.toIsTraciallyCompletePair
  isClosed := toDevHomeomorph.isClosed_preimage.2 h.isClosed
  isFace := isFaceTraceSet_of h.isFace

theorem mem_iff_of
    (h : ∀ σ : GroupApproximation.TracialState A,
      σ ∈ S ↔ GroupApproximation.TraciallyComplete.IsUniformTwoContinuousOn S σ)
    (σ : TracialState A) : σ ∈ toDev ⁻¹' S ↔ IsUniformTwoContinuous (toDev ⁻¹' S) σ :=
  (h (toDev σ)).trans (isUniformTwoContinuous_iff (S := S) σ).symm

theorem exists_not_isUniformTwoContinuous_of
    (h : ¬ GroupApproximation.TraciallyComplete.AllTracesUniformTwoContinuous S) :
    ∃ σ : TracialState A, ¬ IsUniformTwoContinuous (toDev ⁻¹' S) σ := by
  by_contra hc
  apply h
  intro σ
  have hσ : IsUniformTwoContinuous (toDev ⁻¹' S) (toDev.symm σ) := by
    by_contra hn
    exact hc ⟨_, hn⟩
  have h' := (isUniformTwoContinuous_iff (S := S) (toDev.symm σ)).1 hσ
  rwa [Equiv.apply_symm_apply] at h'

theorem preimage_ne_univ_of
    (h : ¬ GroupApproximation.TraciallyComplete.DesignatedTracesAreAllTraces S) :
    toDev ⁻¹' S ≠ Set.univ := by
  intro hc
  apply h
  show S = Set.univ
  rw [Set.eq_univ_iff_forall]
  intro σ
  have hσ : toDev.symm σ ∈ toDev ⁻¹' S := by
    rw [hc]
    exact Set.mem_univ _
  rwa [Set.mem_preimage, Equiv.apply_symm_apply] at hσ

theorem existsUnique_restrict_of {B : Type*} [CStarAlgebra B] {α : B →⋆ₐ[ℂ] A}
    (h : ∀ τ : GroupApproximation.TracialState B, ∃! σ : GroupApproximation.TracialState A,
      σ ∈ S ∧ ∀ b : B, σ (α b) = τ b)
    (τ : TracialState B) :
    ∃! σ : TracialState A, σ ∈ toDev ⁻¹' S ∧ ∀ b : B, σ.toLinearMap (α b) = τ.toLinearMap b := by
  obtain ⟨σ, hσ, huniq⟩ := h (toDev τ)
  refine ⟨toDev.symm σ, ⟨by rw [Set.mem_preimage, Equiv.apply_symm_apply]; exact hσ.1, hσ.2⟩, ?_⟩
  rintro ρ ⟨hρS, hρ⟩
  rw [Equiv.eq_symm_apply]
  exact huniq (toDev ρ) ⟨hρS, hρ⟩

theorem dense_of {B : Type*} [CStarAlgebra B] {α : B →⋆ₐ[ℂ] A}
    (h : ∀ m : A, ∃ x : ℕ → B, Tendsto (fun k ↦
      GroupApproximation.TraciallyComplete.uniformTwoNormOn S (m - α (x k))) atTop (nhds 0))
    (m : A) :
    ∃ x : ℕ → B, Tendsto (fun k ↦ uniformTwoNorm (toDev ⁻¹' S) (m - α (x k))) atTop (nhds 0) := by
  rw [uniformTwoNorm_preimage]
  exact h m

end Bridges

/-- **Problem XXII has a negative answer.** There are a separable unital C⋆-algebra `A`, with
`T(A)` non-empty and compact, and a presentation `α : A → M` of its uniform tracial completion
`(M, X) = (Ā^{T(A)}, T(A)~)`, such that the `‖·‖_{2,X}`-continuous traces on `M` are exactly the
members of `X`, some trace on `M` is not `‖·‖_{2,X}`-continuous, and `X ≠ T(M)`. -/
theorem exists_uniformTracialCompletion_with_discontinuous_trace :
    ∃ (A : Type) (_ : CStarAlgebra A) (M : Type) (_ : CStarAlgebra M) (α : A →⋆ₐ[ℂ] M)
      (X : Set (TracialState M)),
      TopologicalSpace.SeparableSpace A ∧
      (Set.univ : Set (TracialState A)).Nonempty ∧ IsCompact (Set.univ : Set (TracialState A)) ∧
      IsUniformTracialCompletion α X ∧
      (∀ σ : TracialState M, σ ∈ X ↔ IsUniformTwoContinuous X σ) ∧
      (∃ σ : TracialState M, ¬ IsUniformTwoContinuous X σ) ∧ X ≠ Set.univ := by
  obtain ⟨hfac, hmem, hcont, hall⟩ :=
    GroupApproximation.STW22.antipodalFactorialNegativeSolutionToProblemXXII
  refine ⟨GroupApproximation.STW22NegativeSolution.AntipodalCounterexampleAlgebra, inferInstance,
    GroupApproximation.STW22.AntipodalCompletionAlgebra, inferInstance,
    GroupApproximation.PalomarBridges.XXII.antipodalBaseToCompletion,
    toDev ⁻¹' GroupApproximation.STW22.antipodalDesignatedTraces,
    GroupApproximation.PalomarBridges.XXII.antipodal_separableSpace, ?_, ?_, ?_, mem_iff_of hmem,
    exists_not_isUniformTwoContinuous_of hcont, preimage_ne_univ_of hall⟩
  · obtain ⟨_, τ, -⟩ := GroupApproximation.STW22.antipodalDesignatedTraces_nonempty
    exact ⟨toDev.symm τ, Set.mem_univ _⟩
  · have hc := (toDevHomeomorph
      (A := GroupApproximation.STW22NegativeSolution.AntipodalCounterexampleAlgebra)).isCompact_preimage.2
      (@isCompact_univ _ _ (GroupApproximation.TraciallyComplete.compactSpace_tracialState
        GroupApproximation.STW22NegativeSolution.AntipodalCounterexampleAlgebra))
    rwa [Set.preimage_univ] at hc
  · exact ⟨isTraciallyComplete_of hfac.toIsTraciallyCompletePair,
      existsUnique_restrict_of GroupApproximation.PalomarBridges.XXII.antipodal_existsUnique_restrict,
      dense_of GroupApproximation.PalomarBridges.XXII.antipodal_dense⟩

/-- **The trace problem fails for factorial tracially complete C⋆-algebras.** Some factorial
tracially complete C⋆-algebra `(M, X)` has a trace that is not `‖·‖_{2,X}`-continuous, and
`X ≠ T(M)`; its `‖·‖_{2,X}`-continuous traces are exactly the members of `X`. -/
theorem exists_factorial_traciallyComplete_with_discontinuous_trace :
    ∃ (M : Type) (_ : CStarAlgebra M) (X : Set (TracialState M)),
      IsFactorialTraciallyComplete X ∧
      (∀ σ : TracialState M, σ ∈ X ↔ IsUniformTwoContinuous X σ) ∧
      (∃ σ : TracialState M, ¬ IsUniformTwoContinuous X σ) ∧ X ≠ Set.univ := by
  obtain ⟨hfac, hmem, hcont, hall⟩ :=
    GroupApproximation.STW22.antipodalFactorialNegativeSolutionToProblemXXII
  exact ⟨GroupApproximation.STW22.AntipodalCompletionAlgebra, inferInstance,
    toDev ⁻¹' GroupApproximation.STW22.antipodalDesignatedTraces,
    isFactorialTraciallyComplete_of hfac, mem_iff_of hmem,
    exists_not_isUniformTwoContinuous_of hcont, preimage_ne_univ_of hall⟩

end

end STWProblemXXII
