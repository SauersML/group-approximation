import Mathlib.Algebra.Group.Commute.Hom
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.GroupTheory.Commutator.Basic

/-!
# The involutive collapse data at an arbitrary universe

`non_mf_groups_exist.tex`, `thm:collapse` (and the witness pattern displayed
just before it) quantifies over **all** countable groups.  The formalization in
`GroupApproximation.Sofic.InvolutionCollapseEndpoint` fixes the ambient group at
`Type 0` — its `InvolutiveDischarge` section opens with `variable {E : Type}` —
so the witness predicate, the collapse set and the collapse defect are all
available only for groups in the smallest universe.  That is a strictly weaker
*scope* than the manuscript's, and it is the reason `thm:collapse` does not
compose at face value with the neighbouring `Type u` wrappers such as
`manuscriptRadicalReductionToQuotient`.

This module restates exactly those three definitions with the ambient group in
`Type u`, verbatim in their bodies, and records how they transport along a group
isomorphism.  Nothing here is analytic: the whole file is elementary group
theory, and the accompanying module
`GroupApproximation.Sofic.CollapseUniverseScope` proves that at `Type 0` these
definitions are *definitionally* the ones in `InvolutionCollapseEndpoint`.
-/

namespace GroupApproximation
namespace CollapseUniverseScope

open scoped commutatorElement

universe u v

/-! ## The universe-polymorphic collapse data -/

section Data

variable {E : Type u} [Group E]

/-- An involutive torsion compression witness, over an ambient group in an
arbitrary universe: an involution centralized by the `s`-compressed copy of `L`
whose `L`-conjugation orbit commutes pairwise.  The body is verbatim
`InvolutionCollapseEndpoint.IsInvolutiveCompressionWitness`, which is stated
only for `E : Type`. -/
def IsInvolutiveCompressionWitness (L : Subgroup E) (s : E) (k : E) : Prop :=
  k * k = 1 ∧ (∀ γ ∈ L, Commute (s * γ * s⁻¹) k) ∧
    (∀ γ₁ ∈ L, ∀ γ₂ ∈ L, Commute (γ₁ * k * γ₁⁻¹) (γ₂ * k * γ₂⁻¹))

/-- The marked collapse commutators of all involutive witnesses, over an ambient
group in an arbitrary universe. -/
def involutiveCollapseSet (L : Subgroup E) (s : E) : Set E :=
  {x | ∃ k : E, IsInvolutiveCompressionWitness L s k ∧
    ∃ γ ∈ L, x = ⁅γ, k⁆}

/-- The intrinsic involutive compression-collapse defect subgroup, over an
ambient group in an arbitrary universe. -/
def involutiveCollapseDefect (L : Subgroup E) (s : E) : Subgroup E :=
  Subgroup.normalClosure (involutiveCollapseSet L s)

instance involutiveCollapseDefect_normal (L : Subgroup E) (s : E) :
    (involutiveCollapseDefect L s).Normal :=
  Subgroup.normalClosure_normal

/-- Membership in the collapse defect for a displayed collapse commutator. -/
theorem commutator_mem_involutiveCollapseDefect {L : Subgroup E} {s k : E}
    (hk : IsInvolutiveCompressionWitness L s k) {γ : E} (hγ : γ ∈ L) :
    ⁅γ, k⁆ ∈ involutiveCollapseDefect L s :=
  Subgroup.subset_normalClosure ⟨k, hk, γ, hγ, rfl⟩

end Data

/-! ## Transport along a group isomorphism

The collapse data is defined by group-theoretic equations alone, so it is
carried by any isomorphism — in particular by an isomorphism that *changes the
universe of the ambient group*, which is what the descent in
`GroupApproximation.Sofic.CollapseUniverseScope` needs. -/

section Transport

variable {A : Type u} {B : Type v} [Group A] [Group B]

/-- **The involutive witness predicate transports along a group isomorphism.**
An isomorphism `e : A ≃* B` carries a witness for `(L, s, k)` to a witness for
`(e L, e s, e k)`; the three defining equations are images of the originals. -/
theorem IsInvolutiveCompressionWitness.map {L : Subgroup A} {s k : A}
    (h : IsInvolutiveCompressionWitness L s k) (e : A ≃* B) :
    IsInvolutiveCompressionWitness (L.map (e : A →* B)) (e s) (e k) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [← map_mul, h1, map_one]
  · rintro _ ⟨g, hg, rfl⟩
    have hc : Commute (e (s * g * s⁻¹)) (e k) := (h2 g hg).map e
    have hrw : e (s * g * s⁻¹) = e s * e g * (e s)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    rw [hrw] at hc
    exact hc
  · rintro _ ⟨g₁, hg₁, rfl⟩ _ ⟨g₂, hg₂, rfl⟩
    have hc : Commute (e (g₁ * k * g₁⁻¹)) (e (g₂ * k * g₂⁻¹)) :=
      (h3 g₁ hg₁ g₂ hg₂).map e
    have hrw₁ : e (g₁ * k * g₁⁻¹) = e g₁ * e k * (e g₁)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    have hrw₂ : e (g₂ * k * g₂⁻¹) = e g₂ * e k * (e g₂)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    rw [hrw₁, hrw₂] at hc
    exact hc

/-- **The one-sided compression hypothesis transports along a group
isomorphism.** -/
theorem compresses_map {L : Subgroup A} {s : A}
    (hcomp : ∀ γ ∈ L, s * γ * s⁻¹ ∈ L) (e : A ≃* B) :
    ∀ γ ∈ L.map (e : A →* B),
      e s * γ * (e s)⁻¹ ∈ L.map (e : A →* B) := by
  rintro _ ⟨g, hg, rfl⟩
  refine ⟨s * g * s⁻¹, hcomp g hg, ?_⟩
  simp only [MonoidHom.coe_coe, map_mul, map_inv]

end Transport

end CollapseUniverseScope
end GroupApproximation
