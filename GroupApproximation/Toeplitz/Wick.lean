/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GroupApproximation.Toeplitz.FockModule

/-!
# Sums of products of two creation operators

Let `M` be a submodule of sections of the Fock space that is invariant under the creation operators
of a set `E` of sections and under the annihilation operators of the sections that are continuous
against `E` (`IsFockInvariant`).  For finitely many admissible sections `u k`, `v k`, the operator
`creationPairs u v = ∑_k ℓ(u k) ℓ(v k)` has the adjoint `annihilationPairs u v = ∑_k ℓ(v k)* ℓ(u k)*`
(`isSectionAdjoint_creationPairs`), and

`annihilationPairs u' v' * creationPairs u v = (∑_{i,j} ⟪u' i, u j⟫ ⟪v' i, v j⟫) • 1`

at every point (`annihilationPairs_mul_creationPairs_apply`).  So when the scalar sums are `1`, `0`
and `1`, the operators `creationPairs u v₁` and `creationPairs u v₂` are isometries with orthogonal
ranges (`exists_properlyInfinite_of_coeff`), and they lie in every set of operators with the closure
properties of a Toeplitz algebra (`IsToeplitzClosed`).
-/

namespace GroupApproximation.Toeplitz

noncomputable section

open scoped ENNReal InnerProductSpace

variable {X : Type*} {ι : Type*} {κ : Type*}

/-- `M` is invariant under the creation operators of `E` and under the annihilation operators of
the sections whose pointwise inner products with `E` are continuous. -/
structure IsFockInvariant [TopologicalSpace X] (E : Set (Sections X (Fib ι)))
    (M : Submodule ℂ (Sections X (Fock ι))) : Prop where
  creation : ∀ ζ ∈ E, ∀ ω ∈ M, creationSec ζ ω ∈ M
  annihilation : ∀ ζ : Sections X (Fib ι), (∀ ζ' ∈ E, Continuous fun x => ⟪ζ x, ζ' x⟫_ℂ) →
    ∀ ω ∈ M, annihilationSec ζ ω ∈ M

/-- A section of `E` whose pointwise inner products with the sections of `E` are continuous. -/
def IsAdmissible [TopologicalSpace X] (E : Set (Sections X (Fib ι))) (ζ : Sections X (Fib ι)) :
    Prop :=
  ζ ∈ E ∧ ∀ ζ' ∈ E, Continuous fun x => ⟪ζ x, ζ' x⟫_ℂ

/-- The closure properties of a Toeplitz algebra: `1`, the creation operators of `E`, sums, scalar
multiples, products and adjoints. -/
structure IsToeplitzClosed (E : Set (Sections X (Fib ι))) {M : Submodule ℂ (Sections X (Fock ι))}
    (𝒯 : Set (Module.End ℂ M)) : Prop where
  one_mem : 1 ∈ 𝒯
  creation_mem : ∀ ζ ∈ E, ∀ T : Module.End ℂ M, (∀ (ω : M) (x : X) (w : List ι),
    (((T ω : M) : Sections X (Fock ι)) x : List ι → ℂ) w =
      tensorCoord (ζ x : ι → ℂ) ((ω : Sections X (Fock ι)) x : List ι → ℂ) w) → T ∈ 𝒯
  add_mem : ∀ S ∈ 𝒯, ∀ T ∈ 𝒯, S + T ∈ 𝒯
  smul_mem : ∀ c : ℂ, ∀ T ∈ 𝒯, c • T ∈ 𝒯
  mul_mem : ∀ S ∈ 𝒯, ∀ T ∈ 𝒯, S * T ∈ 𝒯
  adjoint_mem : ∀ T ∈ 𝒯, ∀ S, IsSectionAdjoint T S → S ∈ 𝒯

/-- `∑_k ℓ(u k) ℓ(v k)`. -/
def creationPairs [TopologicalSpace X] [Fintype κ] {E : Set (Sections X (Fib ι))}
    {M : Submodule ℂ (Sections X (Fock ι))} (hM : IsFockInvariant E M)
    (u v : κ → Sections X (Fib ι)) (hu : ∀ k, IsAdmissible E (u k))
    (hv : ∀ k, IsAdmissible E (v k)) : Module.End ℂ M :=
  ∑ k, creationEnd (u k) (hM.creation _ (hu k).1) * creationEnd (v k) (hM.creation _ (hv k).1)

/-- `∑_k ℓ(v k)* ℓ(u k)*`. -/
def annihilationPairs [TopologicalSpace X] [Fintype κ] {E : Set (Sections X (Fib ι))}
    {M : Submodule ℂ (Sections X (Fock ι))} (hM : IsFockInvariant E M)
    (u v : κ → Sections X (Fib ι)) (hu : ∀ k, IsAdmissible E (u k))
    (hv : ∀ k, IsAdmissible E (v k)) : Module.End ℂ M :=
  ∑ k, annihilationEnd (v k) (hM.annihilation _ (hv k).2) *
    annihilationEnd (u k) (hM.annihilation _ (hu k).2)

theorem isSectionAdjoint_creationPairs [TopologicalSpace X] [Fintype κ]
    {E : Set (Sections X (Fib ι))} {M : Submodule ℂ (Sections X (Fock ι))}
    (hM : IsFockInvariant E M) (u v : κ → Sections X (Fib ι)) (hu : ∀ k, IsAdmissible E (u k))
    (hv : ∀ k, IsAdmissible E (v k)) :
    IsSectionAdjoint (creationPairs hM u v hu hv) (annihilationPairs hM u v hu hv) :=
  fun ξ η x => by
    simp only [creationPairs, annihilationPairs, LinearMap.sum_apply, Module.End.mul_apply,
      Submodule.coe_sum, lp.coeFn_sum, Finset.sum_apply, sum_inner, inner_sum, creationEnd_apply,
      annihilationEnd_apply, inner_annihilation_right]

theorem annihilationPairs_mul_creationPairs_apply [TopologicalSpace X] [Fintype κ]
    {E : Set (Sections X (Fib ι))} {M : Submodule ℂ (Sections X (Fock ι))}
    (hM : IsFockInvariant E M) (u v u' v' : κ → Sections X (Fib ι))
    (hu : ∀ k, IsAdmissible E (u k)) (hv : ∀ k, IsAdmissible E (v k))
    (hu' : ∀ k, IsAdmissible E (u' k)) (hv' : ∀ k, IsAdmissible E (v' k)) (ω : M) (x : X) :
    (((annihilationPairs hM u' v' hu' hv' * creationPairs hM u v hu hv) ω : M) :
        Sections X (Fock ι)) x =
      (∑ i, ∑ j, ⟪u' i x, u j x⟫_ℂ * ⟪v' i x, v j x⟫_ℂ) • (ω : Sections X (Fock ι)) x := by
  simp only [annihilationPairs, creationPairs, Module.End.mul_apply, LinearMap.sum_apply, map_sum,
    Submodule.coe_sum, lp.coeFn_sum, Finset.sum_apply, annihilationEnd_apply, creationEnd_apply,
    annihilation_annihilation_creation_creation, Finset.sum_smul]
  exact Finset.sum_comm

theorem IsToeplitzClosed.zero_mem {E : Set (Sections X (Fib ι))}
    {M : Submodule ℂ (Sections X (Fock ι))} {𝒯 : Set (Module.End ℂ M)}
    (h : IsToeplitzClosed E 𝒯) : 0 ∈ 𝒯 := by
  have h0 := h.smul_mem 0 1 h.one_mem
  rwa [zero_smul] at h0

theorem IsToeplitzClosed.sum_mem {E : Set (Sections X (Fib ι))}
    {M : Submodule ℂ (Sections X (Fock ι))} {𝒯 : Set (Module.End ℂ M)}
    (h : IsToeplitzClosed E 𝒯) (s : Finset κ) (T : κ → Module.End ℂ M)
    (hT : ∀ k ∈ s, T k ∈ 𝒯) : ∑ k ∈ s, T k ∈ 𝒯 :=
  Finset.sum_induction T (· ∈ 𝒯) (fun _ _ ha hb => h.add_mem _ ha _ hb) h.zero_mem hT

theorem IsToeplitzClosed.creationEnd_mem {E : Set (Sections X (Fib ι))}
    {M : Submodule ℂ (Sections X (Fock ι))} {𝒯 : Set (Module.End ℂ M)}
    (h : IsToeplitzClosed E 𝒯) {ζ : Sections X (Fib ι)} (hζ : ζ ∈ E)
    (hM : ∀ ω ∈ M, creationSec ζ ω ∈ M) : creationEnd ζ hM ∈ 𝒯 :=
  h.creation_mem ζ hζ _ fun _ _ _ => rfl

theorem IsToeplitzClosed.creationPairs_mem [TopologicalSpace X] [Fintype κ]
    {E : Set (Sections X (Fib ι))} {M : Submodule ℂ (Sections X (Fock ι))}
    {𝒯 : Set (Module.End ℂ M)} (h : IsToeplitzClosed E 𝒯) (hM : IsFockInvariant E M)
    (u v : κ → Sections X (Fib ι)) (hu : ∀ k, IsAdmissible E (u k))
    (hv : ∀ k, IsAdmissible E (v k)) : creationPairs hM u v hu hv ∈ 𝒯 :=
  h.sum_mem _ _ fun k _ =>
    h.mul_mem _ (h.creationEnd_mem (hu k).1 _) _ (h.creationEnd_mem (hv k).1 _)

theorem end_ext_apply {M : Submodule ℂ (Sections X (Fock ι))} {S T : Module.End ℂ M}
    (h : ∀ (ω : M) (x : X), ((S ω : M) : Sections X (Fock ι)) x = ((T ω : M) : Sections X (Fock ι)) x) :
    S = T :=
  LinearMap.ext fun ω => Subtype.ext (lp.ext (funext (h ω)))

/-- Two isometries with orthogonal ranges from the scalar identities `1`, `0`, `1`. -/
theorem exists_properlyInfinite_of_coeff [TopologicalSpace X] [Fintype κ]
    {E : Set (Sections X (Fib ι))} {M : Submodule ℂ (Sections X (Fock ι))}
    (hM : IsFockInvariant E M) (u v₁ v₂ : κ → Sections X (Fib ι))
    (hu : ∀ k, IsAdmissible E (u k)) (hv₁ : ∀ k, IsAdmissible E (v₁ k))
    (hv₂ : ∀ k, IsAdmissible E (v₂ k))
    (h11 : ∀ x, ∑ i, ∑ j, ⟪u i x, u j x⟫_ℂ * ⟪v₁ i x, v₁ j x⟫_ℂ = 1)
    (h12 : ∀ x, ∑ i, ∑ j, ⟪u i x, u j x⟫_ℂ * ⟪v₁ i x, v₂ j x⟫_ℂ = 0)
    (h22 : ∀ x, ∑ i, ∑ j, ⟪u i x, u j x⟫_ℂ * ⟪v₂ i x, v₂ j x⟫_ℂ = 1) :
    ∃ s₁ s₂ t₁ t₂ : Module.End ℂ M,
      (∀ 𝒯 : Set (Module.End ℂ M), IsToeplitzClosed E 𝒯 → s₁ ∈ 𝒯 ∧ s₂ ∈ 𝒯) ∧
      IsSectionAdjoint s₁ t₁ ∧ IsSectionAdjoint s₂ t₂ ∧ t₁ * s₁ = 1 ∧ t₂ * s₂ = 1 ∧
      (s₁ * t₁) * (s₂ * t₂) = 0 := by
  have h0 : annihilationPairs hM u v₁ hu hv₁ * creationPairs hM u v₂ hu hv₂ = 0 :=
    end_ext_apply fun ω x => by
      rw [annihilationPairs_mul_creationPairs_apply, h12 x, zero_smul, LinearMap.zero_apply,
        Submodule.coe_zero, lp.coeFn_zero, Pi.zero_apply]
  refine ⟨creationPairs hM u v₁ hu hv₁, creationPairs hM u v₂ hu hv₂,
    annihilationPairs hM u v₁ hu hv₁, annihilationPairs hM u v₂ hu hv₂,
    fun 𝒯 h𝒯 => ⟨h𝒯.creationPairs_mem hM u v₁ hu hv₁, h𝒯.creationPairs_mem hM u v₂ hu hv₂⟩,
    isSectionAdjoint_creationPairs hM u v₁ hu hv₁, isSectionAdjoint_creationPairs hM u v₂ hu hv₂,
    end_ext_apply fun ω x => ?_, end_ext_apply fun ω x => ?_, ?_⟩
  · rw [annihilationPairs_mul_creationPairs_apply, h11 x, one_smul, Module.End.one_apply]
  · rw [annihilationPairs_mul_creationPairs_apply, h22 x, one_smul, Module.End.one_apply]
  · rw [mul_assoc, ← mul_assoc (annihilationPairs hM u v₁ hu hv₁), h0, zero_mul, mul_zero]

end

end GroupApproximation.Toeplitz
