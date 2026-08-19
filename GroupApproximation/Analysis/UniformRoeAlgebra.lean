import GroupApproximation.Analysis.ReducedGroupCStarTrace
import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-!
# The uniform Roe algebra of a group

## The ledger row, and what this module is

`SO.16`'s standing record (`CStarExactness.lean`) lists among the missing
objects, for Ozawa's route from property A to exactness of the reduced
algebra: *"no crossed products and no uniform Roe algebra, which is what
Ozawa's proof of `property A ⟹ Cred(G) exact` runs through."*  This module
removes the second absence: the uniform Roe algebra of a group now exists,
with the two facts every use of it starts from --- the finite-propagation
operators form a ⋆-subalgebra, and the reduced group C⋆-algebra sits inside
the uniform Roe algebra.

* `matrixCoeff T s t` --- the matrix coefficient `(T δ_t)(s)`, taken
  coordinatewise; inner products appear only for the adjoint.
* `HasPropagationIn T S` --- every nonvanishing coefficient has `s * t⁻¹`
  in the window `S`; `λ_g` has propagation in `{g}`.
* `matrixCoeff_mul` --- against a finite-propagation right factor the
  product coefficient is a finite convolution over the translated window;
  hence finite propagation is closed under multiplication with windows
  multiplying, under the adjoint with the window inverting, and under the
  linear operations.
* `finitePropagationSubalgebra` / `uniformRoeSubalgebra` --- the
  ⋆-subalgebra of finite-propagation operators and its norm closure, the
  uniform Roe algebra `C⋆_u(G)`.
* `reducedGroupCStar_le_uniformRoe` --- `C⋆_red(G) ≤ C⋆_u(G)`.

## What remains for the row

Everything analytic: Schur multipliers of positive-type kernels, the
property-A approximation of the identity of `C⋆_u(G)`, and nuclearity of
the uniform Roe algebra from property A --- the content of Ozawa's theorem.
None of it is claimed here, and `SO.16` remains graded exactly as the
standing record says.
-/

namespace GroupApproximation
namespace UniformRoe

open ReducedGroupCStarTrace
open scoped InnerProductSpace Pointwise

universe u

noncomputable section

variable (G : Type u) [Group G] [DecidableEq G]

/-- The point mass at a group element. -/
def delta (g : G) : GroupHilbert G := lp.single 2 g (1 : ℂ)

omit [Group G] in
theorem delta_apply_self (g : G) : delta G g g = 1 :=
  lp.single_apply_self 2 g 1

omit [Group G] in
theorem delta_apply_ne {x g : G} (h : x ≠ g) : delta G g x = 0 :=
  lp.single_apply_ne 2 g 1 h

/-- The matrix coefficient of a bounded operator on `ℓ²(G)`, taken
coordinatewise: `(T δ_t)(s)`. -/
def matrixCoeff (T : GroupHilbert G →L[ℂ] GroupHilbert G) (s t : G) : ℂ :=
  T (delta G t) s

omit [Group G] in
@[simp] theorem matrixCoeff_def (T : GroupHilbert G →L[ℂ] GroupHilbert G)
    (s t : G) : matrixCoeff G T s t = T (delta G t) s := rfl

omit [Group G] in
/-- Coordinates are inner products against point masses. -/
theorem coord_eq_inner (v : GroupHilbert G) (s : G) :
    v s = ⟪delta G s, v⟫_ℂ := by
  show v s = ⟪lp.single 2 s (1 : ℂ), v⟫_ℂ
  rw [lp.inner_single_left]
  simp

/-- **Propagation in a window**: every nonvanishing coefficient has
`s * t⁻¹` in `S`. -/
def HasPropagationIn (T : GroupHilbert G →L[ℂ] GroupHilbert G)
    (S : Set G) : Prop :=
  ∀ s t : G, matrixCoeff G T s t ≠ 0 → s * t⁻¹ ∈ S

/-- Finite propagation. -/
def FinitePropagation (T : GroupHilbert G →L[ℂ] GroupHilbert G) : Prop :=
  ∃ S : Finset G, HasPropagationIn G T (S : Set G)

variable {G}

/-! ## Coefficient calculus -/

omit [Group G] in
theorem matrixCoeff_add (T T' : GroupHilbert G →L[ℂ] GroupHilbert G)
    (s t : G) : matrixCoeff G (T + T') s t
      = matrixCoeff G T s t + matrixCoeff G T' s t := by
  show lp.evalCLM ℂ (fun _ : G ↦ ℂ) 2 s ((T + T') (delta G t))
    = lp.evalCLM ℂ (fun _ : G ↦ ℂ) 2 s (T (delta G t))
      + lp.evalCLM ℂ (fun _ : G ↦ ℂ) 2 s (T' (delta G t))
  rw [add_apply, map_add]

omit [Group G] in
theorem matrixCoeff_smul (z : ℂ) (T : GroupHilbert G →L[ℂ] GroupHilbert G)
    (s t : G) : matrixCoeff G (z • T) s t = z * matrixCoeff G T s t := by
  show lp.evalCLM ℂ (fun _ : G ↦ ℂ) 2 s ((z • T) (delta G t))
    = z * lp.evalCLM ℂ (fun _ : G ↦ ℂ) 2 s (T (delta G t))
  rw [smul_apply, map_smul, smul_eq_mul]

omit [Group G] in
/-- The adjoint coefficient is the conjugate transposed coefficient. -/
theorem matrixCoeff_star (T : GroupHilbert G →L[ℂ] GroupHilbert G)
    (s t : G) : matrixCoeff G (star T) s t
      = (starRingEnd ℂ) (matrixCoeff G T t s) := by
  rw [matrixCoeff_def, matrixCoeff_def, coord_eq_inner ((star T) _) s,
    coord_eq_inner (T _) t, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  exact (inner_conj_symm _ _).symm

/-! ## Basic examples -/

theorem hasPropagationIn_one :
    HasPropagationIn G (1 : GroupHilbert G →L[ℂ] GroupHilbert G)
      {(1 : G)} := by
  intro s t h0
  rw [matrixCoeff_def, one_apply_eq_self] at h0
  have hst : s = t := by
    by_contra hne
    exact h0 (delta_apply_ne hne)
  rw [hst, mul_inv_cancel]
  rfl

theorem hasPropagationIn_leftRegular (g : G) :
    HasPropagationIn G (leftRegularOperator G g) {g} := by
  intro s t h0
  rw [matrixCoeff_def, leftRegularOperator_apply] at h0
  have hst : g⁻¹ * s = t := by
    by_contra hne
    exact h0 (delta_apply_ne hne)
  have hs : s = g * t := by
    rw [← hst, mul_inv_cancel_left]
  have : s * t⁻¹ = g := by
    rw [hs, mul_inv_cancel_right]
  rw [this]
  rfl

/-! ## Stability of propagation windows -/

theorem hasPropagationIn_add {T T' : GroupHilbert G →L[ℂ] GroupHilbert G}
    {S S' : Set G} (hT : HasPropagationIn G T S)
    (hT' : HasPropagationIn G T' S') :
    HasPropagationIn G (T + T') (S ∪ S') := by
  intro s t h0
  rw [matrixCoeff_add] at h0
  by_cases hc : matrixCoeff G T s t = 0
  · have h2 : matrixCoeff G T' s t ≠ 0 := by
      intro h
      exact h0 (by rw [hc, h, add_zero])
    exact Or.inr (hT' s t h2)
  · exact Or.inl (hT s t hc)

theorem hasPropagationIn_smul {T : GroupHilbert G →L[ℂ] GroupHilbert G}
    {S : Set G} (z : ℂ) (hT : HasPropagationIn G T S) :
    HasPropagationIn G (z • T) S := by
  intro s t h0
  rw [matrixCoeff_smul] at h0
  have h1 : matrixCoeff G T s t ≠ 0 := by
    intro h
    exact h0 (by rw [h, mul_zero])
  exact hT s t h1

theorem hasPropagationIn_star {T : GroupHilbert G →L[ℂ] GroupHilbert G}
    {S : Set G} (hT : HasPropagationIn G T S) :
    HasPropagationIn G (star T) S⁻¹ := by
  intro s t h0
  rw [matrixCoeff_star] at h0
  have h1 : matrixCoeff G T t s ≠ 0 := by
    intro h
    exact h0 (by rw [h, map_zero])
  have h2 : t * s⁻¹ ∈ S := hT t s h1
  have h3 : s * t⁻¹ = (t * s⁻¹)⁻¹ := by group
  rw [h3]
  exact Set.inv_mem_inv.mpr h2

/-! ## Multiplication: the finite convolution -/

omit [Group G] in
/-- A vector supported in a finite set is the finite sum of its point
masses. -/
theorem eq_sum_single_of_support_subset (v : GroupHilbert G) (F : Finset G)
    (hv : ∀ x : G, x ∉ F → v x = 0) :
    v = ∑ u ∈ F, v u • delta G u := by
  rw [lp.ext_iff]
  funext x
  have hR : (∑ u ∈ F, v u • delta G u) x
      = ∑ u ∈ F, v u * (delta G u x) := by
    have h1 := map_sum (lp.evalCLM ℂ (fun _ : G ↦ ℂ) 2 x)
      (fun u => v u • delta G u) F
    have h2 : (∑ u ∈ F, v u • delta G u) x
        = lp.evalCLM ℂ (fun _ : G ↦ ℂ) 2 x (∑ u ∈ F, v u • delta G u) :=
      rfl
    rw [h2, h1]
    refine Finset.sum_congr rfl fun u _ => ?_
    have h3 : lp.evalCLM ℂ (fun _ : G ↦ ℂ) 2 x (v u • delta G u)
        = v u • lp.evalCLM ℂ (fun _ : G ↦ ℂ) 2 x (delta G u) :=
      map_smul _ _ _
    rw [h3, smul_eq_mul]
  by_cases hx : x ∈ F
  · show v x = _
    rw [hR, Finset.sum_eq_single x]
    · rw [delta_apply_self, mul_one]
    · intro u _ hu
      rw [delta_apply_ne (Ne.symm hu), mul_zero]
    · intro h
      exact absurd hx h
  · show v x = _
    rw [hv x hx, hR]
    refine (Finset.sum_eq_zero fun u hu => ?_).symm
    have hne : x ≠ u := by
      intro h
      rw [h] at hx
      exact hx hu
    rw [delta_apply_ne hne, mul_zero]

/-- **The product coefficient is a finite convolution** over the window
translate of a finite-propagation right factor. -/
theorem matrixCoeff_mul (T T' : GroupHilbert G →L[ℂ] GroupHilbert G)
    {S' : Finset G} (hT' : HasPropagationIn G T' (S' : Set G)) (s t : G) :
    matrixCoeff G (T * T') s t
      = ∑ u ∈ S'.image (· * t),
          matrixCoeff G T' u t * matrixCoeff G T s u := by
  have hsupp : ∀ x : G, x ∉ S'.image (· * t) →
      (T' (delta G t)) x = 0 := by
    intro x hx
    by_contra h0
    have h1 : x * t⁻¹ ∈ (S' : Set G) := hT' x t h0
    refine hx (Finset.mem_image.mpr ⟨x * t⁻¹, h1, ?_⟩)
    exact inv_mul_cancel_right x t
  have hdec := eq_sum_single_of_support_subset (T' (delta G t))
    (S'.image (· * t)) hsupp
  have hΦ : matrixCoeff G (T * T') s t
      = ((lp.evalCLM ℂ (fun _ : G ↦ ℂ) 2 s).comp T) (T' (delta G t)) := rfl
  rw [hΦ, hdec, map_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  have h2 : ((lp.evalCLM ℂ (fun _ : G ↦ ℂ) 2 s).comp T)
      ((T' (delta G t)) u • delta G u)
      = (T' (delta G t)) u
          • ((lp.evalCLM ℂ (fun _ : G ↦ ℂ) 2 s).comp T) (delta G u) :=
    map_smul _ _ _
  rw [h2, smul_eq_mul]
  rfl

/-- Finite-propagation windows multiply under composition. -/
theorem hasPropagationIn_mul {T T' : GroupHilbert G →L[ℂ] GroupHilbert G}
    {S S' : Finset G} (hT : HasPropagationIn G T (S : Set G))
    (hT' : HasPropagationIn G T' (S' : Set G)) :
    HasPropagationIn G (T * T') ((S * S' : Finset G) : Set G) := by
  intro s t h0
  rw [matrixCoeff_mul T T' hT' s t] at h0
  obtain ⟨u, hu, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h0
  have h1 : matrixCoeff G T' u t ≠ 0 := by
    intro h
    exact hne (by rw [h, zero_mul])
  have h2 : matrixCoeff G T s u ≠ 0 := by
    intro h
    exact hne (by rw [h, mul_zero])
  have e1 : u * t⁻¹ ∈ (S' : Set G) := hT' u t h1
  have e2 : s * u⁻¹ ∈ (S : Set G) := hT s u h2
  have e3 : s * t⁻¹ = (s * u⁻¹) * (u * t⁻¹) := by group
  rw [e3]
  exact Finset.mul_mem_mul e2 e1

/-! ## The uniform Roe algebra -/

variable (G)

/-- **The finite-propagation ⋆-subalgebra** of `B(ℓ²(G))`. -/
def finitePropagationSubalgebra :
    StarSubalgebra ℂ (GroupHilbert G →L[ℂ] GroupHilbert G) where
  carrier := {T | FinitePropagation G T}
  mul_mem' := by
    rintro ⟨S, hS⟩ ⟨S', hS'⟩
    exact ⟨S * S', hasPropagationIn_mul hS hS'⟩
  add_mem' := by
    rintro ⟨S, hS⟩ ⟨S', hS'⟩
    refine ⟨S ∪ S', ?_⟩
    have h1 := hasPropagationIn_add hS hS'
    rwa [← Finset.coe_union] at h1
  algebraMap_mem' := by
    intro z
    refine ⟨{(1 : G)}, ?_⟩
    have he : algebraMap ℂ (GroupHilbert G →L[ℂ] GroupHilbert G) z
        = z • (1 : GroupHilbert G →L[ℂ] GroupHilbert G) :=
      Algebra.algebraMap_eq_smul_one z
    rw [he]
    have h1 := hasPropagationIn_smul z (hasPropagationIn_one (G := G))
    intro s t h0
    have h2 := h1 s t h0
    have h3 : s * t⁻¹ = 1 := h2
    rw [Finset.coe_singleton]
    exact h3
  star_mem' := by
    rintro ⟨S, hS⟩
    refine ⟨S⁻¹, ?_⟩
    have h1 := hasPropagationIn_star hS
    rwa [← Finset.coe_inv] at h1

/-- **The uniform Roe algebra** `C⋆_u(G)`: the norm closure of the
finite-propagation operators. -/
def uniformRoeSubalgebra :
    StarSubalgebra ℂ (GroupHilbert G →L[ℂ] GroupHilbert G) :=
  (finitePropagationSubalgebra G).topologicalClosure

/-- **The reduced group C⋆-algebra sits inside the uniform Roe algebra**:
every left regular operator has finite propagation. -/
theorem reducedGroupCStar_le_uniformRoe :
    reducedGroupCStarSubalgebra G ≤ uniformRoeSubalgebra G := by
  refine StarSubalgebra.topologicalClosure_mono ?_
  refine StarAlgebra.adjoin_le ?_
  rintro _ ⟨g, rfl⟩
  refine ⟨{g}, ?_⟩
  intro s t h0
  have h2 : s * t⁻¹ ∈ ({g} : Set G) :=
    hasPropagationIn_leftRegular g s t h0
  have h3 : s * t⁻¹ = g := h2
  rw [Finset.coe_singleton]
  exact h3

end

end UniformRoe
end GroupApproximation
