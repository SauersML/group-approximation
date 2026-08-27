import GroupApproximation.Analysis.GaussianRoeOperator
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# Square roots in the uniform Roe algebra

This is the closing paragraph of Guentner--Kaminker's Theorem 3.2.  Given a
positive element `K` of the uniform Roe algebra, its positive square root `V`
is again in the uniform Roe algebra --- the continuous functional calculus of
an element lands in every closed ⋆-subalgebra containing it --- so `V` is a
norm limit of finite-propagation operators.  For a finite-propagation `W` close
to `V`,

```
    star V * V - star W * W = star V * (V - W) + star (V - W) * W ,
```

so `‖K - star W * W‖ ≤ ‖V - W‖ (‖V‖ + ‖W‖)`, and since matrix coefficients are
bounded by the operator norm the *kernel* of `star W * W` is uniformly close to
the kernel of `K`.  That kernel is a Gram kernel of finite width: exactly what
Yu's property A needs.

## Structure

The one step that reaches outside elementary Hilbert space theory ---
existence of the square root inside the subalgebra --- is isolated in
`exists_sqrt_mem`, so that everything downstream depends only on its statement.
It rests on Mathlib's `cfc_mem`: the continuous functional calculus of an
element is contained in any closed star subalgebra containing the element.
The square root is written as `cfc Real.sqrt K` in the real functional
calculus.  The normal and self-adjoint functional calculi are installed
locally below, and `cfc_mem` puts the result directly in the closed star
subalgebra.

This module and the assembly in `Analysis/GuentnerKaminkerEndpoint.lean` have
both been elaborated at the pinned toolchain.
-/

namespace GroupApproximation
namespace RoeSquareRoot

open ReducedGroupCStarTrace UniformRoe L2KernelOperator GaussianRoeOperator
open scoped InnerProductSpace

universe u

variable {G : Type u} [Group G] [DecidableEq G]

/-! ## The square root -/

/-! ### Functional calculus on `B(ℓ²(G))` -/

noncomputable local instance :
    ContinuousFunctionalCalculus ℂ (GroupHilbert G →L[ℂ] GroupHilbert G) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus

noncomputable local instance :
    ContinuousFunctionalCalculus ℝ (GroupHilbert G →L[ℂ] GroupHilbert G) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

/-- The real scalars act compatibly with the involution: a real scalar is its
own conjugate, so the complex statement gives the real one. -/
local instance : StarModule ℝ (GroupHilbert G →L[ℂ] GroupHilbert G) where
  star_smul r a := by
    have hr : ∀ b : GroupHilbert G →L[ℂ] GroupHilbert G,
        r • b = ((r : ℂ)) • b := fun b ↦ (Complex.coe_smul r b).symm
    rw [star_trivial r, hr a, hr (star a), star_smul, Complex.star_def,
      Complex.conj_ofReal]

/-- **The positive square root stays in the uniform Roe algebra.**

`uniformRoeSubalgebra` is by construction a topological closure, hence closed,
and `cfc_mem` says the continuous functional calculus of an element lands in
every closed star subalgebra containing it. -/
theorem exists_sqrt_mem {K : GroupHilbert G →L[ℂ] GroupHilbert G}
    (hmem : K ∈ uniformRoeSubalgebra G) (hK : 0 ≤ K) :
    ∃ V : GroupHilbert G →L[ℂ] GroupHilbert G,
      V ∈ uniformRoeSubalgebra G ∧ IsSelfAdjoint V ∧ V * V = K := by
  have hclosed : IsClosed ((uniformRoeSubalgebra G : StarSubalgebra ℂ _) :
      Set (GroupHilbert G →L[ℂ] GroupHilbert G)) :=
    (finitePropagationSubalgebra G).isClosed_topologicalClosure
  haveI := hclosed
  have hKsa : IsSelfAdjoint K := IsSelfAdjoint.of_nonneg hK
  refine ⟨cfc (R := ℝ) (p := IsSelfAdjoint) Real.sqrt K,
    cfc_mem (p := IsSelfAdjoint) Real.sqrt hmem,
    cfc_predicate (p := IsSelfAdjoint) Real.sqrt K, ?_⟩
  have hmul : cfc (R := ℝ) (p := IsSelfAdjoint) Real.sqrt K *
        cfc (R := ℝ) (p := IsSelfAdjoint) Real.sqrt K
      = cfc (R := ℝ) (p := IsSelfAdjoint)
          (fun x : ℝ ↦ Real.sqrt x * Real.sqrt x) K :=
    (cfc_mul (p := IsSelfAdjoint) _ _ K Real.continuous_sqrt.continuousOn
      Real.continuous_sqrt.continuousOn).symm
  have hid : cfc (R := ℝ) (p := IsSelfAdjoint)
        (fun x : ℝ ↦ Real.sqrt x * Real.sqrt x) K =
      cfc (R := ℝ) (p := IsSelfAdjoint) (id : ℝ → ℝ) K := by
    refine cfc_congr (p := IsSelfAdjoint) fun x hx ↦ ?_
    exact Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hK hx)
  rw [hmul, hid, cfc_id (p := IsSelfAdjoint) (ha := hKsa) ℝ K]

/-! ## Finite-width Gram approximation -/

/-- **The operator step of Guentner--Kaminker, discharged.**  A positive element
of the uniform Roe algebra has, at every tolerance, a finite-propagation `W`
whose Gram kernel `⟨W δ_s, W δ_t⟩` is uniformly within that tolerance of its
own kernel. -/
theorem exists_finiteWidth_gram {K : GroupHilbert G →L[ℂ] GroupHilbert G}
    (hmem : K ∈ uniformRoeSubalgebra G) (hK : 0 ≤ K) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (S : Finset G) (W : GroupHilbert G →L[ℂ] GroupHilbert G),
      HasPropagationIn G W (S : Set G) ∧
        ∀ s t : G,
          ‖matrixCoeff G K s t - matrixCoeff G (star W * W) s t‖ ≤ δ := by
  obtain ⟨V, hVmem, hVsa, hVsq⟩ := exists_sqrt_mem hmem hK
  -- the tolerance at which to approximate `V`
  set η : ℝ := min 1 (δ / (2 * ‖V‖ + 1)) with hηdef
  have hden : (0 : ℝ) < 2 * ‖V‖ + 1 := by positivity
  have hη : 0 < η := lt_min one_pos (div_pos hδ hden)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηδ : η * (2 * ‖V‖ + 1) ≤ δ := by
    have h := min_le_right (1 : ℝ) (δ / (2 * ‖V‖ + 1))
    calc η * (2 * ‖V‖ + 1) ≤ (δ / (2 * ‖V‖ + 1)) * (2 * ‖V‖ + 1) :=
          mul_le_mul_of_nonneg_right h (le_of_lt hden)
      _ = δ := by field_simp
  -- a finite-propagation operator within `η` of `V`
  have hVclosure : V ∈ closure ((finitePropagationSubalgebra G :
      StarSubalgebra ℂ (GroupHilbert G →L[ℂ] GroupHilbert G)) :
      Set (GroupHilbert G →L[ℂ] GroupHilbert G)) := hVmem
  obtain ⟨W, hWmem, hWdist⟩ := Metric.mem_closure_iff.mp hVclosure η hη
  obtain ⟨S, hS⟩ : FinitePropagation G W := hWmem
  refine ⟨S, W, hS, ?_⟩
  intro s t
  -- the algebraic identity behind the estimate
  have hVW : ‖V - W‖ ≤ η := by
    rw [← dist_eq_norm]
    exact le_of_lt hWdist
  have hWnorm : ‖W‖ ≤ ‖V‖ + η := by
    have h : ‖W‖ ≤ ‖V‖ + ‖V - W‖ := by
      have := norm_sub_norm_le V W
      have h2 : ‖W‖ - ‖V‖ ≤ ‖V - W‖ := by
        rw [← norm_neg (V - W), neg_sub]
        exact norm_sub_norm_le W V
      linarith
    linarith
  have hsplit : K - star W * W = star V * (V - W) + star (V - W) * W := by
    rw [← hVsq]
    rw [star_sub, hVsa.star_eq]
    noncomm_ring
  have hnorm : ‖K - star W * W‖ ≤ δ := by
    rw [hsplit]
    have h1 : ‖star V * (V - W)‖ ≤ ‖V‖ * η := by
      refine le_trans (norm_mul_le _ _) ?_
      have hstarV : ‖star V‖ = ‖V‖ := by
        rw [ContinuousLinearMap.star_eq_adjoint, LinearIsometryEquiv.norm_map]
      rw [hstarV]
      exact mul_le_mul_of_nonneg_left hVW (norm_nonneg V)
    have h2 : ‖star (V - W) * W‖ ≤ η * (‖V‖ + η) := by
      refine le_trans (norm_mul_le _ _) ?_
      have hVWstar : ‖star (V - W)‖ ≤ η := by
        rw [ContinuousLinearMap.star_eq_adjoint, LinearIsometryEquiv.norm_map]
        exact hVW
      exact mul_le_mul hVWstar hWnorm (norm_nonneg _) (le_of_lt hη)
    have h3 : ‖star V * (V - W) + star (V - W) * W‖ ≤ ‖V‖ * η + η * (‖V‖ + η) :=
      le_trans (norm_add_le _ _) (add_le_add h1 h2)
    have h4 : ‖V‖ * η + η * (‖V‖ + η) ≤ η * (2 * ‖V‖ + 1) := by
      nlinarith [norm_nonneg V, hη.le, hη1]
    linarith
  -- matrix coefficients are bounded by the operator norm
  have hcoeff : matrixCoeff G K s t - matrixCoeff G (star W * W) s t
      = matrixCoeff G (K - star W * W) s t := (matrixCoeff_sub K (star W * W) s t).symm
  rw [hcoeff]
  exact le_trans (norm_matrixCoeff_le _ s t) hnorm

end RoeSquareRoot
end GroupApproximation
