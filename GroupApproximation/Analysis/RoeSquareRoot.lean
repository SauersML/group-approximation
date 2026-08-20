import GroupApproximation.Analysis.GaussianRoeOperator

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
Note that `cfc Real.sqrt` is used rather than `CFC.sqrt`; the latter is
`cfcₙ NNReal.sqrt`, and the non-unital membership lemma `cfcₙ_mem` is stated
only for `RCLike` scalars, which `ℝ≥0` is not.

**Status: authored, not yet elaborated.**  Everything up to and including
`Analysis/GaussianRoeOperator.lean` has been built at the pinned toolchain;
this module and the assembly that follows it have not.
-/

namespace GroupApproximation
namespace RoeSquareRoot

open ReducedGroupCStarTrace UniformRoe L2KernelOperator GaussianRoeOperator
open scoped InnerProductSpace

universe u

variable {G : Type u} [Group G] [DecidableEq G]

/-! ## The square root -/

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
  refine ⟨cfc Real.sqrt K, cfc_mem Real.sqrt hmem, ?_, ?_⟩
  · exact cfc_predicate Real.sqrt K
  · have hmul : cfc Real.sqrt K * cfc Real.sqrt K
        = cfc (fun x : ℝ ↦ Real.sqrt x * Real.sqrt x) K :=
      (cfc_mul _ _ K Real.continuous_sqrt.continuousOn
        Real.continuous_sqrt.continuousOn).symm
    have hid : cfc (fun x : ℝ ↦ Real.sqrt x * Real.sqrt x) K = cfc (id : ℝ → ℝ) K := by
      refine cfc_congr fun x hx ↦ ?_
      exact Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hK hx)
    rw [hmul, hid, cfc_id ℝ K]

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
    rw [hVsa.star_eq] at *
    rw [← hVsq]
    rw [star_sub, hVsa.star_eq]
    ring
  have hnorm : ‖K - star W * W‖ ≤ δ := by
    rw [hsplit]
    have h1 : ‖star V * (V - W)‖ ≤ ‖V‖ * η := by
      refine le_trans (norm_mul_le _ _) ?_
      rw [norm_star]
      exact mul_le_mul_of_nonneg_left hVW (norm_nonneg _)
    have h2 : ‖star (V - W) * W‖ ≤ η * (‖V‖ + η) := by
      refine le_trans (norm_mul_le _ _) ?_
      rw [norm_star]
      exact mul_le_mul hVW hWnorm (norm_nonneg _) (le_of_lt hη)
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
