import GroupApproximation.Analysis.LanceBlockOperator
import GroupApproximation.Analysis.CStarCompletelyPositiveForm
import GroupApproximation.Analysis.CStarUnitalCPContractive

/-!
# Form positivity implies complete positivity

`CStarCompletelyPositiveForm.IsCompletelyPositive.form_nonneg` runs one way: a
completely positive map has nonnegative sesquilinear sums.  Every dilation
argument consumes that direction, and so nothing in the repository needed the
converse --- until an input arrived stated in the form vocabulary
(`Quasidiagonal.IsCompletelyPositiveOnMatrices`) and had to be handed to the
Stinespring chain, which speaks the factorization vocabulary.

This file closes the loop, at matrix-sized targets:

> a `⋆`-preserving linear map into `B(ℂᵏ)` whose sesquilinear sums are
> nonnegative and real is completely positive.

## Why it is not circular, and why `⋆`-preservation is a hypothesis

The factorization is `LanceBlockOperator.exists_factor_of_blockOp_form_nonneg`,
which takes the operator square root of the block operator and cuts it into
blocks.  It asks for two things: that the block matrix be self-adjoint, and
that its form be nonnegative.  The second is the hypothesis here, transported
one index at a time.  The first is *not* implied by the form condition ---
positivity of a quadratic form's real part says nothing about a matrix's
anti-Hermitian part --- so it has to come from `⋆`-preservation of the map,
which is why that appears as a hypothesis rather than as a consequence.

At the site this exists for, `Quasidiagonal.ucp_map_star` supplies it, itself
proved from the reality clause of the same form condition.  So nothing is
assumed twice: reality gives `⋆`-preservation, `⋆`-preservation gives
self-adjointness of the block matrix, and nonnegativity gives the rest.

## The transport

For `M = star N * N` the entries expand as `M i j = ∑ₖ (N k i)⋆ (N k j)`, so the
block form at `v` is `∑ₖ` of the form at the tuple `a = N k ·`.  Each summand is
the hypothesis at that tuple, and a sum of nonnegative reals is nonnegative.
Self-adjointness is the same expansion read once: `star M = M` because
`star (star N * N) = star N * N`, and `⋆`-preservation moves that through the
map.
-/

namespace GroupApproximation
namespace CStarExactness

open scoped InnerProductSpace

noncomputable section

universe u

variable {A : Type u} [CStarAlgebra A] {k : ℕ}

/-- **Form positivity implies complete positivity**, at a matrix-sized target.

The `⋆`-preservation hypothesis is what makes the transported block matrix
self-adjoint; see the module docstring for why the form condition cannot supply
it on its own. -/
theorem isCompletelyPositive_of_form
    (ψ : A →ₗ[ℂ] (EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k)))
    (hstar : ∀ b : A, ψ (star b) = star (ψ b))
    (hform : ∀ (m : ℕ) (a : Fin m → A) (v : Fin m → EuclideanSpace ℂ (Fin k)),
      0 ≤ (∑ i : Fin m, ∑ j : Fin m,
        ⟪v i, ψ (star (a i) * a j) (v j)⟫_ℂ).re) :
    IsCompletelyPositive ψ := by
  classical
  intro n M hM
  obtain ⟨N, hN⟩ := hM
  -- the source matrix is self-adjoint, entry by entry
  have hMsa : star M = M := by
    rw [hN, star_mul, star_star]
  have hMentry : ∀ i j : Fin n, star (M j i) = M i j := by
    intro i j
    have h := congrArg (fun P : CStarMatrix (Fin n) (Fin n) A => P i j) hMsa
    simpa using h
  -- and its entries are the sums the hypothesis is stated at
  have hMsum : ∀ i j : Fin n, M i j = ∑ l : Fin n, star (N l i) * N l j := by
    intro i j
    rw [hN, cstarMatrix_mul_apply]
    exact Finset.sum_congr rfl fun l _ ↦ by rw [cstarMatrix_star_apply]
  refine exists_factor_of_blockOp_form_nonneg ?_ ?_
  · -- self-adjointness of the transported matrix
    apply CStarMatrix.ext
    intro i j
    rw [cstarMatrix_star_apply]
    show star (ψ (M j i)) = ψ (M i j)
    rw [← hstar, hMentry]
  · -- nonnegativity of its form
    intro v
    rw [inner_blockOp]
    have hexp : ∀ i j : Fin n,
        ⟪v i, (M.map ⇑ψ) i j (v j)⟫_ℂ
          = ∑ l : Fin n, ⟪v i, ψ (star (N l i) * N l j) (v j)⟫_ℂ := by
      intro i j
      show ⟪v i, ψ (M i j) (v j)⟫_ℂ = _
      rw [hMsum i j, map_sum, _root_.sum_apply, inner_sum]
    rw [Finset.sum_congr rfl fun i _ ↦
      Finset.sum_congr rfl fun j _ ↦ hexp i j]
    have hswap : ∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin n,
          ⟪v i, ψ (star (N l i) * N l j) (v j)⟫_ℂ
        = ∑ l : Fin n, ∑ i : Fin n, ∑ j : Fin n,
          ⟪v i, ψ (star (N l i) * N l j) (v j)⟫_ℂ := by
      calc ∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin n,
            ⟪v i, ψ (star (N l i) * N l j) (v j)⟫_ℂ
          = ∑ i : Fin n, ∑ l : Fin n, ∑ j : Fin n,
            ⟪v i, ψ (star (N l i) * N l j) (v j)⟫_ℂ :=
            Finset.sum_congr rfl fun i _ ↦ Finset.sum_comm
        _ = ∑ l : Fin n, ∑ i : Fin n, ∑ j : Fin n,
            ⟪v i, ψ (star (N l i) * N l j) (v j)⟫_ℂ := Finset.sum_comm
    rw [hswap, Complex.re_sum]
    refine Finset.sum_nonneg fun l _ ↦ ?_
    exact hform n (fun i ↦ N l i) (fun i ↦ v i)

/-- **A unital map that is completely positive in the form sense is a
contraction.**  `isCompletelyPositive_of_form` composed with the Stinespring
estimate of `Analysis/CStarUnitalCPContractive`.

This is the shape the Lance approximation needs.  `NuclearReducedCPAP` hands out
its `down` with exactly these three properties --- form positivity,
`⋆`-preservation, unitality --- and `IsNuclearMap` asks its `α` for
`‖α a‖ ≤ ‖a‖`, which no part of the CPAP supplies directly.  The `up` side needs
no companion: it arrives already carrying `IsCompletelyPositive`, so
`norm_apply_le_of_unital` applies to it unchanged. -/
theorem norm_le_of_form_unital
    (ψ : A →ₗ[ℂ] (EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k)))
    (hstar : ∀ b : A, ψ (star b) = star (ψ b))
    (hform : ∀ (m : ℕ) (a : Fin m → A) (v : Fin m → EuclideanSpace ℂ (Fin k)),
      0 ≤ (∑ i : Fin m, ∑ j : Fin m,
        ⟪v i, ψ (star (a i) * a j) (v j)⟫_ℂ).re)
    (h1 : ψ 1 = 1) (b : A) :
    ‖ψ b‖ ≤ ‖b‖ :=
  (isCompletelyPositive_of_form ψ hstar hform).norm_apply_le_of_unital h1 b

end

end CStarExactness
end GroupApproximation
