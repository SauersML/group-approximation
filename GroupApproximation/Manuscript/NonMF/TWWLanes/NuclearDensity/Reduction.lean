import GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.TraceFacts
import GroupApproximation.Manuscript.MFRecognition.TensorSynchronizationData
import GroupApproximation.Meta.AxiomGuard

/-!
# Lane nm-tww-12, part 3: the τ-dependent reduction, and the lane endpoint

Fix a tracial state `τ`, a finite `F` and `ε > 0`.

1. `sqrtControl` gives `F'` and `η`.  Apply `cpap` at `F ∪ F'` with tolerance
   `δ = min (η/2) ε`, which gives `ρ` and `ψ`.
2. Put `ω = τ ∘ ψ` and `h = densityOf ω`.  Since `ψ` preserves stars and `τ` is hermitian
   (`apply_star_of_nonneg`), `h` is Hermitian.  It is positive semidefinite because
   `ψ(v v⋆) = c⋆c`, and `tr h = τ(ψ 1) = 1`.
3. By traciality, `tr((hρ(a) − ρ(a)h)x) = τ(ψ(ρ(a)x) − aψ(x)) − τ(ψ(xρ(a)) − ψ(x)a)`.  The
   bimodule clauses bound this by `2δ‖x‖ ≤ η‖x‖`.  Also
   `tr(h(ρ(ab) − ρ(a)ρ(b))) = τ(ψ(…))`, which is at most `δ ≤ η` in modulus.
4. `sqrtControl` then returns a Hermitian `T` with `T² = h` and the commutator bound.  The
   trace clause and weighted multiplicativity follow from `trace_T_mul_T` and
   `trace_conjTranspose_mul_T`, together with `‖τ z‖ ≤ ‖z‖`.

Separability of `A` and faithfulness of `τ` are never used.
-/

namespace GroupApproximation
namespace Manuscript.NonMF.TWWLanes.NuclearDensity

open Matrix Quasidiagonal
open scoped Matrix.Norms.L2Operator ComplexOrder

noncomputable section

universe u

/-- **The reduction.**  On a unital C⋆-algebra with ucp matrix factorizations and
Powers--Størmer control, every tracial state has approximately invariant densities. -/
theorem hasApproxInvariantDensities_of_gap {A : Type u} [CStarAlgebra A]
    (hcpap : IsMatrixCPAP A) (hsqrt : HasSqrtCommutatorControl A) (τ : TracialState A) :
    NuclearAmenable.HasApproxInvariantDensities (fun a : A ↦ τ a) := by
  classical
  intro F ε hε
  have hτn : ∀ z : A, ‖τ.toLinearMap z‖ ≤ ‖z‖ := fun z ↦
    MFRecognition.TensorSynchronization.norm_tracialState_le τ z
  obtain ⟨F', η, hη, hsq⟩ := hsqrt F ε hε
  have hδ : 0 < min (η / 2) ε := lt_min (by linarith) hε
  have hδη : min (η / 2) ε ≤ η / 2 := min_le_left _ _
  have hδε : min (η / 2) ε ≤ ε := min_le_right _ _
  obtain ⟨Y, ρ, ψ, hρ1, hρcp, hρn, hρs, hψ1, hψpos, hψs, hψρ, hbim, hmul, hmul2⟩ :=
    hcpap (F ∪ F') (min (η / 2) ε) hδ
  obtain ⟨ω, hω⟩ : ∃ ω : Matrix Y Y ℂ →ₗ[ℂ] ℂ, ∀ X, ω X = τ.toLinearMap (ψ X) :=
    ⟨τ.toLinearMap ∘ₗ ψ, fun _ ↦ rfl⟩
  have hωs : ∀ M : Matrix Y Y ℂ, ω (star M) = star (ω M) := fun M ↦ by
    rw [hω, hω, hψs]
    exact apply_star_of_nonneg τ.toLinearMap τ.map_star_mul_self_nonneg (ψ M)
  have hωpos : ∀ v : Y → ℂ, 0 ≤ ω (vecMulVec v (star v)) := fun v ↦ by
    obtain ⟨c, hc⟩ := hψpos v
    rw [hω, hc]
    exact τ.map_star_mul_self_nonneg c
  have hPSD : (densityOf ω).PosSemidef := densityOf_posSemidef ω hωs hωpos
  have htr : Matrix.trace (densityOf ω) = 1 := by
    rw [trace_densityOf, hω, hψ1]
    exact τ.map_one
  have H1 : ∀ a ∈ F', ∀ x : Matrix Y Y ℂ,
      ‖Matrix.trace ((densityOf ω * ρ a - ρ a * densityOf ω) * x)‖ ≤ η * ‖x‖ := by
    intro a ha x
    have e : Matrix.trace ((densityOf ω * ρ a - ρ a * densityOf ω) * x)
        = τ.toLinearMap (ψ (ρ a * x) - a * ψ x)
          - τ.toLinearMap (ψ (x * ρ a) - ψ x * a) := by
      rw [sub_mul, Matrix.trace_sub, mul_assoc, mul_assoc, Matrix.trace_mul_comm (ρ a),
        mul_assoc, trace_densityOf_mul, trace_densityOf_mul, hω, hω, map_sub, map_sub,
        τ.map_mul_comm a (ψ x)]
      ring
    obtain ⟨hl, hr⟩ := hbim a (Finset.mem_union_right F ha) x
    have hsc : min (η / 2) ε * ‖x‖ ≤ η / 2 * ‖x‖ :=
      mul_le_mul_of_nonneg_right hδη (norm_nonneg x)
    rw [e, ← map_sub τ.toLinearMap]
    calc ‖τ.toLinearMap ((ψ (ρ a * x) - a * ψ x) - (ψ (x * ρ a) - ψ x * a))‖
        ≤ ‖(ψ (ρ a * x) - a * ψ x) - (ψ (x * ρ a) - ψ x * a)‖ := hτn _
      _ ≤ ‖ψ (ρ a * x) - a * ψ x‖ + ‖ψ (x * ρ a) - ψ x * a‖ := norm_sub_le _ _
      _ ≤ min (η / 2) ε * ‖x‖ + min (η / 2) ε * ‖x‖ := add_le_add hl hr
      _ ≤ η * ‖x‖ := by linarith
  have H2 : ∀ a ∈ F', ∀ b ∈ F',
      ‖Matrix.trace (densityOf ω * (ρ (a * b) - ρ a * ρ b))‖ ≤ η := by
    intro a ha b hb
    rw [trace_densityOf_mul, hω]
    calc ‖τ.toLinearMap (ψ (ρ (a * b) - ρ a * ρ b))‖
        ≤ ‖ψ (ρ (a * b) - ρ a * ρ b)‖ := hτn _
      _ ≤ min (η / 2) ε :=
          hmul a (Finset.mem_union_right F ha) b (Finset.mem_union_right F hb)
      _ ≤ η := by linarith
  obtain ⟨T, hTh, hTT, hcomm⟩ := hsq Y ρ hρ1 hρn hρs (densityOf ω) hPSD htr H1 H2
  refine ⟨Y, ρ, T, hρ1, hρcp, hTh, ?_, ?_, hcomm, ?_⟩
  · rw [hTT]
    exact htr
  · intro x hx
    show ‖τ.toLinearMap x - Matrix.trace (T * ρ x * T)‖ ≤ ε
    rw [trace_T_mul_T ω hTT, hω, norm_sub_rev, ← map_sub τ.toLinearMap]
    calc ‖τ.toLinearMap (ψ (ρ x) - x)‖ ≤ ‖ψ (ρ x) - x‖ := hτn _
      _ ≤ min (η / 2) ε := hψρ x (Finset.mem_union_left F' hx)
      _ ≤ ε := hδε
  · intro x hx y hy
    rw [trace_conjTranspose_mul_T ω hTh hTT, hω]
    calc (τ.toLinearMap (ψ (star (ρ (x * y) - ρ x * ρ y) * (ρ (x * y) - ρ x * ρ y)))).re
        ≤ ‖τ.toLinearMap (ψ (star (ρ (x * y) - ρ x * ρ y) * (ρ (x * y) - ρ x * ρ y)))‖ :=
          Complex.re_le_norm _
      _ ≤ ‖ψ (star (ρ (x * y) - ρ x * ρ y) * (ρ (x * y) - ρ x * ρ y))‖ := hτn _
      _ ≤ min (η / 2) ε :=
          hmul2 x (Finset.mem_union_left F' hx) y (Finset.mem_union_left F' hy)
      _ ≤ ε := hδε

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.hasApproxInvariantDensities_of_gap

/-- **The lane endpoint (nm-tww-12).**  The τ-free gap `NuclearDensityGapStatement` implies
`NuclearAmenable.NuclearTraceApproxDensityStatement`, the interface that nm-tww-13 consumes. -/
theorem nuclearTraceApproxDensityStatement_of_nuclearDensityGapStatement
    (h : NuclearDensityGapStatement.{u}) :
    NuclearAmenable.NuclearTraceApproxDensityStatement.{u} :=
  fun A inst _ hnuc τ ↦
    hasApproxInvariantDensities_of_gap (h.cpap A inst hnuc) (h.sqrtControl A inst)
      τ.toTracialState

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.nuclearTraceApproxDensityStatement_of_nuclearDensityGapStatement

end

end Manuscript.NonMF.TWWLanes.NuclearDensity
end GroupApproximation
