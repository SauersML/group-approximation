import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.EmbeddingConnesTraceFacts
import GroupApproximation.Manuscript.MFRecognition.TensorSynchronizationData

/-!
# Connes' trick, density side: matrix CPAP and square-root control give densities

Lane TWWSch3b1 (work order WO-TWWSch-3b-1).  This file works toward
`isAmenableTrace_of_isNuclearCStarAlgebra`, the Tikuisis--White--Winter input of
`non_mf_group_notes.tex`.
Source: Brown--Ozawa, *C⋆-algebras and finite-dimensional approximations*, Thm 6.2.7
(the step from the CPAP to approximately invariant densities).

The file was adapted, after review, from the never-wired foreign
`TWWLanes/NuclearDensity/Reduction` module, which is WIP-tainted.

Fix a tracial state `τ`, a finite `F` and `ε > 0`.

1. Square-root control gives `F'` and `η`.  Apply the CPAP at `F ∪ F'` with tolerance
   `δ = min (η/2) ε`.  This gives `ρ` and `ψ`.
2. Put `ω = τ ∘ ψ` and `h = densityOf ω`.  Then `h` is Hermitian, positive semidefinite,
   and `tr h = 1`.
3. By traciality, `tr((hρ(a) − ρ(a)h)x)` is bounded by `2δ‖x‖ ≤ η‖x‖`.  Also
   `|tr(h(ρ(ab) − ρ(a)ρ(b)))| ≤ δ ≤ η`.
4. Square-root control returns a Hermitian `T` with `T² = h` and the commutator bound.  The
   remaining clauses follow from `trace_T_mul_T`, `trace_conjTranspose_mul_T` and
   `‖τ z‖ ≤ ‖z‖`.
-/

namespace GroupApproximation.Full.TWWSchafhauser.Connes

open Matrix Quasidiagonal
open scoped Matrix.Norms.L2Operator ComplexOrder

noncomputable section

universe u

/-- **CPAP and square-root control give approximately invariant densities** (Brown--Ozawa
6.2.7, density step).  Separability of `A` and faithfulness of `τ` are not used. -/
theorem hasApproxInvariantDensities_of_gap {A : Type u} [CStarAlgebra A]
    (hcpap : IsMatrixCPAP A) (hsqrt : HasSqrtCommutatorControl A) (τ : TracialState A) :
    HasApproxInvariantDensities (fun a : A ↦ τ a) := by
  classical
  intro F ε hε
  have hτn : ∀ z : A, ‖τ.toLinearMap z‖ ≤ ‖z‖ := fun z ↦
    Manuscript.MFRecognition.TensorSynchronization.norm_tracialState_le τ z
  obtain ⟨F', η, hη, hsq⟩ := hsqrt F ε hε
  have hδ : 0 < min (η / 2) ε := lt_min (by linarith) hε
  have hδη : min (η / 2) ε ≤ η / 2 := min_le_left _ _
  have hδε : min (η / 2) ε ≤ ε := min_le_right _ _
  obtain ⟨Y, ρ, ψ, hρ1, hρcp, hρn, hρs, hψ1, hψpos, hψs, hψρ, hbim, hmul, hmul2⟩ :=
    hcpap (F ∪ F') (min (η / 2) ε) hδ
  obtain ⟨ω, hω⟩ : ∃ ω : Matrix Y Y ℂ →ₗ[ℂ] ℂ, ∀ X, ω X = τ.toLinearMap (ψ X) :=
    ⟨τ.toLinearMap ∘ₗ ψ, fun _ ↦ rfl⟩
  have hωs : ∀ M : Matrix Y Y ℂ, ω (star M) = star (ω M) := fun M ↦ by
    rw [hω, hω, hψs, apply_star_of_nonneg τ.toLinearMap τ.map_star_mul_self_nonneg (ψ M),
      starRingEnd_apply]
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
    rw [e, ← map_sub τ.toLinearMap]
    calc ‖τ.toLinearMap ((ψ (ρ a * x) - a * ψ x) - (ψ (x * ρ a) - ψ x * a))‖
        ≤ ‖(ψ (ρ a * x) - a * ψ x) - (ψ (x * ρ a) - ψ x * a)‖ := hτn _
      _ ≤ ‖ψ (ρ a * x) - a * ψ x‖ + ‖ψ (x * ρ a) - ψ x * a‖ := norm_sub_le _ _
      _ ≤ min (η / 2) ε * ‖x‖ + min (η / 2) ε * ‖x‖ := add_le_add hl hr
      _ ≤ η / 2 * ‖x‖ + η / 2 * ‖x‖ := by
          have hsc : min (η / 2) ε * ‖x‖ ≤ η / 2 * ‖x‖ :=
            mul_le_mul_of_nonneg_right hδη (norm_nonneg x)
          linarith
      _ = η * ‖x‖ := by ring
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

end

end GroupApproximation.Full.TWWSchafhauser.Connes
