import GroupApproximation.Manuscript.NonMF.TWWLanes.CoronaChoiEffros.Assembly
import GroupApproximation.Analysis.BlackadarKirchbergCoordinateSelection
import GroupApproximation.Meta.AxiomGuard

/-!
# Choi--Effros into matrix-sequence coronas: exact CPC coordinates

Lane `nm-tww-08`, step 3. Let `A` be separable and nuclear, and let `Φ : A → Q(X)` be a
unital `⋆`-homomorphism. Then there are completely positive contractions
`φ n : A → M_{X n}` whose assembled sequence represents `Φ` exactly.

Proof route (diagonal selection).
* Fix a dense sequence `u`. For each `m`, `exists_cpc_approximateLift` gives a CPC
  `ψ m : A → ∏ M_{X n}` with `‖q (ψ m (u i)) - Φ (u i)‖ ≤ 1/(m+1)` for `i ≤ m`.
* Choose representatives `r i` of `Φ (u i)`. The coordinates of `ψ m (u i) - r i`
  are eventually `< 2/(m+1)`, by `eventually_coord_norm_lt_of_corona_norm_lt`.
  Choose a threshold `N m` that works for all `i ≤ m`.
* Put `φ n = ev_n ∘ ψ (diagonalIndex N n)`. Each coordinate is CPC. For fixed `i` and
  large `n`, we have `i ≤ diagonalIndex N n` and `N (diagonalIndex N n) ≤ n`. So
  `‖φ n (u i) - r i n‖ < 2/(diagonalIndex N n + 1)`, which tends to `0`. Hence the
  assembled sequence and `r i` have the same corona image `Φ (u i)`.
* `quotient_assembledSeq_eq_of_denseRange` extends the equality from `u` to `A`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace CoronaChoiEffros

open GroupApproximation.CStarExactness
open Filter
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u v

variable {X : ℕ → Type v} [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)]
  [∀ n, Nonempty (X n)] {A : Type u} [CStarAlgebra A]

/-- Bounded matrix sequences are C-star algebras (the same instance as in the corpus). -/
local instance boundedMatrixSequenceCStarAlgebraForCoronaChoiEffrosDiagonal :
    CStarAlgebra (BoundedMatrixSequence X) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CoronaChoiEffros.boundedMatrixSequenceCStarAlgebraForCoronaChoiEffrosDiagonal

/-- Matrix blocks at the scoped operator norm are C-star algebras. -/
local instance matrixBlockCStarAlgebraForCoronaChoiEffrosDiagonal
    (Z : Type*) [Fintype Z] [DecidableEq Z] [Nonempty Z] :
    CStarAlgebra (Matrix Z Z ℂ) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CoronaChoiEffros.matrixBlockCStarAlgebraForCoronaChoiEffrosDiagonal

/-- The diagonal coordinates `φ n = ev_n ∘ ψ (diagonalIndex N n)`. -/
def diagonalCoordinates (ψ : ℕ → A →ₗ[ℂ] BoundedMatrixSequence X) (N : ℕ → ℕ) (n : ℕ) :
    A →ₗ[ℂ] Matrix (X n) (X n) ℂ :=
  BlackadarKirchberg.coordinateEvaluation X n ∘ₗ ψ (diagonalIndex N n)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CoronaChoiEffros.diagonalCoordinates

theorem diagonalCoordinates_apply (ψ : ℕ → A →ₗ[ℂ] BoundedMatrixSequence X) (N : ℕ → ℕ)
    (n : ℕ) (a : A) : diagonalCoordinates ψ N n a = ψ (diagonalIndex N n) a n := rfl

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CoronaChoiEffros.diagonalCoordinates_apply

/-- **Exact CPC coordinates.** A unital `⋆`-homomorphism from a separable nuclear
C-star algebra into the matrix corona has completely positive contractive matrix
coordinates whose assembled sequence represents it. -/
theorem exists_cpc_coordinates_lift [TopologicalSpace.SeparableSpace A]
    (hnuc : IsNuclearCStarAlgebra A) (Φ : A →⋆ₐ[ℂ] NormMatrixCStarCorona X) :
    ∃ (φ : ∀ n, A →ₗ[ℂ] Matrix (X n) (X n) ℂ) (hφ : ∀ n a, ‖φ n a‖ ≤ ‖a‖),
      (∀ n, IsCompletelyPositive (φ n)) ∧
        ∀ a, normMatrixCStarCoronaQuotient X (assembledSeq φ hφ a) = Φ a := by
  classical
  haveI : Nonempty A := ⟨0⟩
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq A
  have hstep : ∀ m : ℕ, ∃ ψ : A →ₗ[ℂ] BoundedMatrixSequence X,
      IsCompletelyPositive ψ ∧ (∀ a, ‖ψ a‖ ≤ ‖a‖) ∧ ∀ i, i ≤ m →
        ‖normMatrixCStarCoronaMk X (ψ (u i)) - Φ (u i)‖ ≤ 1 / ((m : ℝ) + 1) := by
    intro m
    obtain ⟨ψ, hψCP, hψC, hψS⟩ :=
      exists_cpc_approximateLift hnuc Φ ((Finset.range (m + 1)).image u)
        (δ := 1 / ((m : ℝ) + 1)) (by positivity)
    refine ⟨ψ, hψCP, hψC, fun i hi ↦ ?_⟩
    rw [← quotient_apply_eq_mk]
    exact hψS (u i) (Finset.mem_image_of_mem u (Finset.mem_range.2 (by omega)))
  choose ψ hψCP hψC hψS using hstep
  choose r hr using fun i ↦ normMatrixCStarCoronaMk_surjective X (Φ (u i))
  have hev : ∀ m : ℕ, ∀ᶠ n in atTop, ∀ i ∈ Finset.range (m + 1),
      ‖(ψ m (u i) - r i) n‖ < 2 * (1 / ((m : ℝ) + 1)) := by
    intro m
    refine (Filter.eventually_all_finset (Finset.range (m + 1))).2 fun i hi ↦ ?_
    show ∀ᶠ n in atTop, ‖(ψ m (u i) - r i) n‖ < 2 * (1 / ((m : ℝ) + 1))
    refine BlackadarKirchberg.eventually_coord_norm_lt_of_corona_norm_lt _ ?_
    have hmk : normMatrixCStarCoronaMk X (ψ m (u i) - r i) =
        normMatrixCStarCoronaMk X (ψ m (u i)) - Φ (u i) := by
      rw [map_sub, hr i]
    have hS : ‖normMatrixCStarCoronaMk X (ψ m (u i)) - Φ (u i)‖ ≤ 1 / ((m : ℝ) + 1) :=
      hψS m i (Nat.le_of_lt_succ (Finset.mem_range.1 hi))
    have hpos : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    rw [hmk]
    linarith
  choose N hN using fun m ↦ Filter.eventually_atTop.1 (hev m)
  have hφ : ∀ n a, ‖diagonalCoordinates ψ N n a‖ ≤ ‖a‖ := fun n a ↦ by
    rw [diagonalCoordinates_apply]
    exact (boundedMatrixSequence_coord_norm_le X _ n).trans (hψC _ a)
  have hφCP : ∀ n, IsCompletelyPositive (diagonalCoordinates ψ N n) := fun n ↦
    (BlackadarKirchberg.isCompletelyPositive_coordinateEvaluation X n).comp (hψCP _)
  have hlim : Tendsto (fun n ↦ 2 * (1 / ((diagonalIndex N n : ℝ) + 1))) atTop (nhds 0) := by
    have h : Tendsto (fun n ↦ 2 * (1 / ((diagonalIndex N n : ℝ) + 1))) atTop
        (nhds (2 * 0)) :=
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        (tendsto_diagonalIndex N)).const_mul 2
    rwa [mul_zero] at h
  have hnull : ∀ i, normMatrixCStarCoronaQuotient X
      (assembledSeq (diagonalCoordinates ψ N) hφ (u i)) = Φ (u i) := by
    intro i
    have hzero : normMatrixCStarCoronaMk X
        (assembledSeq (diagonalCoordinates ψ N) hφ (u i) - r i) = 0 := by
      rw [normMatrixCStarCoronaMk_eq_zero_iff, IsNullMatrixSequence, Nat.cofinite_eq_atTop]
      refine squeeze_zero' (Filter.Eventually.of_forall fun n ↦ norm_nonneg _) ?_ hlim
      rw [Filter.eventually_atTop]
      refine ⟨N 0 + (N i + i), fun n hn ↦ ?_⟩
      have hK : i ≤ diagonalIndex N n := le_diagonalIndex (by omega)
      have hMN : N (diagonalIndex N n) ≤ n := diagonalIndex_spec (by omega)
      have h := hN _ n hMN i (Finset.mem_range.2 (by omega))
      rw [lp.coeFn_sub, Pi.sub_apply] at h ⊢
      rw [assembledSeq_apply, diagonalCoordinates_apply]
      exact le_of_lt h
    rw [map_sub, hr i, sub_eq_zero] at hzero
    rw [quotient_apply_eq_mk]
    exact hzero
  exact ⟨diagonalCoordinates ψ N, hφ, hφCP,
    quotient_assembledSeq_eq_of_denseRange Φ _ hφ hu hnull⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CoronaChoiEffros.exists_cpc_coordinates_lift

end

end CoronaChoiEffros
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
