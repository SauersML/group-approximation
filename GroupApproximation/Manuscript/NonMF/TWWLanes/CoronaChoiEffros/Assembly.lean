import GroupApproximation.Manuscript.NonMF.TWWLanes.CoronaChoiEffros.ApproximateLift
import GroupApproximation.Meta.AxiomGuard

/-!
# Choi--Effros into matrix-sequence coronas: assembling coordinates

Lane `nm-tww-08`, step 2, which is bookkeeping.

* `assembledSeq`. A family of contractive coordinate maps `φ n : A → M_{X n}` assembles
  into a bounded sequence `(φ n a)_n` with norm at most `‖a‖`. It is linear in `a`
  (`assembledLift`).
* `quotient_assembledSeq_eq_of_denseRange`. The corona image of the assembled sequence is
  a contraction of `a`, and so is `Φ`. If the two agree on a dense sequence, they agree
  everywhere (`DenseRange.equalizer`).
* `diagonalIndex N n` is the largest `m ≤ n` with `N m + m ≤ n` (`Nat.findGreatest`). It
  tends to infinity. Once `N 0 ≤ n`, its threshold `N (diagonalIndex N n)` is at most `n`.
  This is the diagonal selection used in `DiagonalLift`.
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
local instance boundedMatrixSequenceCStarAlgebraForCoronaChoiEffrosAssembly :
    CStarAlgebra (BoundedMatrixSequence X) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CoronaChoiEffros.boundedMatrixSequenceCStarAlgebraForCoronaChoiEffrosAssembly

/-- The bounded sequence `(φ n a)_n` of contractive coordinates. -/
def assembledSeq (φ : ∀ n, A →ₗ[ℂ] Matrix (X n) (X n) ℂ)
    (hφ : ∀ n a, ‖φ n a‖ ≤ ‖a‖) (a : A) : BoundedMatrixSequence X :=
  ⟨fun n ↦ φ n a, memℓp_infty ⟨‖a‖, by rintro _ ⟨n, rfl⟩; exact hφ n a⟩⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CoronaChoiEffros.assembledSeq

theorem assembledSeq_apply (φ : ∀ n, A →ₗ[ℂ] Matrix (X n) (X n) ℂ)
    (hφ : ∀ n a, ‖φ n a‖ ≤ ‖a‖) (a : A) (n : ℕ) :
    assembledSeq φ hφ a n = φ n a := rfl

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CoronaChoiEffros.assembledSeq_apply

theorem norm_assembledSeq_le (φ : ∀ n, A →ₗ[ℂ] Matrix (X n) (X n) ℂ)
    (hφ : ∀ n a, ‖φ n a‖ ≤ ‖a‖) (a : A) : ‖assembledSeq φ hφ a‖ ≤ ‖a‖ :=
  lp.norm_le_of_forall_le (norm_nonneg a) fun n ↦ hφ n a

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CoronaChoiEffros.norm_assembledSeq_le

/-- The assembled sequence as a linear map. -/
def assembledLift (φ : ∀ n, A →ₗ[ℂ] Matrix (X n) (X n) ℂ)
    (hφ : ∀ n a, ‖φ n a‖ ≤ ‖a‖) : A →ₗ[ℂ] BoundedMatrixSequence X where
  toFun := assembledSeq φ hφ
  map_add' x y := by
    apply lp.ext
    funext n
    change φ n (x + y) = φ n x + φ n y
    exact map_add (φ n) x y
  map_smul' c x := by
    apply lp.ext
    funext n
    change φ n (c • x) = c • φ n x
    exact map_smul (φ n) c x

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CoronaChoiEffros.assembledLift

/-- **Density extension.** If the corona image of the assembled sequence agrees with the
`⋆`-homomorphism `Φ` along a dense sequence, it agrees with `Φ` everywhere. -/
theorem quotient_assembledSeq_eq_of_denseRange (Φ : A →⋆ₐ[ℂ] NormMatrixCStarCorona X)
    (φ : ∀ n, A →ₗ[ℂ] Matrix (X n) (X n) ℂ) (hφ : ∀ n a, ‖φ n a‖ ≤ ‖a‖)
    {u : ℕ → A} (hu : DenseRange u)
    (hi : ∀ i, normMatrixCStarCoronaQuotient X (assembledSeq φ hφ (u i)) = Φ (u i))
    (a : A) : normMatrixCStarCoronaQuotient X (assembledSeq φ hφ a) = Φ a := by
  have hq : Continuous (normMatrixCStarCoronaQuotient X) :=
    AddMonoidHomClass.continuous_of_bound (normMatrixCStarCoronaQuotient X) 1 fun x ↦ by
      rw [one_mul]
      exact NonUnitalStarAlgHom.norm_apply_le (normMatrixCStarCoronaQuotient X) x
  have hΨ : Continuous (assembledLift φ hφ) :=
    AddMonoidHomClass.continuous_of_bound (assembledLift φ hφ) 1 fun x ↦ by
      rw [one_mul]
      exact norm_assembledSeq_le φ hφ x
  have hΦ : Continuous Φ :=
    AddMonoidHomClass.continuous_of_bound Φ 1 fun x ↦ by
      rw [one_mul]
      exact NonUnitalStarAlgHom.norm_apply_le Φ x
  exact congrFun (hu.equalizer (hq.comp hΨ) hΦ (funext hi)) a

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CoronaChoiEffros.quotient_assembledSeq_eq_of_denseRange

/-- The diagonal index: the largest `m ≤ n` with `N m + m ≤ n`. -/
def diagonalIndex (N : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.findGreatest (fun m ↦ N m + m ≤ n) n

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CoronaChoiEffros.diagonalIndex

theorem le_diagonalIndex {N : ℕ → ℕ} {K n : ℕ} (h : N K + K ≤ n) :
    K ≤ diagonalIndex N n := by
  unfold diagonalIndex
  exact Nat.le_findGreatest (by omega) h

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CoronaChoiEffros.le_diagonalIndex

theorem diagonalIndex_spec {N : ℕ → ℕ} {n : ℕ} (h : N 0 ≤ n) :
    N (diagonalIndex N n) ≤ n := by
  have hspec : N (diagonalIndex N n) + diagonalIndex N n ≤ n :=
    Nat.findGreatest_spec (P := fun m ↦ N m + m ≤ n) (Nat.zero_le n)
      (show N 0 + 0 ≤ n by omega)
  omega

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CoronaChoiEffros.diagonalIndex_spec

theorem tendsto_diagonalIndex (N : ℕ → ℕ) : Tendsto (diagonalIndex N) atTop atTop :=
  tendsto_atTop_atTop.2 fun K ↦ ⟨N K + K, fun _n hn ↦ le_diagonalIndex hn⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CoronaChoiEffros.tendsto_diagonalIndex

end

end CoronaChoiEffros
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
