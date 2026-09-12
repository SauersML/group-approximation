import GroupApproximation.Analysis.ShulmanFillNormingDoubledData
import GroupApproximation.Analysis.StarStrongMatrixSequencesAlgebra

/-!
# The flip is a unitary of the doubled `𝒟`

This is the supplier of the four hypotheses that
`Analysis/ShulmanFillNormingConjugationLift.conjugate` places on its
conjugating unitary.  The unitary is the constant sequence at the flip
`((0,1),(1,0))` of `M₂` over the models:

* it is a unitary of each `M₂(A n)` — `star_flip2` and `flip2_mul_flip2` of
  `Analysis/ShulmanFillSymmetricDoubleFlip` — so the two identities hold
  coordinatewise, and its norm is `1` by the C-star identity;
* it lies in the doubled `𝒟` because its image under `ι'` converges
  `*`-strongly: entrywise `ι n (1) → 1` off the diagonal and `0 → 0` on it, so
  the block operators converge to the flip of `B(H ⊕ H)`.  The `*`-strong
  clause is free here, because the flip is self-adjoint and so are its images.

With this, `conjugate` turns one asymptotic lift of the doubled `𝒟` into the
second leg of Shulman's Theorem 10, and
`ShulmanFill.conjugate_toFun_eq_of_commute` makes the two legs agree on `C`
exactly, since the flip commutes with `diag(x, x)`.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology

noncomputable section

section Flip

/-- A unitary of a C-star algebra has norm one; in particular the flip does. -/
theorem norm_flip2_le_one {D : Type} [CStarAlgebra D]
    [Nontrivial (CStarMatrix (Fin 2) (Fin 2) D)] :
    ‖(flip2 : CStarMatrix (Fin 2) (Fin 2) D)‖ ≤ 1 := by
  have h1 : ‖(flip2 : CStarMatrix (Fin 2) (Fin 2) D)‖ *
      ‖(flip2 : CStarMatrix (Fin 2) (Fin 2) D)‖ = 1 := by
    rw [← CStarRing.norm_star_mul_self, star_flip2, flip2_mul_flip2, norm_one]
  nlinarith [norm_nonneg (flip2 : CStarMatrix (Fin 2) (Fin 2) D)]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
variable {A : ℕ → Type} [∀ n, CStarAlgebra (A n)]
variable (ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H))

/-- The entrywise limits of the flip's image: `ι n (1) → 1` off the diagonal
and `0 → 0` on it. -/
theorem tendsto_flip_entry (hone : ∀ v : H,
    Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v)) (i j : Fin 2) (x : H) :
    Tendsto (fun n ↦ ((CStarMatrix.mapₙₐ (ι n))
        (flip2 : DoubledModel A n) i j) x) atTop
      (𝓝 (((flip2 : CStarMatrix (Fin 2) (Fin 2) (H →L[ℂ] H)) i j) x)) := by
  by_cases hij : i = j
  · subst hij
    have hL : ∀ n : ℕ, ((CStarMatrix.mapₙₐ (ι n))
        (flip2 : DoubledModel A n) i i) x = 0 := by
      intro n
      rw [mapₙₐ_entry, flip2_apply_self, map_zero,
        _root_.zero_apply]
    have hR : ((flip2 : CStarMatrix (Fin 2) (Fin 2) (H →L[ℂ] H)) i i) x = 0 := by
      rw [flip2_apply_self, _root_.zero_apply]
    simp only [hL, hR]
    exact tendsto_const_nhds
  · have hL : ∀ n : ℕ, ((CStarMatrix.mapₙₐ (ι n))
        (flip2 : DoubledModel A n) i j) x = ι n (1 : A n) x := by
      intro n
      rw [mapₙₐ_entry, flip2_apply_ne hij]
    have hR : ((flip2 : CStarMatrix (Fin 2) (Fin 2) (H →L[ℂ] H)) i j) x = x := by
      rw [flip2_apply_ne hij, _root_.one_apply_eq_self]
    simp only [hL, hR]
    exact hone x

/-! ## The flip as a member of `𝒟`

Everything below needs the doubled models to be C-star algebras in their own
right, which is where the positivity order and nontriviality enter. -/

variable [∀ n, PartialOrder (A n)] [∀ n, StarOrderedRing (A n)]
variable [∀ n, Nontrivial (CStarMatrix (Fin 2) (Fin 2) (A n))]

/-- The constant sequence at the flip, as a bounded sequence of doubled
models. -/
def doubledFlipSeq :
    StarStrong.BoundedStarSequence (fun n ↦ DoubledModel A n) :=
  ⟨fun _ ↦ flip2, memℓp_infty ⟨1, by
    rintro _ ⟨n, rfl⟩
    exact norm_flip2_le_one⟩⟩

@[simp] theorem doubledFlipSeq_apply (n : ℕ) :
    (doubledFlipSeq (A := A)) n = flip2 := rfl

theorem doubledFlipSeq_star_mul_self :
    star (doubledFlipSeq (A := A)) * doubledFlipSeq = 1 := by
  apply lp.ext
  funext n
  show star (flip2 : DoubledModel A n) * flip2 = 1
  rw [star_flip2, flip2_mul_flip2]

theorem doubledFlipSeq_mul_star_self :
    (doubledFlipSeq (A := A)) * star doubledFlipSeq = 1 := by
  apply lp.ext
  funext n
  show (flip2 : DoubledModel A n) * star flip2 = 1
  rw [star_flip2, flip2_mul_flip2]

theorem norm_doubledFlipSeq_le_one : ‖doubledFlipSeq (A := A)‖ ≤ 1 := by
  rw [lp.norm_eq_ciSup]
  exact ciSup_le fun _ ↦ norm_flip2_le_one

/-- **The flip lies in the doubled `𝒟`.**  Its images converge `*`-strongly to
the flip of `B(H ⊕ H)`; the adjoint clause is the same statement, because the
flip and all its images are self-adjoint. -/
theorem doubledFlipSeq_mem (hone : ∀ v : H,
    Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v)) :
    doubledFlipSeq (A := A) ∈
      StarStrong.starStrongSubalgebra (doubledIota ι) (doubled_norm_le ι)
        (doubled_hone ι hone) := by
  refine ⟨hBlockOp (flip2 : CStarMatrix (Fin 2) (Fin 2) (H →L[ℂ] H)), ?_, ?_⟩
  · intro v
    exact tendsto_hBlockOp_of_coord (tendsto_flip_entry ι hone) v
  · intro v
    have hstarL : ∀ n : ℕ,
        star (doubledIota ι n ((doubledFlipSeq (A := A)) n)) =
          doubledIota ι n ((doubledFlipSeq (A := A)) n) := by
      intro n
      show star (doubledIota ι n (flip2 : DoubledModel A n)) = _
      rw [← map_star, star_flip2]
      rfl
    have hstarR : star (hBlockOp
        (flip2 : CStarMatrix (Fin 2) (Fin 2) (H →L[ℂ] H))) =
          hBlockOp (flip2 : CStarMatrix (Fin 2) (Fin 2) (H →L[ℂ] H)) := by
      rw [← hBlockOp_star, star_flip2]
    simp only [hstarL, hstarR]
    exact tendsto_hBlockOp_of_coord (tendsto_flip_entry ι hone) v

end Flip

end

end ShulmanFill
end GroupApproximation
