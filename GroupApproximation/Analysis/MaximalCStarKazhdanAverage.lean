import GroupApproximation.Analysis.MaximalGroupCStar
import GroupApproximation.Analysis.ProperIsometryFromCompression

/-!
# Unitary averages in the maximal group C-star algebra

The averaging element of a finite symmetric set of group elements, inside
the universe-relative maximal group C-star algebra: self-adjoint, of norm
at most one, and conjugated by a canonical unitary to the average of the
conjugated set.

These are the algebraic bricks of the strict-Kazhdan-compression program
of `notes/FORMALIZATION_DIRECTIVES_2026-08-15.md` §1: the Kazhdan
projection of a compressed subgroup will arise as the limit of the powers
of this average, and the proper-isometry machinery of
`ProperIsometryFromCompression` consumes the resulting projection data.
The spectral-gap convergence itself is the separate analytic brick and is
not claimed here.
-/

namespace GroupApproximation

open scoped ComplexConjugate

noncomputable section

universe u

variable (G : Type u) [Group G]

/-- The maximal group C-star algebra is nontrivial: the reduced coordinate
separates `1` from `0`. -/
instance maximalGroupCStar_nontrivial : Nontrivial (MaximalGroupCStar G) := by
  refine ⟨1, 0, fun h => ?_⟩
  have := congrArg (maximalGroupCStarEval G
    (CStarUnitaryRepresentation.reduced G)) h
  rw [map_one, map_zero] at this
  exact one_ne_zero this

theorem maximalGroupCStarGenerator_mul (g h : G) :
    maximalGroupCStarGenerator G g * maximalGroupCStarGenerator G h
      = maximalGroupCStarGenerator G (g * h) :=
  (congrArg (fun u : unitary (MaximalGroupCStar G) =>
    (u : MaximalGroupCStar G))
    (map_mul (maximalGroupCStarUnitaryHom G) g h)).symm

theorem star_maximalGroupCStarGenerator (g : G) :
    star (maximalGroupCStarGenerator G g)
      = maximalGroupCStarGenerator G g⁻¹ := by
  apply Subtype.ext
  apply lp.ext
  funext R
  show star ((R.hom g : R.carrier)) = (R.hom g⁻¹ : R.carrier)
  rw [map_inv]
  rfl

theorem norm_maximalGroupCStarGenerator (g : G) :
    ‖maximalGroupCStarGenerator G g‖ = 1 :=
  CStarRing.norm_of_mem_unitary (maximalGroupCStarUnitary G g).property

/-- The unitary average of a finite set of group elements. -/
def maximalCStarAverage (S : Finset G) : MaximalGroupCStar G :=
  ((S.card : ℂ))⁻¹ • ∑ g ∈ S, maximalGroupCStarGenerator G g

theorem maximalCStarEval_average (R : CStarUnitaryRepresentation G)
    (S : Finset G) :
    maximalGroupCStarEval G R (maximalCStarAverage G S)
      = ((S.card : ℂ))⁻¹ • ∑ g ∈ S, (R.hom g : R.carrier) := by
  unfold maximalCStarAverage
  rw [map_smul, map_sum]
  simp only [maximalGroupCStarEval_generator]

/-- The average of a symmetric set is self-adjoint. -/
theorem isSelfAdjoint_maximalCStarAverage {S : Finset G}
    (hS : ∀ g ∈ S, g⁻¹ ∈ S) :
    IsSelfAdjoint (maximalCStarAverage G S) := by
  unfold maximalCStarAverage
  have hconj : star ((S.card : ℂ))⁻¹ = ((S.card : ℂ))⁻¹ := by
    rw [star_inv₀, star_natCast]
  rw [IsSelfAdjoint, star_smul, star_sum, hconj]
  congr 1
  rw [show (∑ g ∈ S, star (maximalGroupCStarGenerator G g))
      = ∑ g ∈ S, maximalGroupCStarGenerator G g⁻¹ from
    Finset.sum_congr rfl fun g _ => star_maximalGroupCStarGenerator G g]
  refine Finset.sum_nbij' (fun g => g⁻¹) (fun g => g⁻¹) ?_ ?_ ?_ ?_ ?_
  · intro g hg; exact hS g hg
  · intro g hg; exact hS g hg
  · intro g _; exact inv_inv g
  · intro g _; exact inv_inv g
  · intro g _; rfl

/-- The average of a nonempty set has norm at most one. -/
theorem norm_maximalCStarAverage_le {S : Finset G} (hS : S.Nonempty) :
    ‖maximalCStarAverage G S‖ ≤ 1 := by
  unfold maximalCStarAverage
  have hcard : (0 : ℝ) < S.card := by
    exact_mod_cast Finset.card_pos.mpr hS
  calc ‖((S.card : ℂ))⁻¹ • ∑ g ∈ S, maximalGroupCStarGenerator G g‖
      = ‖((S.card : ℂ))⁻¹‖ * ‖∑ g ∈ S, maximalGroupCStarGenerator G g‖ :=
        norm_smul _ _
    _ ≤ ‖((S.card : ℂ))⁻¹‖ * ∑ g ∈ S, ‖maximalGroupCStarGenerator G g‖ := by
        apply mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
    _ = ((S.card : ℝ))⁻¹ * S.card := by
        rw [norm_inv]
        congr 1
        · congr 1
          exact Complex.norm_natCast _
        · rw [Finset.sum_congr rfl fun g _ =>
            norm_maximalGroupCStarGenerator G g]
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ = 1 := inv_mul_cancel₀ (ne_of_gt hcard)

/-- Conjugating the average by a canonical unitary gives the average of the
conjugated set. -/
theorem generator_mul_average_mul_star [DecidableEq G] (t : G) (S : Finset G) :
    maximalGroupCStarGenerator G t * maximalCStarAverage G S *
        star (maximalGroupCStarGenerator G t)
      = maximalCStarAverage G (S.image fun g => t * g * t⁻¹) := by
  have hinj : Function.Injective fun g : G => t * g * t⁻¹ := by
    intro a b hab
    simpa using hab
  unfold maximalCStarAverage
  rw [star_maximalGroupCStarGenerator,
    Finset.card_image_of_injective S hinj]
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_image
    (fun a _ b _ hab => hinj hab)]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [maximalGroupCStarGenerator_mul, maximalGroupCStarGenerator_mul]

end

end GroupApproximation
