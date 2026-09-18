import GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.ChoiEffrosCauchySchwarz
import GroupApproximation.Sofic.KazhdanCornerModel
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import GroupApproximation.Meta.AxiomGuard

/-!
# Lane nm-tww-28c, part 1: positivity and contractivity of Kraus-column maps

For `G : Y → A`, the map `ψ_G(N) = ⟨G, N G⟩` is positive: a PSD `P = Q⋆Q` gives
`ψ_G(P) = ⟨Q G, Q G⟩ ≥ 0`.  When `⟨G, G⟩ = 1`, the map `ψ_G` is also contractive.  The
matrix `‖M‖² · 1 − M⋆M` is PSD, so `ψ_G(M⋆M) ≤ ‖M‖² · 1`.  Then Cauchy--Schwarz for the
column pairing gives
`‖ψ_G(M)‖ = ‖⟨G, M G⟩‖ ≤ √‖⟨G, G⟩‖ · √‖ψ_G(M⋆M)‖ ≤ ‖M‖`.

The order on `A` is the spectral order, and it is supplied locally.
-/

namespace GroupApproximation
namespace Manuscript.NonMF.TWWLanes.NuclearDensity

open Matrix Quasidiagonal
open scoped Matrix.Norms.L2Operator ComplexOrder

noncomputable section

universe u

variable {A : Type u} [CStarAlgebra A]

/-- `x⋆ x = ∑ |x i|²`. -/
theorem choiEffrosUcp_star_dotProduct_self {Y : Type} [Fintype Y] (x : Y → ℂ) :
    star x ⬝ᵥ x = ((∑ i, Complex.normSq (x i) : ℝ) : ℂ) := by
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  exact Complex.normSq_eq_conj_mul_self.symm

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.choiEffrosUcp_star_dotProduct_self

/-- `x⋆ (Mᴴ M) x = ∑ |(M x) i|²`. -/
theorem choiEffrosUcp_star_dotProduct_gram {Y : Type} [Fintype Y] (M : Matrix Y Y ℂ)
    (x : Y → ℂ) :
    star x ⬝ᵥ ((Mᴴ * M) *ᵥ x) = ((∑ i, Complex.normSq ((M *ᵥ x) i) : ℝ) : ℂ) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star,
    choiEffrosUcp_star_dotProduct_self]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.choiEffrosUcp_star_dotProduct_gram

/-- `‖M‖² · 1 − M⋆M` is positive semidefinite, for the operator norm. -/
theorem choiEffrosUcp_posSemidef_sub {Y : Type} [Fintype Y] [DecidableEq Y]
    (M : Matrix Y Y ℂ) :
    (((‖M‖ ^ 2 : ℝ) : ℂ) • (1 : Matrix Y Y ℂ) - star M * M).PosSemidef := by
  rw [Matrix.star_eq_conjTranspose]
  have hc : IsSelfAdjoint ((‖M‖ ^ 2 : ℝ) : ℂ) :=
    isSelfAdjoint_iff.mpr (by rw [← starRingEnd_apply, Complex.conj_ofReal])
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    ((Matrix.isHermitian_one.smul hc).sub (Matrix.isHermitian_conjTranspose_mul_self M))
    fun x ↦ ?_
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub, dotProduct_smul,
    choiEffrosUcp_star_dotProduct_self x, choiEffrosUcp_star_dotProduct_gram M x, smul_eq_mul,
    ← Complex.ofReal_mul, ← Complex.ofReal_sub]
  exact Complex.zero_le_real.mpr
    (sub_nonneg.mpr (KazhdanCornerMatrices.sum_normSq_mulVec_le_general M x))

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.choiEffrosUcp_posSemidef_sub

/-- `⟨u, u⟩ ≥ 0` for any order making `A` star-ordered. -/
theorem choiEffrosUcp_pair_self_nonneg [PartialOrder A] [StarOrderedRing A] {Y : Type}
    [Fintype Y] (u : Y → A) : 0 ≤ choiEffrosPair u u := by
  show 0 ≤ ∑ y, star (u y) * u y
  exact Finset.sum_nonneg fun y _ ↦ star_mul_self_nonneg (u y)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.choiEffrosUcp_pair_self_nonneg

open scoped MatrixOrder in
/-- **Positivity of `ψ_G`.**  A PSD matrix is sent to a positive element. -/
theorem choiEffrosUcp_krausMap_nonneg [PartialOrder A] [StarOrderedRing A] {Y : Type}
    [Fintype Y] [DecidableEq Y] (G : Y → A) {P : Matrix Y Y ℂ} (hP : P.PosSemidef) :
    0 ≤ choiEffrosKrausMap G P := by
  obtain ⟨Q, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hP.nonneg
  rw [← choiEffros_pair_act_act G (star Q) Q, star_star]
  exact choiEffrosUcp_pair_self_nonneg _

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.choiEffrosUcp_krausMap_nonneg

/-- **Contractivity of `ψ_G`** when `⟨G, G⟩ = 1`. -/
theorem choiEffrosUcp_norm_krausMap_le {Y : Type} [Fintype Y] [DecidableEq Y] (G : Y → A)
    (hG : choiEffrosPair G G = 1) (M : Matrix Y Y ℂ) : ‖choiEffrosKrausMap G M‖ ≤ ‖M‖ := by
  letI : PartialOrder A := CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  obtain _ | _ := subsingleton_or_nontrivial A
  · rw [Subsingleton.elim (choiEffrosKrausMap G M) 0, norm_zero]
    exact norm_nonneg M
  have hηη : choiEffrosPair (choiEffrosAct M G) (choiEffrosAct M G) =
      choiEffrosKrausMap G (star M * M) := by
    have h := choiEffros_pair_act_act G (star M) M
    rwa [star_star] at h
  have hpos : 0 ≤ choiEffrosKrausMap G (star M * M) := by
    rw [← hηη]
    exact choiEffrosUcp_pair_self_nonneg _
  have hle : choiEffrosKrausMap G (star M * M) ≤ ((‖M‖ ^ 2 : ℝ) : ℂ) • (1 : A) := by
    have h := choiEffrosUcp_krausMap_nonneg G (choiEffrosUcp_posSemidef_sub M)
    rwa [map_sub, map_smul, choiEffros_krausMap_one, hG, sub_nonneg] at h
  have hnorm : ‖choiEffrosKrausMap G (star M * M)‖ ≤ ‖M‖ ^ 2 :=
    (CStarAlgebra.norm_le_norm_of_nonneg_of_le hpos hle).trans_eq (by
      rw [norm_smul, norm_one, mul_one, Complex.norm_of_nonneg (sq_nonneg _)])
  have hGη : choiEffrosPair G (choiEffrosAct M G) = choiEffrosKrausMap G M := rfl
  have hcs := choiEffros_norm_pair_le G (choiEffrosAct M G)
  rw [hGη, hG, hηη, norm_one, Real.sqrt_one, one_mul] at hcs
  exact hcs.trans ((Real.sqrt_le_sqrt hnorm).trans_eq (Real.sqrt_sq (norm_nonneg M)))

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.choiEffrosUcp_norm_krausMap_le

end

end Manuscript.NonMF.TWWLanes.NuclearDensity
end GroupApproximation
