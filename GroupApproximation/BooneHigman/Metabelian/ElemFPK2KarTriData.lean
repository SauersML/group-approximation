import GroupApproximation.BooneHigman.Metabelian.ElemFPK2KarTriCol
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2KarTriClose
import GroupApproximation.Meta.AxiomGuard

/-!
# A root times a rank-one datum is again a rank-one datum (two cases)

Lane `bh-met-93k`, data module.  Let `(y₂, α, ρ)` be a rank-one datum (`ElemFPK2KarTriClose`)
with `ρ ⬝ᵥ α = 0`, over a commutative ring with no zero divisors.

* `k2KarTri_rowCase`: if `α` is supported on `{i}`, then `(x_ij(b) y₂, e_i(1), b e_j + α_i ρ)`
  is a rank-one datum.  Both commutators are rewritten as `⁅x_{i,N}(1), padRow _⁆`.
* `k2KarTri_colCase`: if `ρ` is supported on `{j}`, then `(x_ij(b) y₂, ρ_j α + e_i(b), e_j(1))`
  is a rank-one datum.  Both commutators are rewritten as `⁅padCol _, x_{N,j}(1)⁆`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral
open scoped Matrix commutatorElement

section KarTriDataRing

variable {R : Type*} [Ring R] {n : ℕ}

/-- `stab x_ij(b) = ⁅padCol e_i(b), padRow e_j(1)⁆`. -/
theorem k2KarTri_stab_x (i j : Fin n) (hij : i ≠ j) (b : R) :
    stab n R (x i j hij b) = ⁅padCol (Pi.single i b), padRow (Pi.single j (1 : R))⁆ := by
  have e := k2KarInd_stab_conj_x (1 : St n R) i j hij b
  rwa [inv_one, mul_one, one_mul, map_one (padMat (R := R) (n := n)), Matrix.one_mulVec,
    Matrix.vecMul_one] at e

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_stab_x

/-- `padMat x_ij(b) = 1 + e_i(b) e_j(1)ᵀ`. -/
theorem k2KarTri_padMat_x (i j : Fin n) (hij : i ≠ j) (b : R) :
    padMat (x i j hij b) = 1 + Matrix.vecMulVec (Pi.single i b) (Pi.single j (1 : R)) := by
  have e := k2KarTri_padMat_conj (1 : St n R) i j hij b
  rwa [inv_one, mul_one, one_mul, map_one (padMat (R := R) (n := n)), Matrix.one_mulVec,
    Matrix.vecMul_one] at e

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_padMat_x

/-- `(1 + V Wᵀ)(1 + V' W'ᵀ) = 1 + V Wᵀ + V' W'ᵀ` when `(W ⬝ᵥ V') W' = 0`. -/
theorem k2KarTri_rankOne_mul {V W V' W' : Fin n → R} (h : (W ⬝ᵥ V') • W' = 0) :
    (1 + Matrix.vecMulVec V W) * (1 + Matrix.vecMulVec V' W') =
      1 + (Matrix.vecMulVec V W + Matrix.vecMulVec V' W') := by
  simp only [mul_add, add_mul, mul_one, one_mul]
  rw [Matrix.vecMulVec_mul_vecMulVec, h, Matrix.vecMulVec_zero, add_zero]
  abel

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_rankOne_mul

end KarTriDataRing

section KarTriDataComm

variable {R : Type*} [CommRing R] {n : ℕ}

theorem k2KarTri_rowSum (i j : Fin n) (b a : R) {α ρ : Fin n → R} (hαe : α = Pi.single i a) :
    Matrix.vecMulVec (Pi.single i b) (Pi.single j (1 : R)) + Matrix.vecMulVec α ρ =
      Matrix.vecMulVec (Pi.single i (1 : R)) (b • Pi.single j (1 : R) + a • ρ) := by
  rw [hαe, Matrix.vecMulVec_add, Matrix.vecMulVec_smul, Matrix.vecMulVec_smul,
    ← Matrix.smul_vecMulVec, ← Matrix.smul_vecMulVec, k2KarTri_smul_single, k2KarTri_smul_single]
  simp only [mul_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_rowSum

theorem k2KarTri_colSum (i j : Fin n) (b r : R) {α ρ : Fin n → R} (hρe : ρ = Pi.single j r) :
    Matrix.vecMulVec (Pi.single i b) (Pi.single j (1 : R)) + Matrix.vecMulVec α ρ =
      Matrix.vecMulVec (r • α + Pi.single i b) (Pi.single j (1 : R)) := by
  rw [hρe, Matrix.add_vecMulVec, Matrix.smul_vecMulVec, ← Matrix.vecMulVec_smul,
    k2KarTri_smul_single, mul_one]
  exact add_comm _ _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_colSum
