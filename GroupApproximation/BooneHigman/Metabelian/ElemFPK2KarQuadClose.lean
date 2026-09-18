import GroupApproximation.BooneHigman.Metabelian.ElemFPK2KarTriStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# A rank-one datum times two root conjugates

Lane `bh-met-93q`, closing module.  A *rank-one datum* `(Y, V, W)` means
`stab Y = ⁅padCol V, padRow W⁆` and `padMat Y = 1 + V Wᵀ` (`ElemFPK2KarTriClose`).

* `k2KarQuad_dot_conj`: `(W H) ⬝ᵥ (G V) = W ⬝ᵥ V` for `G = padMat g`, `H = padMat g⁻¹`.
* `k2KarQuad_dot_eq_of_padMat`: two rank-one data for the same matrix have the same `W ⬝ᵥ V`
  (by `Matrix.trace_vecMulVec`).
* **`k2KarQuad_stDies_datum_mul_two`**: over a commutative ring with no zero divisors, if
  `(Y, V, W)` is a rank-one datum with `W ⬝ᵥ V = 0`, and `Y · z₃ · z₄` has trivial matrix
  (`z₃, z₄` root conjugates), then `Y · z₃ · z₄` dies after one stabilization (up to
  conjugation).  Proof: `Y z₃ z₄ = z₄⁻¹ (z₄ Y z₃) z₄`, and `z₄ Y z₃`, conjugated by `g₄⁻¹`, is
  `x(c₄) · (g₄⁻¹ Y g₄) · (conjugate of x(c₃))`, which is killed by the triple lemma
  `k2KarTri_stab_triple`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral
open scoped Matrix commutatorElement

section KarQuadCloseRing

variable {R : Type*} [Ring R] {n : ℕ}

/-- `(W ᵥ* padMat g⁻¹) ⬝ᵥ (padMat g *ᵥ V) = W ⬝ᵥ V`. -/
theorem k2KarQuad_dot_conj (g : St n R) (V W : Fin n → R) :
    (W ᵥ* padMat g⁻¹) ⬝ᵥ (padMat g *ᵥ V) = W ⬝ᵥ V := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, ← map_mul padMat g⁻¹ g, inv_mul_cancel,
    map_one, Matrix.vecMul_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarQuad_dot_conj

end KarQuadCloseRing

section KarQuadCloseComm

variable {R : Type*} [CommRing R] {n : ℕ}

/-- Two rank-one decompositions of the same matrix have the same `W ⬝ᵥ V`. -/
theorem k2KarQuad_dot_eq_of_padMat {y : St n R} {V W V' W' : Fin n → R}
    (h : padMat y = 1 + Matrix.vecMulVec V W) (h' : padMat y = 1 + Matrix.vecMulVec V' W') :
    W' ⬝ᵥ V' = W ⬝ᵥ V := by
  have e : Matrix.vecMulVec V' W' = Matrix.vecMulVec V W := add_left_cancel (h'.symm.trans h)
  have t := congrArg Matrix.trace e
  rw [Matrix.trace_vecMulVec, Matrix.trace_vecMulVec] at t
  rw [dotProduct_comm W' V', dotProduct_comm W V]
  exact t

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarQuad_dot_eq_of_padMat

/-- **A rank-one datum times two root conjugates** with trivial matrix dies after padding. -/
theorem k2KarQuad_stDies_datum_mul_two (hR : ∀ a b : R, a * b = 0 → a = 0 ∨ b = 0)
    {Y : St n R} {V W : Fin n → R} (hs : stab n R Y = ⁅padCol V, padRow W⁆)
    (hm : padMat Y = 1 + Matrix.vecMulVec V W) (hd : W ⬝ᵥ V = 0)
    (g₃ : St n R) (k l : Fin n) (hkl : k ≠ l) (c₃ : R)
    (g₄ : St n R) (i j : Fin n) (hij : i ≠ j) (c₄ : R)
    (h : padMat (Y * (g₃ * x k l hkl c₃ * g₃⁻¹) * (g₄ * x i j hij c₄ * g₄⁻¹)) = 1) :
    cubeDiagDilate_StDies (Y * (g₃ * x k l hkl c₃ * g₃⁻¹) * (g₄ * x i j hij c₄ * g₄⁻¹)) := by
  obtain ⟨hs', hm'⟩ := k2KarTri_rankOne_conj g₄⁻¹ hs hm
  have hd' : (W ᵥ* padMat g₄⁻¹⁻¹) ⬝ᵥ (padMat g₄⁻¹ *ᵥ V) = 0 := by
    rw [k2KarQuad_dot_conj g₄⁻¹ V W, hd]
  have e : Y * (g₃ * x k l hkl c₃ * g₃⁻¹) * (g₄ * x i j hij c₄ * g₄⁻¹) =
      (g₄ * x i j hij c₄ * g₄⁻¹)⁻¹ *
        (g₄ * (x i j hij c₄ * (g₄⁻¹ * Y * g₄⁻¹⁻¹) *
          ((g₄⁻¹ * g₃) * x k l hkl c₃ * (g₄⁻¹ * g₃)⁻¹)) * g₄⁻¹) *
        (g₄ * x i j hij c₄ * g₄⁻¹)⁻¹⁻¹ := by
    group
  rw [e] at h ⊢
  have h₁ := k2KarTri_padMat_conj_eq_one (k2KarTri_padMat_conj_eq_one h)
  have h₂ := k2KarTri_stab_triple hR i j hij c₄ hs' hm' hd' (g₄⁻¹ * g₃) k l hkl c₃ h₁
  exact cubeDiagDilate_stDies_conj _ (k2KarInd_stDies_of_stab (k2KarTri_stab_conj_eq_one h₂))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarQuad_stDies_datum_mul_two

end KarQuadCloseComm

end GroupApproximation.BooneHigman.Metabelian.ElemFP
