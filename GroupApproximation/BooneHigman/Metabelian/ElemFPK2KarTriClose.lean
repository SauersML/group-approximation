import GroupApproximation.BooneHigman.Metabelian.ElemFPK2KarIndPair
import GroupApproximation.Meta.AxiomGuard

/-!
# Rank-one commutator data times a root conjugate

Lane `bh-met-93k`, closing module.  Call `(y, V, W)` a *rank-one datum* in `St(n, R)` when

  `stab y = ⁅padCol V, padRow W⁆`  and  `padMat y = 1 + V Wᵀ`.

For example `(g x_ij(b) g⁻¹, G e_i(b), e_j(1) H)` is one (`k2KarInd_stab_conj_x`,
`k2KarTri_padMat_conj`).

* `k2KarTri_stab_rankOne_mul_x`: over a ring with no zero divisors, if `(y, V, W)` is a
  rank-one datum and `padMat (y x_kl(c)) = 1`, then `stab (y x_kl(c)) = 1`.  Either `W = 0`
  (then `c = 0`), or the rank-one dichotomy `k2KarInd_vec_dichotomy` applies.
* `k2KarTri_stab_rankOne_mul_conj`: the same for `y · g x_kl(c) g⁻¹`, by conjugating with `g`.

Neither statement uses `1 ≠ 0`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral
open scoped Matrix commutatorElement

section KarTriClose

variable {R : Type*} [Ring R] {n : ℕ}

/-- `padMat (g x_ij(b) g⁻¹) = 1 + (G e_i(b)) (e_j(1) H)ᵀ`. -/
theorem k2KarTri_padMat_conj (g : St n R) (i j : Fin n) (hij : i ≠ j) (b : R) :
    padMat (g * x i j hij b * g⁻¹) =
      1 + Matrix.vecMulVec (padMat g *ᵥ Pi.single i b) (Pi.single j (1 : R) ᵥ* padMat g⁻¹) := by
  refine Matrix.ext fun p q ↦ ?_
  rw [k2KarInd_padMat_conj_apply, Matrix.add_apply, Matrix.vecMulVec_apply,
    k2KarInd_mulVec_single_apply, single_vecMul_apply, one_mul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_padMat_conj

/-- `(e_j(1) H) · (G e_i(b)) = 0` for `i ≠ j`. -/
theorem k2KarTri_dot_eq_zero (g : St n R) {i j : Fin n} (hij : i ≠ j) (b : R) :
    (Pi.single j (1 : R) ᵥ* padMat g⁻¹) ⬝ᵥ (padMat g *ᵥ Pi.single i b) = 0 := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, ← map_mul padMat g⁻¹ g, inv_mul_cancel,
    map_one, Matrix.vecMul_one, single_dotProduct, Pi.single_eq_of_ne hij.symm, mul_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_dot_eq_zero

theorem k2KarTri_padMat_conj_eq_one {g y : St n R} (h : padMat (g * y * g⁻¹) = 1) :
    padMat y = 1 := by
  have e : y = g⁻¹ * (g * y * g⁻¹) * g := by group
  rw [e, map_mul padMat (g⁻¹ * (g * y * g⁻¹)) g, map_mul padMat g⁻¹ (g * y * g⁻¹), h, mul_one,
    ← map_mul padMat g⁻¹ g, inv_mul_cancel, map_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_padMat_conj_eq_one

theorem k2KarTri_stab_conj_eq_one {g y : St n R} (h : stab n R y = 1) :
    stab n R (g * y * g⁻¹) = 1 := by
  rw [map_mul (stab n R) (g * y) g⁻¹, map_mul (stab n R) g y, h, mul_one,
    ← map_mul (stab n R) g g⁻¹, mul_inv_cancel, map_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_stab_conj_eq_one

/-- Rows `p ≠ i` of `padMat (x_ij(b) y)` are those of `padMat y`. -/
theorem k2KarTri_padMat_x_mul_apply_of_ne (y : St n R) (i j : Fin n) (hij : i ≠ j) (b : R)
    {p : Fin n} (hp : p ≠ i) (q : Fin n) :
    padMat (x i j hij b * y) p q = padMat y p q := by
  rw [map_mul padMat (x i j hij b) y, padMat_x, add_mul, one_mul, Matrix.add_apply,
    Matrix.single_mul_apply_of_ne b i j p q hp, add_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_padMat_x_mul_apply_of_ne

/-- Row `i` of `padMat (x_ij(b) y)`. -/
theorem k2KarTri_padMat_x_mul_apply_same (y : St n R) (i j : Fin n) (hij : i ≠ j) (b : R)
    (q : Fin n) :
    padMat (x i j hij b * y) i q = padMat y i q + b * padMat y j q := by
  rw [map_mul padMat (x i j hij b) y, padMat_x, add_mul, one_mul, Matrix.add_apply,
    Matrix.single_mul_apply_same]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_padMat_x_mul_apply_same

/-- **Rank-one datum times a root.** -/
theorem k2KarTri_stab_rankOne_mul_x (hR : ∀ a b : R, a * b = 0 → a = 0 ∨ b = 0)
    {y : St n R} {V W : Fin n → R} (hs : stab n R y = ⁅padCol V, padRow W⁆)
    (hm : padMat y = 1 + Matrix.vecMulVec V W) (k l : Fin n) (hkl : k ≠ l) (c : R)
    (h : padMat (y * x k l hkl c) = 1) : stab n R (y * x k l hkl c) = 1 := by
  have hmx : padMat y = 1 + Matrix.single k l (-c) := by
    have hy : y = y * x k l hkl c * x k l hkl (-c) := by
      rw [mul_assoc, x_mul, add_neg_cancel, x_zero, mul_one]
    rw [hy, map_mul padMat _ (x k l hkl (-c)), h, one_mul, padMat_x]
  have hVW : ∀ p q, V p * W q = Matrix.single k l (-c) p q := by
    intro p q
    have e : (1 + Matrix.vecMulVec V W) p q = (1 + Matrix.single k l (-c)) p q := by
      rw [← hm, hmx]
    rwa [Matrix.add_apply, Matrix.add_apply, Matrix.vecMulVec_apply, add_right_inj] at e
  rw [map_mul (stab n R) y, hs, stab_x]
  by_cases hW : W = 0
  · have hc : c = 0 := by
      have e := hVW k l
      rw [hW, Pi.zero_apply, mul_zero, Matrix.single_apply_same] at e
      exact neg_eq_zero.mp e.symm
    rw [hW, padRow_zero, commutatorElement_one_right, one_mul, hc, x_zero]
  · rcases k2KarInd_vec_dichotomy hR hW hVW with ⟨hV, hc⟩ | ⟨hV, hW', hvw⟩
    · rw [hV, padCol_zero, commutatorElement_one_left, one_mul, hc, x_zero]
    · rw [hV, hW', padCol_single, padRow_single,
        x_commutator k.castSucc (Fin.last n) l.castSucc (Fin.castSucc_lt_last k).ne
          (Fin.castSucc_lt_last l).ne' (fun h ↦ hkl (Fin.castSucc_inj.mp h)), x_mul, hvw, x_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_stab_rankOne_mul_x

/-- **Rank-one datum times a root conjugate.** -/
theorem k2KarTri_stab_rankOne_mul_conj (hR : ∀ a b : R, a * b = 0 → a = 0 ∨ b = 0)
    {y : St n R} {V W : Fin n → R} (hs : stab n R y = ⁅padCol V, padRow W⁆)
    (hm : padMat y = 1 + Matrix.vecMulVec V W) (g : St n R) (k l : Fin n) (hkl : k ≠ l) (c : R)
    (h : padMat (y * (g * x k l hkl c * g⁻¹)) = 1) :
    stab n R (y * (g * x k l hkl c * g⁻¹)) = 1 := by
  have e : y * (g * x k l hkl c * g⁻¹) = g * (g⁻¹ * y * g * x k l hkl c) * g⁻¹ := by group
  rw [e] at h ⊢
  refine k2KarTri_stab_conj_eq_one (k2KarTri_stab_rankOne_mul_x hR
    (V := padMat g⁻¹ *ᵥ V) (W := W ᵥ* padMat g) ?_ ?_ k l hkl c (k2KarTri_padMat_conj_eq_one h))
  · have hg : stab n R g = (stab n R g⁻¹)⁻¹ := by rw [map_inv, inv_inv]
    have hrow := stab_conj_padRow g W
    rw [← map_inv (stab n R) g, hg] at hrow
    rw [map_mul (stab n R) (g⁻¹ * y) g, map_mul (stab n R) g⁻¹ y, hs, hg,
      conjugate_commutatorElement, stab_conj_padCol g⁻¹ V, hrow]
  · rw [map_mul padMat (g⁻¹ * y) g, map_mul padMat g⁻¹ y, hm, mul_add, add_mul, mul_one,
      Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← map_mul padMat g⁻¹ g, inv_mul_cancel,
      map_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_stab_rankOne_mul_conj

end KarTriClose

end GroupApproximation.BooneHigman.Metabelian.ElemFP
