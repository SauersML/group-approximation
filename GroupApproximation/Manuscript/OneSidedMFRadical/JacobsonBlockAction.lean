import GroupApproximation.Manuscript.OneSidedMFRadical.JacobsonFiniteMatrices
import GroupApproximation.Algebra.FinitaryLinearTransvections
import GroupApproximation.Leavitt.CongruenceSubgroups
import GroupApproximation.Leavitt.ElementaryNoFiniteQuotients
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.Tactic.NoncommRing

/-!
# `EL_n(J)` acting on `V^n`, and each transvection as a relative root

`non_mf_groups_exist.tex`, the remark after `prop:torsion-defect-ring`
(tex lines 1131--1138):

> Over `F_2` every element of `GL_fs(V^n)` is a product of transvections, and each
> transvection is a relative root `e_{ij}(f_{uv})` or, inside one coordinate, the
> commutator `[e_{ik}(f_{uw}), e_{ki}(f_{wv})]` of two.

Matrices over `J ⊆ End(V)` act on `V^n = Fin n → F_2[X]` by `(m x)_i = Σ_j m_{ij}(x_j)`
(`matrixAct`, through Mathlib's `End(M^n) ≅ M_n(End M)`), so `EL_n(J)` acts faithfully
on `V^n` (`blockAct`, `blockAct_injective`).  With the standard basis
`b_{(i,u)} = X^u` in coordinate `i`:

* `f_{uv}` sends `p` to `(coefficient of X^v in p) · X^u` (`matUnit_apply`), and
  `f_{uv} f_{wx} = [v = w] f_{ux}`;
* `1 + f_{uv} E_{ij}` acts as the basis transvection `τ_{(i,u),(j,v)}`
  (`matrixAct_one_add_single_matUnit`);
* so `τ_{(i,u),(j,v)}` is the image of the relative root `e_{ij}(f_{uv})` when `i ≠ j`
  (`blockAct_elGen_matUnit`), and of the commutator `[e_{ik}(f_{uv}), e_{ki}(f_{vv})]`
  when `i = j`, `u ≠ v` (`blockAct_commutator_matUnit`).
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace JacobsonSymbol

open TorsionComplementaryIdempotents FinitaryLinear

/-! ## Matrix units in `J` -/

theorem matUnit_apply (u v : ℕ) (p : JacobsonSpace) :
    matUnit u v p = p.coeff v • Polynomial.X ^ u := by
  have h : matUnit u v = (Polynomial.lcoeff (ZMod 2) v).smulRight (Polynomial.X ^ u) := by
    refine (Polynomial.basisMonomials (ZMod 2)).ext fun N ↦ ?_
    rw [Polynomial.coe_basisMonomials, ← Polynomial.X_pow_eq_monomial, matUnit_X_pow,
      LinearMap.smulRight_apply, Polynomial.lcoeff_apply, Polynomial.coeff_X_pow]
    by_cases hN : N = v
    · rw [if_pos hN, if_pos hN.symm, one_smul]
    · rw [if_neg hN, if_neg (Ne.symm hN), zero_smul]
  rw [h, LinearMap.smulRight_apply, Polynomial.lcoeff_apply]

theorem matUnit_mul (u v w x : ℕ) :
    matUnit u v * matUnit w x = if v = w then matUnit u x else 0 := by
  refine (Polynomial.basisMonomials (ZMod 2)).ext fun N ↦ ?_
  rw [Polynomial.coe_basisMonomials, ← Polynomial.X_pow_eq_monomial, Module.End.mul_apply,
    matUnit_X_pow]
  by_cases hNx : N = x
  · rw [if_pos hNx, matUnit_X_pow]
    by_cases hvw : v = w
    · rw [if_pos hvw.symm, if_pos hvw, matUnit_X_pow, if_pos hNx]
    · rw [if_neg (Ne.symm hvw), if_neg hvw, LinearMap.zero_apply]
  · rw [if_neg hNx, map_zero]
    by_cases hvw : v = w
    · rw [if_pos hvw, matUnit_X_pow, if_neg hNx]
    · rw [if_neg hvw, LinearMap.zero_apply]

theorem matUnitJ_mul (u v w x : ℕ) :
    matUnitJ u v * matUnitJ w x = if v = w then matUnitJ u x else 0 := by
  apply Subtype.ext
  by_cases hvw : v = w
  · rw [if_pos hvw]
    show (matUnitJ u v : Module.End (ZMod 2) JacobsonSpace) * matUnitJ w x = matUnitJ u x
    rw [coe_matUnitJ, coe_matUnitJ, coe_matUnitJ, matUnit_mul, if_pos hvw]
  · rw [if_neg hvw]
    show (matUnitJ u v : Module.End (ZMod 2) JacobsonSpace) * matUnitJ w x = 0
    rw [coe_matUnitJ, coe_matUnitJ, matUnit_mul, if_neg hvw]

/-! ## The action of matrices over `J` on `V^n` -/

/-- Matrices over `J` act on `V^n` by `(m x)_i = Σ_j m_{ij}(x_j)`. -/
noncomputable def matrixAct (n : ℕ) :
    Matrix (Fin n) (Fin n) ↥jacobsonAlgebra →+* Module.End (ZMod 2) (BinaryPower n) :=
  ((Matrix.endVecRingEquivMatrixEnd (Fin n) (ZMod 2) JacobsonSpace).symm :
      Matrix (Fin n) (Fin n) (Module.End (ZMod 2) JacobsonSpace) →+*
        Module.End (ZMod 2) (Fin n → JacobsonSpace)).comp
    jacobsonAlgebra.subtype.mapMatrix

theorem matrixAct_apply (n : ℕ) (m : Matrix (Fin n) (Fin n) ↥jacobsonAlgebra) (x : BinaryPower n)
    (i : Fin n) :
    matrixAct n m x i = ∑ j, (m i j : Module.End (ZMod 2) JacobsonSpace) (x j) := rfl

theorem matrixAct_injective (n : ℕ) : Function.Injective (matrixAct n) := by
  intro m m' h
  have h2 : jacobsonAlgebra.subtype.mapMatrix m = jacobsonAlgebra.subtype.mapMatrix m' :=
    (Matrix.endVecRingEquivMatrixEnd (Fin n) (ZMod 2) JacobsonSpace).symm.injective h
  ext i j
  exact Subtype.ext (congrFun (congrFun h2 i) j)

/-- **`EL_n(J)` acting on `V^n`.** -/
noncomputable def blockAct (n : ℕ) :
    elementaryGroup (Fin n) ↥jacobsonAlgebra →* (BinaryPower n ≃ₗ[ZMod 2] BinaryPower n) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (BinaryPower n)).toMonoidHom.comp
    ((Units.map (matrixAct n).toMonoidHom).comp (elementaryGroup (Fin n) ↥jacobsonAlgebra).subtype)

theorem blockAct_apply (n : ℕ) (g : elementaryGroup (Fin n) ↥jacobsonAlgebra) (x : BinaryPower n) :
    blockAct n g x = matrixAct n ((g : (Matrix (Fin n) (Fin n) ↥jacobsonAlgebra)ˣ) :
      Matrix (Fin n) (Fin n) ↥jacobsonAlgebra) x := rfl

/-- **`EL_n(J)` acts faithfully on `V^n`.** -/
theorem blockAct_injective (n : ℕ) : Function.Injective (blockAct n) := by
  intro g h hgh
  apply Subtype.ext
  apply Units.ext
  apply matrixAct_injective n
  refine LinearMap.ext fun x ↦ ?_
  have := congrArg (fun e : BinaryPower n ≃ₗ[ZMod 2] BinaryPower n ↦ e x) hgh
  simpa [blockAct_apply] using this

/-! ## Relative roots as basis transvections -/

theorem binaryPowerBasis_apply (i : Fin n) (u : ℕ) :
    binaryPowerBasis n ⟨i, u⟩ = Pi.single i (Polynomial.X ^ u) := by
  simp [binaryPowerBasis, binaryBasis, Polynomial.coe_basisMonomials, Polynomial.X_pow_eq_monomial]

theorem coord_binaryPowerBasis (x : BinaryPower n) (j : Fin n) (v : ℕ) :
    (binaryPowerBasis n).coord ⟨j, v⟩ x = (x j).coeff v := by
  rw [Module.Basis.coord_apply, Pi.basis_repr]
  rfl

/-- **`1 + f_{uv} E_{ij}` acts as the basis transvection `τ_{(i,u),(j,v)}`.** -/
theorem matrixAct_one_add_single_matUnit (n : ℕ) {i j : Fin n} {u v : ℕ}
    (h : (⟨i, u⟩ : Σ _ : Fin n, ℕ) ≠ ⟨j, v⟩) :
    matrixAct n (1 + Matrix.single i j (matUnitJ u v)) =
      (basisTransvection (binaryPowerBasis n) h : BinaryPower n →ₗ[ZMod 2] BinaryPower n) := by
  classical
  refine LinearMap.ext fun x ↦ funext fun k ↦ ?_
  rw [matrixAct_apply, LinearEquiv.coe_coe, basisTransvection_apply, coord_binaryPowerBasis,
    binaryPowerBasis_apply, Pi.add_apply, Pi.smul_apply]
  have hsplit : ∀ l : Fin n,
      (((1 + Matrix.single i j (matUnitJ u v)) k l : ↥jacobsonAlgebra) :
        Module.End (ZMod 2) JacobsonSpace) (x l) =
        (if k = l then x l else 0) + (if i = k ∧ j = l then matUnit u v (x l) else 0) := by
    intro l
    rw [Matrix.add_apply, Subring.coe_add, LinearMap.add_apply, Matrix.one_apply, Matrix.single_apply]
    congr 1
    · by_cases hkl : k = l
      · rw [if_pos hkl, if_pos hkl, Subring.coe_one, Module.End.one_apply]
      · rw [if_neg hkl, if_neg hkl, Subring.coe_zero, LinearMap.zero_apply]
    · by_cases hc : i = k ∧ j = l
      · rw [if_pos hc, if_pos hc, coe_matUnitJ]
      · rw [if_neg hc, if_neg hc, Subring.coe_zero, LinearMap.zero_apply]
  rw [Finset.sum_congr rfl fun l _ ↦ hsplit l, Finset.sum_add_distrib,
    Finset.sum_eq_single k (fun l _ hl ↦ if_neg (Ne.symm hl)) (by simp), if_pos rfl]
  congr 1
  by_cases hik : i = k
  · subst hik
    rw [Finset.sum_eq_single j (fun l _ hl ↦ if_neg fun hc ↦ hl hc.2.symm) (by simp),
      if_pos ⟨rfl, rfl⟩, matUnit_apply, Pi.single_eq_same]
  · rw [Finset.sum_eq_zero fun l _ ↦ if_neg fun hc ↦ hik hc.1, Pi.single_eq_of_ne (Ne.symm hik),
      smul_zero]

/-- **A relative root is a basis transvection**: `e_{ij}(f_{uv})` acts as
`τ_{(i,u),(j,v)}` for `i ≠ j`. -/
theorem blockAct_elGen_matUnit (n : ℕ) {i j : Fin n} (hij : i ≠ j) (u v : ℕ) :
    blockAct n (elGen i j hij (matUnitJ u v)) =
      basisTransvection (binaryPowerBasis n)
        (show (⟨i, u⟩ : Σ _ : Fin n, ℕ) ≠ ⟨j, v⟩ from fun h ↦ hij (congrArg Sigma.fst h)) := by
  refine LinearEquiv.ext fun x ↦ ?_
  rw [blockAct_apply]
  exact congrArg (fun f : BinaryPower n →ₗ[ZMod 2] BinaryPower n ↦ f x)
    (matrixAct_one_add_single_matUnit n _)

/-- **Inside one coordinate, a transvection is a commutator of two relative roots**:
`[e_{ik}(f_{uv}), e_{ki}(f_{vv})]` acts as `τ_{(i,u),(i,v)}` for `k ≠ i`, `u ≠ v`. -/
theorem blockAct_commutator_matUnit (n : ℕ) {i k : Fin n} (hik : i ≠ k) {u v : ℕ} (huv : u ≠ v) :
    blockAct n (elGen i k hik (matUnitJ u v) * elGen k i (Ne.symm hik) (matUnitJ v v) *
        (elGen i k hik (matUnitJ u v))⁻¹ * (elGen k i (Ne.symm hik) (matUnitJ v v))⁻¹) =
      basisTransvection (binaryPowerBasis n)
        (show (⟨i, u⟩ : Σ _ : Fin n, ℕ) ≠ ⟨i, v⟩ from fun h ↦ huv (by simpa using h)) := by
  set A : Matrix (Fin n) (Fin n) ↥jacobsonAlgebra := Matrix.single i k (matUnitJ u v) with hA
  set B : Matrix (Fin n) (Fin n) ↥jacobsonAlgebra := Matrix.single k i (matUnitJ v v) with hB
  have hAA : A * A = 0 := by
    rw [hA, Matrix.single_mul_single_of_ne _ _ _ hik.symm]
  have hBB : B * B = 0 := by
    rw [hB, Matrix.single_mul_single_of_ne _ _ _ hik]
  have hAB : A * B = Matrix.single i i (matUnitJ u v) := by
    rw [hA, hB, Matrix.single_mul_single_same, matUnitJ_mul, if_pos rfl]
  have hBA : B * A = 0 := by
    rw [hA, hB, Matrix.single_mul_single_same, matUnitJ_mul, if_neg (Ne.symm huv),
      Matrix.single_zero]
  have hval : (((elGen i k hik (matUnitJ u v) * elGen k i (Ne.symm hik) (matUnitJ v v) *
        (elGen i k hik (matUnitJ u v))⁻¹ * (elGen k i (Ne.symm hik) (matUnitJ v v))⁻¹ :
          elementaryGroup (Fin n) ↥jacobsonAlgebra) : (Matrix (Fin n) (Fin n) ↥jacobsonAlgebra)ˣ) :
        Matrix (Fin n) (Fin n) ↥jacobsonAlgebra) = 1 + Matrix.single i i (matUnitJ u v) := by
    have e : (((elGen i k hik (matUnitJ u v) * elGen k i (Ne.symm hik) (matUnitJ v v) *
        (elGen i k hik (matUnitJ u v))⁻¹ * (elGen k i (Ne.symm hik) (matUnitJ v v))⁻¹ :
          elementaryGroup (Fin n) ↥jacobsonAlgebra) : (Matrix (Fin n) (Fin n) ↥jacobsonAlgebra)ˣ) :
        Matrix (Fin n) (Fin n) ↥jacobsonAlgebra) = (1 + A) * (1 + B) * (1 - A) * (1 - B) := by
      rfl
    rw [e]
    have t1 : (1 + A) * (1 + B) * (1 - A) = 1 + B + A * B - A * A - B * A - A * (B * A) := by
      noncomm_ring
    have t2 : (1 + B + A * B) * (1 - B) = 1 + A * B - B * B - A * (B * B) := by
      noncomm_ring
    rw [t1, hAA, hBA, mul_zero, sub_zero, sub_zero, sub_zero, t2, hBB, mul_zero, sub_zero, sub_zero,
      hAB]
  refine LinearEquiv.ext fun x ↦ ?_
  rw [blockAct_apply, hval]
  exact congrArg (fun f : BinaryPower n →ₗ[ZMod 2] BinaryPower n ↦ f x)
    (matrixAct_one_add_single_matUnit n _)

end JacobsonSymbol
end OneSidedMFRadical
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.JacobsonSymbol.blockAct_injective
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.JacobsonSymbol.blockAct_elGen_matUnit
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.JacobsonSymbol.blockAct_commutator_matUnit
