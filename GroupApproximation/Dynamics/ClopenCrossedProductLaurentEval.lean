import GroupApproximation.Dynamics.ClopenCrossedProduct
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.Group.Int.Even
import Mathlib.Algebra.Group.Even

/-!
# Evaluating `R_Y` at points of period at most two

`non_mf_groups_exist.tex`, `sec:chain-core`, the remark after `cor:dynamic-rank-budget`
(tex 1796–1805):

> Its finitely generated restriction image lies in a finite product of groups
> $\GL_2(k[z,z^{-1}])$ [...] The same reasoning applies to unit groups when every core point has
> period at most two: a finite invariant clopen partition gives matrix blocks of size at most two
> over $k[z,z^{-1}]$.

A point `x` with `T x = x` gives the ring map `R_X → k[z,z^{-1}]`, `f ↦ f(x)`, `u ↦ z`
(`evalLaurent`).  When `T ∘ T = id`, every point `x` gives the ring map
`R_X → M_2(k[z,z^{-1}])`, `f ↦ diag(f(x), f(T x))`, `u ↦ z P` with `P` the transposition
(`evalPair`); its first row recovers all Laurent coefficients at `x`.  These are the matrix blocks
of size at most two of the printed argument, one block per point, with the coefficient data read off
by `coeff_evalLaurent` and `coeff_evalPair_row`.
-/

namespace GroupApproximation
namespace ClopenCrossedProduct

open Multiplicative (ofAdd toAdd)

variable {X : Type*} [TopologicalSpace X]

/-- A fixed point of `T` is fixed by every power of `T`. -/
theorem zpow_apply_of_apply_eq {T : X ≃ₜ X} {x : X} (hx : T x = x) (n : ℤ) : (T ^ n) x = x := by
  have hs : T.symm x = x := T.symm_apply_eq.mpr hx.symm
  induction n using Int.induction_on with
  | zero => rfl
  | succ i ih => rw [zpow_add_one, Homeomorph.mul_apply, hx, ih]
  | pred i ih => rw [zpow_sub_one, Homeomorph.mul_apply, Homeomorph.inv_apply, hs, ih]

/-- If `T ∘ T = id`, then `T ^ n` is the identity for even `n` and `T` for odd `n`. -/
theorem zpow_apply_of_apply_apply_eq {T : X ≃ₜ X} (hT : ∀ y, T (T y) = y) (n : ℤ) (x : X) :
    (T ^ n) x = if Even n then x else T x := by
  have hs : ∀ y, T.symm y = T y := fun y ↦ T.symm_apply_eq.mpr (hT y).symm
  induction n using Int.induction_on generalizing x with
  | zero => simp
  | succ i ih =>
    rw [zpow_add_one, Homeomorph.mul_apply, ih]
    by_cases h : Even (i : ℤ)
    · have h' : ¬Even ((i : ℤ) + 1) := fun he ↦ Int.even_add_one.mp he h
      simp only [h, h', ↓reduceIte]
    · have h' : Even ((i : ℤ) + 1) := Int.even_add_one.mpr h
      simp only [h, h', ↓reduceIte, hT]
  | pred i ih =>
    rw [zpow_sub_one, Homeomorph.mul_apply, Homeomorph.inv_apply, hs, ih]
    by_cases h : Even (-(i : ℤ))
    · have h' : ¬Even (-(i : ℤ) - 1) := fun he ↦ Int.even_sub_one.mp he h
      simp only [h, h', ↓reduceIte]
    · have h' : Even (-(i : ℤ) - 1) := Int.even_sub_one.mpr h
      simp only [h, h', ↓reduceIte, hT]

section Eval

variable (T : X ≃ₜ X) (k : Type*) [CommRing k]

/-- `n ↦ zⁿ`, as a monoid hom `ℤ → k[z,z^{-1}]`. -/
noncomputable def laurentT : Multiplicative ℤ →* LaurentPolynomial k where
  toFun j := LaurentPolynomial.T (toAdd j)
  map_one' := LaurentPolynomial.T_zero
  map_mul' a b := by rw [toAdd_mul, LaurentPolynomial.T_add]

/-- **Evaluation at a fixed point**, `R_X → k[z,z^{-1}]`: `f ↦ f(x)` and `u ↦ z`. -/
noncomputable def evalLaurent {x : X} (hx : T x = x) :
    ClopenCrossedProduct T k →+* LaurentPolynomial k :=
  SkewMonoidAlgebra.liftNCRingHom
    (LaurentPolynomial.C.comp
      ((LocallyConstant.evalRingHom x).comp (ClopenCoeff.of T k).symm.toRingHom))
    (laurentT k) (fun {c j} ↦ by
      have hj : (ClopenCoeff.of T k).symm (j • c) x = (ClopenCoeff.of T k).symm c x := by
        show (ClopenCoeff.of T k).symm c ((T ^ (-toAdd j)) x) = _
        rw [zpow_apply_of_apply_eq hx]
      show LaurentPolynomial.C ((ClopenCoeff.of T k).symm (j • c) x) * laurentT k j =
        laurentT k j * LaurentPolynomial.C ((ClopenCoeff.of T k).symm c x)
      rw [hj, mul_comm])

theorem evalLaurent_single {x : X} (hx : T x = x) (m : ℤ) (c : ClopenCoeff T k) :
    evalLaurent T k hx (SkewMonoidAlgebra.single (ofAdd m) c) =
      LaurentPolynomial.C ((ClopenCoeff.of T k).symm c x) * LaurentPolynomial.T m :=
  SkewMonoidAlgebra.liftNC_single _ _ _ _

/-- The Laurent coefficients of `evalLaurent y` are the coefficients of `y` evaluated at `x`. -/
theorem coeff_evalLaurent {x : X} (hx : T x = x) (y : ClopenCrossedProduct T k) (n : ℤ) :
    (evalLaurent T k hx y).coeff n =
      (ClopenCoeff.of T k).symm (SkewMonoidAlgebra.coeff y (ofAdd n)) x := by
  classical
  induction y using SkewMonoidAlgebra.induction_on with
  | zero => simp
  | single g c =>
    obtain ⟨m, rfl⟩ : ∃ m : ℤ, ofAdd m = g := ⟨toAdd g, rfl⟩
    rw [evalLaurent_single, ← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single,
      SkewMonoidAlgebra.coeff_single_apply, Finsupp.single_apply]
    by_cases h : m = n
    · subst h
      simp
    · rw [if_neg h, if_neg fun h' ↦ h (ofAdd.injective h')]
      simp
  | add y z hy hz =>
    rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hy, hz,
      SkewMonoidAlgebra.coeff_add, Finsupp.add_apply, map_add]
    rfl

/-- `n ↦ zⁿ Pⁿ`, with `P` the transposition: `zⁿ` on the diagonal for even `n`, off the diagonal
for odd `n`. -/
noncomputable def laurentSwap : Multiplicative ℤ →* Matrix (Fin 2) (Fin 2) (LaurentPolynomial k) where
  toFun j := if Even (toAdd j) then !![LaurentPolynomial.T (toAdd j), 0; 0, LaurentPolynomial.T (toAdd j)]
    else !![0, LaurentPolynomial.T (toAdd j); LaurentPolynomial.T (toAdd j), 0]
  map_one' := by
    simp only [toAdd_one, Even.zero, ↓reduceIte, LaurentPolynomial.T_zero, Matrix.one_fin_two]
  map_mul' a b := by
    obtain ⟨m, rfl⟩ : ∃ m : ℤ, ofAdd m = a := ⟨toAdd a, rfl⟩
    obtain ⟨n, rfl⟩ : ∃ n : ℤ, ofAdd n = b := ⟨toAdd b, rfl⟩
    by_cases hm : Even m <;> by_cases hn : Even n
    · have h : Even (m + n) := Int.even_add.mpr (iff_of_true hm hn)
      simp only [toAdd_mul, toAdd_ofAdd, hm, hn, h, ↓reduceIte, LaurentPolynomial.T_add,
        Matrix.mul_fin_two, mul_zero, zero_mul, add_zero, zero_add]
    · have h : ¬Even (m + n) := fun h ↦ hn ((Int.even_add.mp h).mp hm)
      simp only [toAdd_mul, toAdd_ofAdd, hm, hn, h, ↓reduceIte, LaurentPolynomial.T_add,
        Matrix.mul_fin_two, mul_zero, zero_mul, add_zero, zero_add]
    · have h : ¬Even (m + n) := fun h ↦ hm ((Int.even_add.mp h).mpr hn)
      simp only [toAdd_mul, toAdd_ofAdd, hm, hn, h, ↓reduceIte, LaurentPolynomial.T_add,
        Matrix.mul_fin_two, mul_zero, zero_mul, add_zero, zero_add]
    · have h : Even (m + n) := Int.even_add.mpr (iff_of_false hm hn)
      simp only [toAdd_mul, toAdd_ofAdd, hm, hn, h, ↓reduceIte, LaurentPolynomial.T_add,
        Matrix.mul_fin_two, mul_zero, zero_mul, add_zero, zero_add]

theorem laurentSwap_ofAdd (n : ℤ) :
    laurentSwap k (ofAdd n) =
      if Even n then !![LaurentPolynomial.T n, 0; 0, LaurentPolynomial.T n]
      else !![0, LaurentPolynomial.T n; LaurentPolynomial.T n, 0] :=
  rfl

/-- `f ↦ diag(f(x), f(T x))`. -/
noncomputable def coeffPair (x : X) :
    ClopenCoeff T k →+* Matrix (Fin 2) (Fin 2) (LaurentPolynomial k) :=
  (Matrix.diagonalRingHom (Fin 2) (LaurentPolynomial k)).comp
    (RingHom.pi fun i : Fin 2 ↦ LaurentPolynomial.C.comp
      ((LocallyConstant.evalRingHom (![x, T x] i)).comp (ClopenCoeff.of T k).symm.toRingHom))

theorem coeffPair_eq (x : X) (c : ClopenCoeff T k) :
    coeffPair T k x c =
      !![LaurentPolynomial.C ((ClopenCoeff.of T k).symm c x), 0;
        0, LaurentPolynomial.C ((ClopenCoeff.of T k).symm c (T x))] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- **Evaluation at a point of period at most two**, `R_X → M_2(k[z,z^{-1}])`:
`f ↦ diag(f(x), f(T x))` and `u ↦ z P`, when `T ∘ T = id`. -/
noncomputable def evalPair (hT : ∀ y, T (T y) = y) (x : X) :
    ClopenCrossedProduct T k →+* Matrix (Fin 2) (Fin 2) (LaurentPolynomial k) :=
  SkewMonoidAlgebra.liftNCRingHom (coeffPair T k x) (laurentSwap k) (fun {c j} ↦ by
    obtain ⟨n, rfl⟩ : ∃ n : ℤ, ofAdd n = j := ⟨toAdd j, rfl⟩
    have hev : ∀ y, (ClopenCoeff.of T k).symm (ofAdd n • c) y =
        (ClopenCoeff.of T k).symm c (if Even n then y else T y) := by
      intro y
      show (ClopenCoeff.of T k).symm c ((T ^ (-n)) y) = _
      simp only [zpow_apply_of_apply_apply_eq hT, even_neg]
    rw [coeffPair_eq, coeffPair_eq, laurentSwap_ofAdd]
    by_cases hn : Even n
    · simp only [hev, hn, ↓reduceIte, Matrix.mul_fin_two, mul_zero, zero_mul, add_zero, zero_add,
        LaurentPolynomial.T_mul]
    · simp only [hev, hn, ↓reduceIte, hT, Matrix.mul_fin_two, mul_zero, zero_mul, add_zero,
        zero_add, LaurentPolynomial.T_mul])

theorem evalPair_single (hT : ∀ y, T (T y) = y) (x : X) (m : ℤ) (c : ClopenCoeff T k) :
    evalPair T k hT x (SkewMonoidAlgebra.single (ofAdd m) c) =
      coeffPair T k x c * laurentSwap k (ofAdd m) :=
  SkewMonoidAlgebra.liftNC_single _ _ _ _

theorem evalPair_single_row (hT : ∀ y, T (T y) = y) (x : X) (m : ℤ) (c : ClopenCoeff T k) :
    evalPair T k hT x (SkewMonoidAlgebra.single (ofAdd m) c) 0 0 +
        evalPair T k hT x (SkewMonoidAlgebra.single (ofAdd m) c) 0 1 =
      LaurentPolynomial.C ((ClopenCoeff.of T k).symm c x) * LaurentPolynomial.T m := by
  rw [evalPair_single, laurentSwap_ofAdd, coeffPair_eq]
  by_cases hm : Even m
  · simp only [hm, ↓reduceIte, Matrix.mul_fin_two, mul_zero, zero_mul, add_zero, zero_add,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  · simp only [hm, ↓reduceIte, Matrix.mul_fin_two, mul_zero, zero_mul, add_zero, zero_add,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The first row of `evalPair y` recovers the Laurent coefficients of `y` at `x`. -/
theorem coeff_evalPair_row (hT : ∀ y, T (T y) = y) (x : X) (y : ClopenCrossedProduct T k)
    (n : ℤ) :
    (evalPair T k hT x y 0 0 + evalPair T k hT x y 0 1).coeff n =
      (ClopenCoeff.of T k).symm (SkewMonoidAlgebra.coeff y (ofAdd n)) x := by
  classical
  induction y using SkewMonoidAlgebra.induction_on with
  | zero => simp
  | single g c =>
    obtain ⟨m, rfl⟩ : ∃ m : ℤ, ofAdd m = g := ⟨toAdd g, rfl⟩
    rw [evalPair_single_row, ← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single,
      SkewMonoidAlgebra.coeff_single_apply, Finsupp.single_apply]
    by_cases h : m = n
    · subst h
      simp
    · rw [if_neg h, if_neg fun h' ↦ h (ofAdd.injective h')]
      simp
  | add y z hy hz =>
    rw [map_add, Matrix.add_apply, Matrix.add_apply, add_add_add_comm, AddMonoidAlgebra.coeff_add,
      Finsupp.add_apply, hy, hz, SkewMonoidAlgebra.coeff_add, Finsupp.add_apply, map_add]
    rfl

end Eval

end ClopenCrossedProduct
end GroupApproximation

#audit_axioms GroupApproximation.ClopenCrossedProduct.coeff_evalLaurent
#audit_axioms GroupApproximation.ClopenCrossedProduct.coeff_evalPair_row
