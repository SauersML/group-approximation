import GroupApproximation.BooneHigmanLinear.CharZero.K2Found.VdK
import Mathlib.GroupTheory.NoncommPiCoprod

/-!
# vdK 3.7: row and column products in `St(n, A)` (k2-poly, piece F.1)

W. van der Kallen, *Another presentation for Steinberg groups*, Indag. Math. **39** (1977), 3.7.
For a row `j` and an index `r`, `x_r(j) = ∏_{q ≠ r} x_{rq}(j_q)`; for a column `i`,
`x(i)_r = ∏_{p ≠ r} x_{pr}(i_p)`. The factors commute, so both are well defined, and both ignore
the `r`-th coordinate. This file proves:

* `rowProd`, `colProd`: `x_r(j)` and `x(i)_r`, additive in `j` and `i` (`rowProd_add`,
  `colProd_add`), with `x_r(ε_q b) = x_{rq}(b)` and `x(ε_p b)_r = x_{pr}(b)` for `p, q ≠ r`;
* `eq_of_add_of_single`: two additive maps `(I → A) → G` that agree on the vectors `Pi.single s b`
  are equal. This replaces vdK's word manipulations;
* `mat_rowProd`, `mat_colProd`: `π(x_r(j)) = 1 + ε_r j'` and `π(x(i)_r) = 1 + i' ε_rᵀ`, where
  `j'` and `i'` have the `r`-th coordinate set to zero;
* **vdK's "well known fact"** (3.7): `conj_rowProd` — if `z` is a product of generators with
  column index `≠ r` and `j_r = 0`, then `z x_r(j) z⁻¹ = x_r(j π(z)⁻¹)`; `conj_colProd` — if `y`
  is a product of generators with row index `≠ r` and `i_r = 0`, then `y x(i)_r y⁻¹ = x(π(y) i)_r`.

Nothing here assumes that a column is unimodular.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false

namespace GroupApproximation
namespace BooneHigmanLinear
namespace K2Found
namespace VdK

open scoped commutatorElement Matrix
open GroupApproximation.SteinbergGroup

variable {I A : Type*} [Fintype I] [DecidableEq I] [CommRing A]

/-! ### Matrices of Steinberg elements -/

/-- `π(z)` as a matrix. -/
abbrev mat (z : SteinbergGroup I A) : Matrix I I A :=
  (((projection z : elementaryGroup I A) : (Matrix I I A)ˣ) : Matrix I I A)

/-- `π(z)⁻¹` as a matrix. -/
abbrev matInv (z : SteinbergGroup I A) : Matrix I I A :=
  ((((projection z : elementaryGroup I A) : (Matrix I I A)ˣ)⁻¹ : (Matrix I I A)ˣ) : Matrix I I A)

theorem mat_one : mat (1 : SteinbergGroup I A) = 1 := by
  simp only [mat, map_one, OneMemClass.coe_one, Units.val_one]

theorem matInv_one : matInv (1 : SteinbergGroup I A) = 1 := by
  simp only [matInv, map_one, OneMemClass.coe_one, inv_one, Units.val_one]

theorem mat_mul (z w : SteinbergGroup I A) : mat (z * w) = mat z * mat w := by
  simp only [mat, map_mul, Subgroup.coe_mul, Units.val_mul]

theorem matInv_mul (z w : SteinbergGroup I A) : matInv (z * w) = matInv w * matInv z := by
  simp only [matInv, map_mul, Subgroup.coe_mul, mul_inv_rev, Units.val_mul]

theorem mat_inv (z : SteinbergGroup I A) : mat z⁻¹ = matInv z := by
  simp only [mat, matInv, map_inv, Subgroup.coe_inv]

theorem matInv_inv (z : SteinbergGroup I A) : matInv z⁻¹ = mat z := by
  simp only [mat, matInv, map_inv, Subgroup.coe_inv, inv_inv]

theorem mat_mul_matInv (z : SteinbergGroup I A) : mat z * matInv z = 1 :=
  Units.mul_inv _

theorem matInv_mul_mat (z : SteinbergGroup I A) : matInv z * mat z = 1 :=
  Units.inv_mul _

theorem mat_x (p q : I) (h : p ≠ q) (a : A) : mat (x p q h a) = 1 + Matrix.single p q a := by
  rw [mat, projection_x]
  rfl

theorem matInv_x (p q : I) (h : p ≠ q) (a : A) : matInv (x p q h a) = 1 - Matrix.single p q a := by
  rw [matInv, projection_x]
  rfl

omit [Fintype I] in
/-- `Pi.single p a ⊗ Pi.single q c = a c E_pq`. -/
theorem vecMulVec_single_single' (p q : I) (a c : A) :
    Matrix.vecMulVec (Pi.single p a) (Pi.single q c) = Matrix.single p q (a * c) := by
  ext r s
  rw [Matrix.vecMulVec_apply, Matrix.single_apply]
  rcases eq_or_ne r p with rfl | hr
  · rcases eq_or_ne s q with rfl | hs
    · rw [Pi.single_eq_same, Pi.single_eq_same, if_pos ⟨rfl, rfl⟩]
    · rw [Pi.single_eq_of_ne hs, mul_zero, if_neg (fun h => hs h.2.symm)]
  · rw [Pi.single_eq_of_ne hr, zero_mul, if_neg (fun h => hr h.1.symm)]

omit [Fintype I] in
/-- `a E_pq = (a ε_p) ε_qᵀ`. -/
theorem single_eq_vecMulVec_right (p q : I) (a : A) :
    Matrix.single p q a = Matrix.vecMulVec (Pi.single p a) (Pi.single q (1 : A)) := by
  rw [vecMulVec_single_single', mul_one]

/-- If `M ε_r = ε_r`, then `(v M)_r = v_r`. -/
theorem vecMul_apply_of_mulVec_single {M : Matrix I I A} {r : I}
    (hM : M *ᵥ Pi.single r (1 : A) = Pi.single r 1) (v : I → A) : (v ᵥ* M) r = v r := by
  have h1 : (v ᵥ* M) r = (v ᵥ* M) ⬝ᵥ Pi.single r (1 : A) := by rw [dotProduct_single, mul_one]
  rw [h1, ← Matrix.dotProduct_mulVec, hM, dotProduct_single, mul_one]

/-- If `ε_rᵀ M = ε_rᵀ`, then `(M v)_r = v_r`. -/
theorem mulVec_apply_of_single_vecMul {M : Matrix I I A} {r : I}
    (hM : Pi.single r (1 : A) ᵥ* M = Pi.single r 1) (v : I → A) : (M *ᵥ v) r = v r := by
  have h1 : (M *ᵥ v) r = Pi.single r (1 : A) ⬝ᵥ (M *ᵥ v) := by rw [single_dotProduct, one_mul]
  rw [h1, Matrix.dotProduct_mulVec, hM, single_dotProduct, one_mul]

/-! ### Additive maps out of `I → A` -/

/-- Two maps `(I → A) → G` that turn sums into products and agree on every `Pi.single s b` are
equal. -/
theorem eq_of_add_of_single {G : Type*} [Group G] {f g : (I → A) → G}
    (hf : ∀ u v, f (u + v) = f u * f v) (hg : ∀ u v, g (u + v) = g u * g v)
    (hs : ∀ (s : I) (b : A), f (Pi.single s b) = g (Pi.single s b)) (u : I → A) : f u = g u := by
  have hf0 : f 0 = 1 := by
    have h := hf 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := f 0) (by rw [mul_one]; exact h.symm)
  have hg0 : g 0 = 1 := by
    have h := hg 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := g 0) (by rw [mul_one]; exact h.symm)
  have key : ∀ S : Finset I,
      f (∑ s ∈ S, Pi.single s (u s)) = g (∑ s ∈ S, Pi.single s (u s)) := by
    intro S
    refine Finset.induction_on S (by rw [Finset.sum_empty, hf0, hg0]) ?_
    intro s S hsS ih
    rw [Finset.sum_insert hsS, hf, hg, ih, hs]
  have h := key Finset.univ
  rwa [Finset.univ_sum_single] at h

/-! ### Row and column products -/

/-- `x_ij` as a monoid homomorphism out of `Multiplicative A`. -/
def xHom (i j : I) (hij : i ≠ j) : Multiplicative A →* SteinbergGroup I A where
  toFun a := x i j hij (Multiplicative.toAdd a)
  map_one' := x_zero i j hij
  map_mul' a b := (x_mul i j hij _ _).symm

@[simp] theorem xHom_apply (i j : I) (hij : i ≠ j) (a : Multiplicative A) :
    xHom i j hij a = x i j hij (Multiplicative.toAdd a) :=
  rfl

/-- The `(r, s)` factor of `x_r(·)`: `x_{rs}` for `s ≠ r`, trivial for `s = r`. -/
def rowPiece (r s : I) : Multiplicative A →* SteinbergGroup I A :=
  if h : r = s then 1 else xHom r s h

/-- The `(p, r)` factor of `x(·)_r`: `x_{pr}` for `p ≠ r`, trivial for `p = r`. -/
def colPiece (r p : I) : Multiplicative A →* SteinbergGroup I A :=
  if h : p = r then 1 else xHom p r h

theorem rowPiece_commute (r : I) :
    Pairwise fun s t => ∀ a b, Commute (rowPiece (A := A) r s a) (rowPiece r t b) := by
  intro s t _ a b
  by_cases hs : r = s
  · simp only [rowPiece, dif_pos hs, MonoidHom.one_apply]
    exact Commute.one_left _
  by_cases ht : r = t
  · simp only [rowPiece, dif_pos ht, MonoidHom.one_apply]
    exact Commute.one_right _
  simp only [rowPiece, dif_neg hs, dif_neg ht, xHom_apply]
  exact x_commute_of_ne r s r t hs ht (Ne.symm hs) (Ne.symm ht) _ _

theorem colPiece_commute (r : I) :
    Pairwise fun p p' => ∀ a b, Commute (colPiece (A := A) r p a) (colPiece r p' b) := by
  intro p p' _ a b
  by_cases hp : p = r
  · simp only [colPiece, dif_pos hp, MonoidHom.one_apply]
    exact Commute.one_left _
  by_cases hp' : p' = r
  · simp only [colPiece, dif_pos hp', MonoidHom.one_apply]
    exact Commute.one_right _
  simp only [colPiece, dif_neg hp, dif_neg hp', xHom_apply]
  exact x_commute_of_ne p r p' r hp hp' (Ne.symm hp') (Ne.symm hp) _ _

/-- vdK's `x_r(j) = ∏_{q ≠ r} x_{rq}(j_q)`. -/
def rowProd (r : I) (j : I → A) : SteinbergGroup I A :=
  MonoidHom.noncommPiCoprod (rowPiece r) (rowPiece_commute r) (fun s => Multiplicative.ofAdd (j s))

/-- vdK's `x(i)_r = ∏_{p ≠ r} x_{pr}(i_p)`. -/
def colProd (r : I) (i : I → A) : SteinbergGroup I A :=
  MonoidHom.noncommPiCoprod (colPiece r) (colPiece_commute r) (fun p => Multiplicative.ofAdd (i p))

theorem rowProd_add (r : I) (j k : I → A) : rowProd r (j + k) = rowProd r j * rowProd r k := by
  unfold rowProd
  rw [← map_mul]
  rfl

theorem colProd_add (r : I) (i k : I → A) : colProd r (i + k) = colProd r i * colProd r k := by
  unfold colProd
  rw [← map_mul]
  rfl

theorem rowProd_zero (r : I) : rowProd r (0 : I → A) = 1 := by
  unfold rowProd
  exact map_one _

theorem colProd_zero (r : I) : colProd r (0 : I → A) = 1 := by
  unfold colProd
  exact map_one _

omit [Fintype I] in
theorem ofAdd_single (s : I) (b : A) :
    (fun t => Multiplicative.ofAdd ((Pi.single s b : I → A) t)) =
      Pi.mulSingle s (Multiplicative.ofAdd b) := by
  funext t
  by_cases ht : t = s
  · subst ht
    rw [Pi.single_eq_same, Pi.mulSingle_eq_same]
  · rw [Pi.single_eq_of_ne ht, Pi.mulSingle_eq_of_ne ht, ofAdd_zero]

theorem rowProd_single_ne (r s : I) (h : r ≠ s) (b : A) : rowProd r (Pi.single s b) = x r s h b := by
  unfold rowProd
  rw [ofAdd_single, MonoidHom.noncommPiCoprod_mulSingle, rowPiece, dif_neg h, xHom_apply,
    toAdd_ofAdd]

theorem rowProd_single_self (r : I) (b : A) : rowProd r (Pi.single r b) = 1 := by
  unfold rowProd
  rw [ofAdd_single, MonoidHom.noncommPiCoprod_mulSingle, rowPiece, dif_pos rfl,
    MonoidHom.one_apply]

theorem colProd_single_ne (r p : I) (h : p ≠ r) (b : A) : colProd r (Pi.single p b) = x p r h b := by
  unfold colProd
  rw [ofAdd_single, MonoidHom.noncommPiCoprod_mulSingle, colPiece, dif_neg h, xHom_apply,
    toAdd_ofAdd]

theorem colProd_single_self (r : I) (b : A) : colProd r (Pi.single r b) = 1 := by
  unfold colProd
  rw [ofAdd_single, MonoidHom.noncommPiCoprod_mulSingle, colPiece, dif_pos rfl,
    MonoidHom.one_apply]

/-- `x_r(j)` ignores `j_r`. -/
theorem rowProd_sub_single_self (r : I) (j : I → A) (c : A) :
    rowProd r (j - Pi.single r c) = rowProd r j := by
  rw [sub_eq_add_neg, ← Pi.single_neg, rowProd_add, rowProd_single_self, mul_one]

/-- `x(i)_r` ignores `i_r`. -/
theorem colProd_sub_single_self (r : I) (i : I → A) (c : A) :
    colProd r (i - Pi.single r c) = colProd r i := by
  rw [sub_eq_add_neg, ← Pi.single_neg, colProd_add, colProd_single_self, mul_one]

/-! ### `π(x_r(j))` and `π(x(i)_r)` -/

theorem eUnit_congr {v w w' : I → A} (hw : w = w') (h : w ⬝ᵥ v = 0) (h' : w' ⬝ᵥ v = 0) :
    eUnit v w h = eUnit v w' h' := by
  subst hw
  rfl

theorem eUnit_congr_left {v v' w : I → A} (hv : v = v') (h : w ⬝ᵥ v = 0) (h' : w ⬝ᵥ v' = 0) :
    eUnit v w h = eUnit v' w h' := by
  subst hv
  rfl

theorem eUnit_zero_right (v : I → A) (h : (0 : I → A) ⬝ᵥ v = 0) : eUnit v 0 h = 1 := by
  apply Units.ext
  rw [eUnit_val, Matrix.vecMulVec_zero, add_zero, Units.val_one]

theorem eUnit_zero_left (w : I → A) (h : w ⬝ᵥ (0 : I → A) = 0) : eUnit 0 w h = 1 := by
  apply Units.ext
  rw [eUnit_val, Matrix.zero_vecMulVec, add_zero, Units.val_one]

/-- `j - j_r ε_r` is killed by `ε_r`. -/
theorem sub_single_dotProduct_single (r : I) (j : I → A) :
    (j - Pi.single r (j r)) ⬝ᵥ Pi.single r (1 : A) = 0 := by
  rw [dotProduct_single, Pi.sub_apply, Pi.single_eq_same, sub_self, zero_mul]

theorem single_dotProduct_sub_single (r : I) (i : I → A) :
    Pi.single r (1 : A) ⬝ᵥ (i - Pi.single r (i r)) = 0 := by
  rw [single_dotProduct, Pi.sub_apply, Pi.single_eq_same, sub_self, mul_zero]

omit [Fintype I] in
theorem sub_single_add (r : I) (u v : I → A) :
    u + v - Pi.single r ((u + v) r) = (u - Pi.single r (u r)) + (v - Pi.single r (v r)) := by
  rw [Pi.add_apply, Pi.single_add]
  abel

/-- `1 + ε_r j'` with `j' = j - j_r ε_r`: the matrix of `x_r(j)`. -/
def rowE (r : I) (j : I → A) : (Matrix I I A)ˣ :=
  eUnit (Pi.single r 1) (j - Pi.single r (j r)) (sub_single_dotProduct_single r j)

/-- `1 + i' ε_rᵀ` with `i' = i - i_r ε_r`: the matrix of `x(i)_r`. -/
def colE (r : I) (i : I → A) : (Matrix I I A)ˣ :=
  eUnit (i - Pi.single r (i r)) (Pi.single r 1) (single_dotProduct_sub_single r i)

theorem rowE_single_self (r : I) (b : A) : rowE r (Pi.single r b) = 1 := by
  apply Units.ext
  show 1 + Matrix.vecMulVec (Pi.single r (1 : A)) (Pi.single r b - Pi.single r (Pi.single r b r)) = 1
  rw [Pi.single_eq_same, sub_self, Matrix.vecMulVec_zero, add_zero]

theorem colE_single_self (r : I) (b : A) : colE r (Pi.single r b) = 1 := by
  apply Units.ext
  show 1 + Matrix.vecMulVec (Pi.single r b - Pi.single r (Pi.single r b r)) (Pi.single r (1 : A)) = 1
  rw [Pi.single_eq_same, sub_self, Matrix.zero_vecMulVec, add_zero]

theorem rowE_val_single_ne {r s : I} (h : r ≠ s) (b : A) :
    ((rowE r (Pi.single s b) : (Matrix I I A)ˣ) : Matrix I I A) = 1 + Matrix.single r s b := by
  show 1 + Matrix.vecMulVec (Pi.single r (1 : A)) (Pi.single s b - Pi.single r (Pi.single s b r)) =
    1 + Matrix.single r s b
  rw [Pi.single_eq_of_ne h, Pi.single_zero, sub_zero, vecMulVec_single_single]

theorem colE_val_single_ne {r p : I} (h : p ≠ r) (b : A) :
    ((colE r (Pi.single p b) : (Matrix I I A)ˣ) : Matrix I I A) = 1 + Matrix.single p r b := by
  show 1 + Matrix.vecMulVec (Pi.single p b - Pi.single r (Pi.single p b r)) (Pi.single r (1 : A)) =
    1 + Matrix.single p r b
  rw [Pi.single_eq_of_ne (Ne.symm h), Pi.single_zero, sub_zero, vecMulVec_single_single', mul_one]

theorem rowE_add (r : I) (u v : I → A) : rowE r (u + v) = rowE r u * rowE r v := by
  rw [rowE, rowE, rowE, eUnit_mul (Pi.single r 1) (u - Pi.single r (u r)) (v - Pi.single r (v r))
    (sub_single_dotProduct_single r u) (sub_single_dotProduct_single r v) (by
      rw [add_dotProduct, sub_single_dotProduct_single, sub_single_dotProduct_single, add_zero])]
  exact eUnit_congr (sub_single_add r u v) _ _

/-- vdK's first relation for `e` in its column form: `e(u, w) e(v, w) = e(u + v, w)` if `w u = 0`
and `w v = 0` (here `(u v)² = 0` because `w v = 0`). -/
theorem eUnit_mul_left (u v w : I → A) (hu : w ⬝ᵥ u = 0) (hv : w ⬝ᵥ v = 0)
    (huv : w ⬝ᵥ (u + v) = 0) : eUnit u w hu * eUnit v w hv = eUnit (u + v) w huv := by
  apply Units.ext
  change (1 + Matrix.vecMulVec u w) * (1 + Matrix.vecMulVec v w) = 1 + Matrix.vecMulVec (u + v) w
  have hx : Matrix.vecMulVec u w * Matrix.vecMulVec v w = 0 := by
    rw [Matrix.vecMulVec_mul_vecMulVec, hv, zero_smul, Matrix.vecMulVec_zero]
  rw [Matrix.add_vecMulVec, add_mul, one_mul, mul_add, mul_one, hx, add_zero]
  abel

theorem colE_add (r : I) (u v : I → A) : colE r (u + v) = colE r u * colE r v := by
  rw [colE, colE, colE, eUnit_mul_left (u - Pi.single r (u r)) (v - Pi.single r (v r))
    (Pi.single r 1) (single_dotProduct_sub_single r u) (single_dotProduct_sub_single r v) (by
      rw [dotProduct_add, single_dotProduct_sub_single, single_dotProduct_sub_single, add_zero])]
  exact eUnit_congr_left (sub_single_add r u v) _ _

/-- `π(x_r(j)) = 1 + ε_r j'`. -/
theorem mat_rowProd (r : I) (j : I → A) :
    ((projection (rowProd r j) : elementaryGroup I A) : (Matrix I I A)ˣ) = rowE r j := by
  refine eq_of_add_of_single (f := fun j => ((projection (rowProd r j) : elementaryGroup I A) :
    (Matrix I I A)ˣ)) (g := rowE r) (fun u v => ?_) (fun u v => rowE_add r u v) (fun s b => ?_) j
  · show ((projection (rowProd r (u + v)) : elementaryGroup I A) : (Matrix I I A)ˣ) =
      ((projection (rowProd r u) : elementaryGroup I A) : (Matrix I I A)ˣ) *
        ((projection (rowProd r v) : elementaryGroup I A) : (Matrix I I A)ˣ)
    rw [rowProd_add, map_mul, Subgroup.coe_mul]
  · show ((projection (rowProd r (Pi.single s b)) : elementaryGroup I A) : (Matrix I I A)ˣ) =
      rowE r (Pi.single s b)
    by_cases hs : r = s
    · subst hs
      rw [rowProd_single_self, map_one, OneMemClass.coe_one, rowE_single_self]
    · rw [rowProd_single_ne r s hs, projection_x]
      apply Units.ext
      rw [rowE_val_single_ne hs]
      rfl

#audit_axioms mat_rowProd

/-- `π(x(i)_r) = 1 + i' ε_rᵀ`. -/
theorem mat_colProd (r : I) (i : I → A) :
    ((projection (colProd r i) : elementaryGroup I A) : (Matrix I I A)ˣ) = colE r i := by
  refine eq_of_add_of_single (f := fun i => ((projection (colProd r i) : elementaryGroup I A) :
    (Matrix I I A)ˣ)) (g := colE r) (fun u v => ?_) (fun u v => colE_add r u v) (fun p b => ?_) i
  · show ((projection (colProd r (u + v)) : elementaryGroup I A) : (Matrix I I A)ˣ) =
      ((projection (colProd r u) : elementaryGroup I A) : (Matrix I I A)ˣ) *
        ((projection (colProd r v) : elementaryGroup I A) : (Matrix I I A)ˣ)
    rw [colProd_add, map_mul, Subgroup.coe_mul]
  · show ((projection (colProd r (Pi.single p b)) : elementaryGroup I A) : (Matrix I I A)ˣ) =
      colE r (Pi.single p b)
    by_cases hp : p = r
    · subst hp
      rw [colProd_single_self, map_one, OneMemClass.coe_one, colE_single_self]
    · rw [colProd_single_ne r p hp, projection_x]
      apply Units.ext
      rw [colE_val_single_ne hp]
      rfl

#audit_axioms mat_colProd

/-! ### Conjugation by single generators -/

/-- `x_pq(a) x_rp(b) x_pq(a)⁻¹ = x_rp(b) x_rq(-(b a))` for distinct `r, p, q`. -/
theorem x_conj_x_left (p q r : I) (hpq : p ≠ q) (hrp : r ≠ p) (hrq : r ≠ q) (a b : A) :
    x p q hpq a * x r p hrp b * (x p q hpq a)⁻¹ = x r p hrp b * x r q hrq (-(b * a)) := by
  have hc := x_commutator r p q hrp hpq hrq (-b) a
  rw [x_neg, neg_mul] at hc
  calc x p q hpq a * x r p hrp b * (x p q hpq a)⁻¹
      = x r p hrp b * ⁅(x r p hrp b)⁻¹, x p q hpq a⁆ := by rw [commutatorElement_def]; group
    _ = x r p hrp b * x r q hrq (-(b * a)) := by rw [hc]

/-- `x_pq(a) x_qr(b) x_pq(a)⁻¹ = x_pr(a b) x_qr(b)` for distinct `p, q, r`. -/
theorem x_conj_x_right (p q r : I) (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r) (a b : A) :
    x p q hpq a * x q r hqr b * (x p q hpq a)⁻¹ = x p r hpr (a * b) * x q r hqr b := by
  rw [← x_commutator p q r hpq hqr hpr a b, commutatorElement_def]
  group

theorem x_conj_x_of_commute {p q r s : I} (hpq : p ≠ q) (hrs : r ≠ s) (hqr : q ≠ r)
    (hsp : s ≠ p) (a b : A) : x p q hpq a * x r s hrs b * (x p q hpq a)⁻¹ = x r s hrs b := by
  rw [(x_commute_of_ne p q r s hpq hrs hqr hsp a b).eq, mul_inv_cancel_right]

/-! ### vdK's "well known fact" for row products -/

variable (I A) in
/-- The subgroup generated by the `x_pq(a)` with column index `q ≠ r`. -/
def colAvoid (r : I) : Subgroup (SteinbergGroup I A) :=
  Subgroup.closure {g | ∃ (p q : I) (hpq : p ≠ q) (a : A), q ≠ r ∧ x p q hpq a = g}

/-- The statement of vdK's fact for rows, for a single `z`. -/
def RowConj (r : I) (z : SteinbergGroup I A) : Prop :=
  mat z *ᵥ Pi.single r (1 : A) = Pi.single r 1 ∧
    ∀ j : I → A, z * rowProd r j * z⁻¹ = rowProd r ((j - Pi.single r (j r)) ᵥ* matInv z)

theorem matInv_mulVec_single {r : I} {z : SteinbergGroup I A}
    (h : mat z *ᵥ Pi.single r (1 : A) = Pi.single r 1) :
    matInv z *ᵥ Pi.single r (1 : A) = Pi.single r 1 := by
  conv_lhs => rw [← h]
  rw [Matrix.mulVec_mulVec, matInv_mul_mat, Matrix.one_mulVec]

theorem rowConj_x {r : I} (p q : I) (hpq : p ≠ q) (a : A) (hqr : q ≠ r) :
    RowConj r (x p q hpq a) := by
  refine ⟨?_, fun j => ?_⟩
  · rw [mat_x, Matrix.add_mulVec, Matrix.one_mulVec, single_eq_vecMulVec_right p q a,
      Matrix.vecMulVec_mulVec, single_dotProduct, Pi.single_eq_of_ne hqr, mul_zero,
      MulOpposite.op_zero, zero_smul, add_zero]
  rw [matInv_x]
  refine eq_of_add_of_single (f := fun j => x p q hpq a * rowProd r j * (x p q hpq a)⁻¹)
    (g := fun j => rowProd r ((j - Pi.single r (j r)) ᵥ* (1 - Matrix.single p q a)))
    (fun u v => ?_) (fun u v => ?_) (fun s b => ?_) j
  · show x p q hpq a * rowProd r (u + v) * (x p q hpq a)⁻¹ =
      x p q hpq a * rowProd r u * (x p q hpq a)⁻¹ * (x p q hpq a * rowProd r v * (x p q hpq a)⁻¹)
    rw [rowProd_add]
    group
  · show rowProd r ((u + v - Pi.single r ((u + v) r)) ᵥ* (1 - Matrix.single p q a)) =
      rowProd r ((u - Pi.single r (u r)) ᵥ* (1 - Matrix.single p q a)) *
        rowProd r ((v - Pi.single r (v r)) ᵥ* (1 - Matrix.single p q a))
    rw [sub_single_add, Matrix.add_vecMul, rowProd_add]
  · show x p q hpq a * rowProd r (Pi.single s b) * (x p q hpq a)⁻¹ =
      rowProd r ((Pi.single s b - Pi.single r (Pi.single s b r)) ᵥ* (1 - Matrix.single p q a))
    by_cases hs : r = s
    · subst hs
      rw [rowProd_single_self, mul_one, mul_inv_cancel, Pi.single_eq_same, sub_self,
        Matrix.zero_vecMul, rowProd_zero]
    · rw [Pi.single_eq_of_ne hs, Pi.single_zero, sub_zero, Matrix.vecMul_sub, Matrix.vecMul_one,
        ← vecMulVec_single_single p q a, Matrix.vecMul_vecMulVec, single_dotProduct,
        rowProd_single_ne r s hs]
      by_cases hsp : s = p
      · subst hsp
        rw [Pi.single_eq_same, mul_one, ← Pi.single_smul', smul_eq_mul, sub_eq_add_neg,
          ← Pi.single_neg, rowProd_add, rowProd_single_ne r s hs,
          rowProd_single_ne r q (Ne.symm hqr)]
        exact x_conj_x_left s q r hpq hs (Ne.symm hqr) a b
      · rw [Pi.single_eq_of_ne hsp, mul_zero, zero_smul, sub_zero, rowProd_single_ne r s hs]
        exact x_conj_x_of_commute hpq hs hqr hsp a b

theorem rowConj_one (r : I) : RowConj r (1 : SteinbergGroup I A) := by
  refine ⟨by rw [mat_one, Matrix.one_mulVec], fun j => ?_⟩
  rw [one_mul, inv_one, mul_one, matInv_one, Matrix.vecMul_one, rowProd_sub_single_self]

theorem rowConj_mul {r : I} {z w : SteinbergGroup I A} (hz : RowConj r z) (hw : RowConj r w) :
    RowConj r (z * w) := by
  refine ⟨by rw [mat_mul, ← Matrix.mulVec_mulVec, hw.1, hz.1], fun j => ?_⟩
  have hj2 : ((j - Pi.single r (j r)) ᵥ* matInv w) r = 0 := by
    rw [vecMul_apply_of_mulVec_single (matInv_mulVec_single hw.1), Pi.sub_apply,
      Pi.single_eq_same, sub_self]
  calc z * w * rowProd r j * (z * w)⁻¹ = z * (w * rowProd r j * w⁻¹) * z⁻¹ := by group
    _ = z * rowProd r ((j - Pi.single r (j r)) ᵥ* matInv w) * z⁻¹ := by rw [hw.2 j]
    _ = rowProd r ((j - Pi.single r (j r)) ᵥ* matInv (z * w)) := by
      rw [hz.2, hj2, Pi.single_zero, sub_zero, Matrix.vecMul_vecMul, matInv_mul]

theorem rowConj_inv {r : I} {z : SteinbergGroup I A} (hz : RowConj r z) : RowConj r z⁻¹ := by
  refine ⟨by rw [mat_inv]; exact matInv_mulVec_single hz.1, fun j => ?_⟩
  have hj' : ((j - Pi.single r (j r)) ᵥ* mat z) r = 0 := by
    rw [vecMul_apply_of_mulVec_single hz.1, Pi.sub_apply, Pi.single_eq_same, sub_self]
  have h := hz.2 ((j - Pi.single r (j r)) ᵥ* mat z)
  rw [hj', Pi.single_zero, sub_zero, Matrix.vecMul_vecMul, mat_mul_matInv, Matrix.vecMul_one,
    rowProd_sub_single_self] at h
  rw [matInv_inv, ← h]
  group

theorem rowConj_of_mem_colAvoid {r : I} {z : SteinbergGroup I A} (hz : z ∈ colAvoid I A r) :
    RowConj r z := by
  induction hz using Subgroup.closure_induction with
  | mem g hg =>
      obtain ⟨p, q, hpq, a, hqr, rfl⟩ := hg
      exact rowConj_x p q hpq a hqr
  | one => exact rowConj_one r
  | mul _ _ _ _ hz hw => exact rowConj_mul hz hw
  | inv _ _ hz => exact rowConj_inv hz

/-- **vdK 3.7, "well known fact" (rows).** If `z` is a product of generators with column index
different from `r` and `j_r = 0`, then `z x_r(j) z⁻¹ = x_r(j π(z)⁻¹)`. -/
theorem conj_rowProd {r : I} {z : SteinbergGroup I A} (hz : z ∈ colAvoid I A r) {j : I → A}
    (hj : j r = 0) : z * rowProd r j * z⁻¹ = rowProd r (j ᵥ* matInv z) := by
  rw [(rowConj_of_mem_colAvoid hz).2 j, hj, Pi.single_zero, sub_zero]

#audit_axioms conj_rowProd

/-! ### vdK's "well known fact" for column products -/

variable (I A) in
/-- The subgroup generated by the `x_pq(a)` with row index `p ≠ r`. -/
def rowAvoid (r : I) : Subgroup (SteinbergGroup I A) :=
  Subgroup.closure {g | ∃ (p q : I) (hpq : p ≠ q) (a : A), p ≠ r ∧ x p q hpq a = g}

/-- The statement of vdK's fact for columns, for a single `y`. -/
def ColConj (r : I) (y : SteinbergGroup I A) : Prop :=
  Pi.single r (1 : A) ᵥ* mat y = Pi.single r 1 ∧
    ∀ i : I → A, y * colProd r i * y⁻¹ = colProd r (mat y *ᵥ (i - Pi.single r (i r)))

theorem single_vecMul_matInv {r : I} {y : SteinbergGroup I A}
    (h : Pi.single r (1 : A) ᵥ* mat y = Pi.single r 1) :
    Pi.single r (1 : A) ᵥ* matInv y = Pi.single r 1 := by
  conv_lhs => rw [← h]
  rw [Matrix.vecMul_vecMul, mat_mul_matInv, Matrix.vecMul_one]

theorem colConj_x {r : I} (p q : I) (hpq : p ≠ q) (a : A) (hpr : p ≠ r) :
    ColConj r (x p q hpq a) := by
  refine ⟨?_, fun i => ?_⟩
  · rw [mat_x, Matrix.vecMul_add, Matrix.vecMul_one, ← vecMulVec_single_single p q a,
      Matrix.vecMul_vecMulVec, single_dotProduct, Pi.single_eq_of_ne (Ne.symm hpr), mul_zero,
      zero_smul, add_zero]
  rw [mat_x]
  refine eq_of_add_of_single (f := fun i => x p q hpq a * colProd r i * (x p q hpq a)⁻¹)
    (g := fun i => colProd r ((1 + Matrix.single p q a) *ᵥ (i - Pi.single r (i r))))
    (fun u v => ?_) (fun u v => ?_) (fun s b => ?_) i
  · show x p q hpq a * colProd r (u + v) * (x p q hpq a)⁻¹ =
      x p q hpq a * colProd r u * (x p q hpq a)⁻¹ * (x p q hpq a * colProd r v * (x p q hpq a)⁻¹)
    rw [colProd_add]
    group
  · show colProd r ((1 + Matrix.single p q a) *ᵥ (u + v - Pi.single r ((u + v) r))) =
      colProd r ((1 + Matrix.single p q a) *ᵥ (u - Pi.single r (u r))) *
        colProd r ((1 + Matrix.single p q a) *ᵥ (v - Pi.single r (v r)))
    rw [sub_single_add, Matrix.mulVec_add, colProd_add]
  · show x p q hpq a * colProd r (Pi.single s b) * (x p q hpq a)⁻¹ =
      colProd r ((1 + Matrix.single p q a) *ᵥ (Pi.single s b - Pi.single r (Pi.single s b r)))
    by_cases hs : s = r
    · subst hs
      rw [colProd_single_self, mul_one, mul_inv_cancel, Pi.single_eq_same, sub_self,
        Matrix.mulVec_zero, colProd_zero]
    · rw [Pi.single_eq_of_ne (Ne.symm hs), Pi.single_zero, sub_zero, Matrix.add_mulVec,
        Matrix.one_mulVec, single_eq_vecMulVec_right p q a, Matrix.vecMulVec_mulVec,
        single_dotProduct, colProd_single_ne r s hs]
      by_cases hsq : s = q
      · subst hsq
        rw [Pi.single_eq_same, one_mul, op_smul_eq_smul, ← Pi.single_smul', smul_eq_mul,
          colProd_add, colProd_single_ne r s hs, colProd_single_ne r p hpr, mul_comm b a,
          (x_commute_of_ne s r p r hs hpr (Ne.symm hpr) (Ne.symm hs) b (a * b)).eq]
        exact x_conj_x_right p s r hpq hs hpr a b
      · rw [Pi.single_eq_of_ne (Ne.symm hsq), mul_zero, MulOpposite.op_zero, zero_smul, add_zero,
          colProd_single_ne r s hs]
        exact x_conj_x_of_commute hpq hs (Ne.symm hsq) (Ne.symm hpr) a b

theorem colConj_one (r : I) : ColConj r (1 : SteinbergGroup I A) := by
  refine ⟨by rw [mat_one, Matrix.vecMul_one], fun i => ?_⟩
  rw [one_mul, inv_one, mul_one, mat_one, Matrix.one_mulVec, colProd_sub_single_self]

theorem colConj_mul {r : I} {y w : SteinbergGroup I A} (hy : ColConj r y) (hw : ColConj r w) :
    ColConj r (y * w) := by
  refine ⟨by rw [mat_mul, ← Matrix.vecMul_vecMul, hy.1, hw.1], fun i => ?_⟩
  have hi2 : (mat w *ᵥ (i - Pi.single r (i r))) r = 0 := by
    rw [mulVec_apply_of_single_vecMul hw.1, Pi.sub_apply, Pi.single_eq_same, sub_self]
  calc y * w * colProd r i * (y * w)⁻¹ = y * (w * colProd r i * w⁻¹) * y⁻¹ := by group
    _ = y * colProd r (mat w *ᵥ (i - Pi.single r (i r))) * y⁻¹ := by rw [hw.2 i]
    _ = colProd r (mat (y * w) *ᵥ (i - Pi.single r (i r))) := by
      rw [hy.2, hi2, Pi.single_zero, sub_zero, Matrix.mulVec_mulVec, mat_mul]

theorem colConj_inv {r : I} {y : SteinbergGroup I A} (hy : ColConj r y) : ColConj r y⁻¹ := by
  refine ⟨by rw [mat_inv]; exact single_vecMul_matInv hy.1, fun i => ?_⟩
  have hi' : (matInv y *ᵥ (i - Pi.single r (i r))) r = 0 := by
    rw [mulVec_apply_of_single_vecMul (single_vecMul_matInv hy.1), Pi.sub_apply,
      Pi.single_eq_same, sub_self]
  have h := hy.2 (matInv y *ᵥ (i - Pi.single r (i r)))
  rw [hi', Pi.single_zero, sub_zero, Matrix.mulVec_mulVec, mat_mul_matInv, Matrix.one_mulVec,
    colProd_sub_single_self] at h
  rw [mat_inv, ← h]
  group

theorem colConj_of_mem_rowAvoid {r : I} {y : SteinbergGroup I A} (hy : y ∈ rowAvoid I A r) :
    ColConj r y := by
  induction hy using Subgroup.closure_induction with
  | mem g hg =>
      obtain ⟨p, q, hpq, a, hpr, rfl⟩ := hg
      exact colConj_x p q hpq a hpr
  | one => exact colConj_one r
  | mul _ _ _ _ hy hw => exact colConj_mul hy hw
  | inv _ _ hy => exact colConj_inv hy

/-- **vdK 3.7, "well known fact" (columns).** If `y` is a product of generators with row index
different from `r` and `i_r = 0`, then `y x(i)_r y⁻¹ = x(π(y) i)_r`. -/
theorem conj_colProd {r : I} {y : SteinbergGroup I A} (hy : y ∈ rowAvoid I A r) {i : I → A}
    (hi : i r = 0) : y * colProd r i * y⁻¹ = colProd r (mat y *ᵥ i) := by
  rw [(colConj_of_mem_rowAvoid hy).2 i, hi, Pi.single_zero, sub_zero]

#audit_axioms conj_colProd

end VdK
end K2Found
end BooneHigmanLinear
end GroupApproximation
