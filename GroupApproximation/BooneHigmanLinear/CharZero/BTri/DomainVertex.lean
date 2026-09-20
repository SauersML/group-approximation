import GroupApproximation.BooneHigmanLinear.CharZero.BTri.DomainType
import GroupApproximation.Meta.AxiomGuard

/-!
# Z.3, part 2: vertex types and the classification of vertices

Lane `fix-bh-a`, piece Z.3 (board `k2-poly.md`).  Built on `BTri/Action.lean`
(bh-pal-linear-char0) and `BTri/DomainType.lean`.

* `vertexOf_mul_map`, `vertexOf_scalar_zpow`: a vertex does not change under right multiplication
  by `GL₃(A)` or under scaling by `p^c`, `c ∈ ℤ`.
* `vertexType_smul`: `γ ∈ GL₃(B)` shifts the type by `v_p(det γ)`.  So `SL₃(B)` preserves types
  (`vertexType_sl_smul`).
* `detVal_stdMat` and `vertexType_std`: the standard vertices `[1]`, `[diag(1,1,p)]` and
  `[diag(1,p,p)]` have types `0, 1, 2`.
* **`exists_sl_smul_eq_std`**: every vertex `x` is `SL₃(B)`-equivalent to the standard vertex of
  its type.  **`eq_of_sl_smul_std`**: distinct standard vertices are not `SL₃(B)`-equivalent.
  Together, `{stdVertex 0, stdVertex 1, stdVertex 2}` is a set of orbit representatives for
  the vertices, indexed by type.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace BTri

open scoped Pointwise
open Matrix

section General

variable {A : Type*} [CommRing A] [IsDomain A] {B : Type*} [CommRing B] [Algebra A B]
  {p : A} [IsLocalization.Away p B]

theorem vertexOf_eq_of_latOf_eq {g h : GL (Fin 3) B} (e : latOf A B g = latOf A B h) :
    vertexOf A B p g = vertexOf A B p h :=
  Quotient.sound (show Homothetic A B p g h from ⟨0, 0, by rw [pow_zero, one_smul, one_smul, e]⟩)

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.vertexOf_eq_of_latOf_eq

theorem vertexOf_mul_map (g : GL (Fin 3) B) (k : GL (Fin 3) A) :
    vertexOf A B p (g * Matrix.GeneralLinearGroup.map (algebraMap A B) k) = vertexOf A B p g :=
  vertexOf_eq_of_latOf_eq (latOf_mul_map g k)

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.vertexOf_mul_map

theorem vertexOf_scalar_pow (a : ℕ) (g : GL (Fin 3) B) :
    vertexOf A B p (Matrix.GeneralLinearGroup.scalar (Fin 3) (pU (B := B) p ^ a) * g) =
      vertexOf A B p g :=
  Quotient.sound (show Homothetic A B p _ _ from ⟨0, a, by rw [pow_zero, one_smul, smul_latOf]⟩)

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.vertexOf_scalar_pow

/-- Scaling by `p^c`, `c ∈ ℤ`, does not move a vertex. -/
theorem vertexOf_scalar_zpow (c : ℤ) (g : GL (Fin 3) B) :
    vertexOf A B p (Matrix.GeneralLinearGroup.scalar (Fin 3) (pU (B := B) p ^ c) * g) =
      vertexOf A B p g := by
  obtain ⟨a, rfl | rfl⟩ := Int.eq_nat_or_neg c
  · rw [zpow_natCast]
    exact vertexOf_scalar_pow a g
  · have h := vertexOf_scalar_pow (p := p) a
      (Matrix.GeneralLinearGroup.scalar (Fin 3) (pU (B := B) p ^ (-(a : ℤ))) * g)
    rw [← mul_assoc, ← map_mul, ← zpow_natCast, ← zpow_add, add_neg_cancel, zpow_zero, map_one,
      one_mul] at h
    exact h.symm

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.vertexOf_scalar_zpow

/-- `γ ∈ GL₃(B)` shifts the type by `v_p(det γ)`. -/
theorem vertexType_smul (hp : Prime p) (γ : GL (Fin 3) B) (x : Vertex A B p) :
    vertexType hp (γ • x) = vertexType hp x + ((detVal hp γ : ℤ) : ZMod 3) := by
  refine Quotient.inductionOn x fun g => ?_
  change vertexType hp (vertexOf A B p (γ * g)) = vertexType hp (vertexOf A B p g) + _
  rw [vertexType_vertexOf, vertexType_vertexOf, detVal_mul]
  push_cast
  ring

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.vertexType_smul

theorem detVal_toGL (hp : Prime p) (γ : Matrix.SpecialLinearGroup (Fin 3) B) :
    detVal hp (Matrix.SpecialLinearGroup.toGL γ) = 0 := by
  unfold detVal
  rw [Matrix.SpecialLinearGroup.coeToGL_det]
  exact pval_eq hp (v := 1) (by rw [map_one, one_mul, zpow_zero])

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.detVal_toGL

/-- **`SL₃(B)` preserves types.** -/
theorem vertexType_sl_smul (hp : Prime p) (γ : Matrix.SpecialLinearGroup (Fin 3) B)
    (x : Vertex A B p) : vertexType hp (γ • x) = vertexType hp x := by
  rw [sl_smul_def, vertexType_smul, detVal_toGL, Int.cast_zero, add_zero]

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.vertexType_sl_smul

end General

section Std

variable {A : Type*} [CommRing A] [IsDomain A] {p : A}

theorem pUnit_eq_pU : pUnit A p = pU (B := Localization.Away p) p :=
  rfl

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.pUnit_eq_pU

/-- The exponents of `p` on the diagonals of the standard matrices. -/
def stdExp : Fin 3 → Fin 3 → ℕ :=
  ![![0, 0, 0], ![0, 0, 1], ![0, 1, 1]]

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.stdExp

theorem coe_stdMat (i : Fin 3) :
    (stdMat A p i : Matrix (Fin 3) (Fin 3) (Localization.Away p)) =
      diagonal fun k => algebraMap A (Localization.Away p) p ^ stdExp i k := by
  have hp1 : ((pUnit A p : (Localization.Away p)ˣ) : Localization.Away p) =
      algebraMap A (Localization.Away p) p := IsUnit.unit_spec _
  fin_cases i
  · ext r c
    fin_cases r <;> fin_cases c <;> simp [stdMat, stdExp, Matrix.one_apply, Matrix.diagonal_apply]
  · ext r c
    fin_cases r <;> fin_cases c <;> simp [stdMat, stdExp, dgUnit, hp1, Matrix.diagonal_apply]
  · ext r c
    fin_cases r <;> fin_cases c <;> simp [stdMat, stdExp, dgUnit, hp1, Matrix.diagonal_apply]

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.coe_stdMat

theorem stdExp_sum (i : Fin 3) : ∑ k, stdExp i k = i.val := by
  fin_cases i <;> simp [stdExp, Fin.sum_univ_three] <;> rfl

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.stdExp_sum

theorem det_stdMat (i : Fin 3) :
    Matrix.GeneralLinearGroup.det (stdMat A p i) = pU (B := Localization.Away p) p ^ i.val := by
  apply Units.ext
  change Matrix.det (stdMat A p i : Matrix (Fin 3) (Fin 3) (Localization.Away p)) = _
  rw [coe_stdMat, Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum, stdExp_sum,
    Units.val_pow_eq_pow_val, coe_pU]

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.det_stdMat

theorem detVal_stdMat (hp : Prime p) (i : Fin 3) : detVal hp (stdMat A p i) = i.val := by
  unfold detVal
  rw [det_stdMat, ← zpow_natCast, pval_pU_pow]

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.detVal_stdMat

/-- **Types of the standard vertices**: `stdVertex i` has type `i`. -/
theorem vertexType_std (hp : Prime p) (i : Fin 3) :
    vertexType hp (stdVertex A p i) = (i.val : ZMod 3) := by
  rw [stdVertex, vertexType_vertexOf, detVal_stdMat]
  exact Int.cast_natCast _

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.vertexType_std

/-- The standard index of a type. -/
def stdOfType (t : ZMod 3) : Fin 3 :=
  ⟨t.val, ZMod.val_lt t⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.stdOfType

theorem stdOfType_natCast (i : Fin 3) : stdOfType (i.val : ZMod 3) = i := by
  apply Fin.ext
  simp only [stdOfType, ZMod.val_natCast]
  exact Nat.mod_eq_of_lt i.isLt

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.stdOfType_natCast

/-- An element of `GL₃` with determinant one, as an element of `SL₃`. -/
def slOfGL {R : Type*} [CommRing R] (γ : GL (Fin 3) R) (h : Matrix.GeneralLinearGroup.det γ = 1) :
    Matrix.SpecialLinearGroup (Fin 3) R :=
  ⟨(γ : Matrix (Fin 3) (Fin 3) R), congrArg Units.val h⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.slOfGL

theorem toGL_slOfGL {R : Type*} [CommRing R] (γ : GL (Fin 3) R)
    (h : Matrix.GeneralLinearGroup.det γ = 1) : Matrix.SpecialLinearGroup.toGL (slOfGL γ h) = γ :=
  Matrix.GeneralLinearGroup.ext fun _ _ => rfl

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.toGL_slOfGL

/-- The unit `diag(v, 1, 1)` of `M₃(A)`, of determinant `v`. -/
def firstUnit (v : Aˣ) : GL (Fin 3) A :=
  dgUnit ![v, 1, 1]

theorem det_firstUnit (v : Aˣ) : Matrix.GeneralLinearGroup.det (firstUnit v) = v := by
  apply Units.ext
  change Matrix.det (Matrix.diagonal fun k => ((![v, 1, 1] k : Aˣ) : A)) = v
  rw [Matrix.det_diagonal, Fin.prod_univ_three]
  simp

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.det_firstUnit

/-- **Vertex classification (existence)**: every vertex is `SL₃(B)`-equivalent to the standard
vertex of its type. -/
theorem exists_sl_smul_eq_std (hp : Prime p) (x : Vertex A (Localization.Away p) p) :
    ∃ γ : Matrix.SpecialLinearGroup (Fin 3) (Localization.Away p),
      γ • x = stdVertex A p (stdOfType (vertexType hp x)) := by
  refine Quotient.inductionOn x fun g => ?_
  change ∃ γ : Matrix.SpecialLinearGroup (Fin 3) (Localization.Away p),
    γ • vertexOf A _ p g = stdVertex A p (stdOfType (vertexType hp (vertexOf A _ p g)))
  set i := stdOfType (vertexType hp (vertexOf A (Localization.Away p) p g)) with hi
  -- `detVal g = i + 3 c`
  have hcong : ((detVal hp g : ℤ) : ZMod 3) = ((i.val : ℤ) : ZMod 3) := by
    have : ((i.val : ℕ) : ZMod 3) = vertexType hp (vertexOf A (Localization.Away p) p g) := by
      rw [hi, stdOfType]
      exact ZMod.natCast_zmod_val (vertexType hp (vertexOf A (Localization.Away p) p g))
    rw [vertexType_vertexOf] at this
    rw [← this]
    exact (Int.cast_natCast _).symm
  obtain ⟨c, hc⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 3).mp hcong
  -- `h = p^c g` has `detVal h = i`
  set h : GL (Fin 3) (Localization.Away p) :=
    Matrix.GeneralLinearGroup.scalar (Fin 3) (pU (B := Localization.Away p) p ^ c) * g with hh
  have hvh : detVal hp h = i.val := by
    rw [hh, detVal_mul]
    unfold detVal
    rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, ← zpow_natCast, ← zpow_mul,
      pval_pU_pow]
    change (c * ((3 : ℕ) : ℤ)) + detVal hp g = i.val
    push_cast at hc ⊢
    linarith
  -- fix the unit part of `det h`
  set v := (exists_unit_decomp hp (Matrix.GeneralLinearGroup.det h)).choose with hv
  have hdet : Matrix.GeneralLinearGroup.det h = unitsMap v * pU (B := Localization.Away p) p ^
      (i.val : ℤ) := by
    have := pval_spec hp (Matrix.GeneralLinearGroup.det h)
    rw [← hv] at this
    change _ = unitsMap v * pU (B := Localization.Away p) p ^ detVal hp h at this
    rwa [hvh] at this
  set h' := h * Matrix.GeneralLinearGroup.map (algebraMap A (Localization.Away p)) (firstUnit v⁻¹)
    with hh'
  have hdet' : Matrix.GeneralLinearGroup.det h' = pU (B := Localization.Away p) p ^ i.val := by
    have hm : Matrix.GeneralLinearGroup.det
        (Matrix.GeneralLinearGroup.map (algebraMap A (Localization.Away p)) (firstUnit v⁻¹)) =
          unitsMap v⁻¹ := by
      apply Units.ext
      change Matrix.det (((firstUnit v⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A).map
        (algebraMap A (Localization.Away p))) = algebraMap A _ ((v⁻¹ : Aˣ) : A)
      exact (RingHom.map_det _ _).symm.trans
        (congrArg (algebraMap A (Localization.Away p)) (congrArg Units.val (det_firstUnit v⁻¹)))
    rw [hh', map_mul, hdet, hm, zpow_natCast]
    rw [mul_comm (unitsMap v) _, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
  have hvert : vertexOf A (Localization.Away p) p h' = vertexOf A (Localization.Away p) p g := by
    rw [hh', vertexOf_mul_map, hh, vertexOf_scalar_zpow]
  -- `γ = D_i h'⁻¹`
  have hγ : Matrix.GeneralLinearGroup.det (stdMat A p i * h'⁻¹) = 1 := by
    rw [map_mul, map_inv, det_stdMat, hdet', mul_inv_cancel]
  refine ⟨slOfGL _ hγ, ?_⟩
  rw [sl_smul_def, toGL_slOfGL, ← hvert, smul_vertexOf, inv_mul_cancel_right]
  rfl

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.exists_sl_smul_eq_std

/-- **Vertex classification (uniqueness)**: `SL₃(B)` does not identify distinct standard
vertices. -/
theorem eq_of_sl_smul_std (hp : Prime p) {i j : Fin 3}
    {γ : Matrix.SpecialLinearGroup (Fin 3) (Localization.Away p)}
    (h : γ • stdVertex A p i = stdVertex A p j) : i = j := by
  have := congrArg (vertexType hp) h
  rw [vertexType_sl_smul, vertexType_std, vertexType_std] at this
  calc i = stdOfType (i.val : ZMod 3) := (stdOfType_natCast i).symm
    _ = stdOfType (j.val : ZMod 3) := by rw [this]
    _ = j := stdOfType_natCast j

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.eq_of_sl_smul_std

end Std

end BTri
end BooneHigmanLinear
end GroupApproximation
