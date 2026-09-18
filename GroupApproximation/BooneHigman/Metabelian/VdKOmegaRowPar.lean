import GroupApproximation.BooneHigman.Metabelian.VdKParPresTilde
import GroupApproximation.Meta.AxiomGuard

/-!
# The amalgam route, part 1: the opposite parabolic `R^n ⋊ St_n(R)` (row version)

Lane `bh-met-92j`.  Everything here is unconditional, for every commutative `R` and every `n`.

* `vdkOmega_rowAct`: `St_n(R)` acts on row vectors `R^n` (written multiplicatively) by
  `w ↦ w M_g⁻¹`.  Because of the inverse this is a *left* action.
* `vdkOmega_TildeMinus n R := R^n ⋊ St_n(R)`, the abstract opposite parabolic `P̃⁻`.
* `vdkOmega_PiMinus : P̃⁻ →* St_{n+1}(R)`, `(w, g) ↦ rowVec w · stab g`.  It is
  `SemidirectProduct.lift` of `rowVec` and `stab`, and the one compatibility is
  `stab_conj_rowVec`.
* `vdkOmega_Pi_inl_single`, `vdkOmega_PiMinus_inl_single`: on unit vectors, `Π` and `Π⁻` give
  the roots `x_{i,last}(a)` and `x_{last,k}(b)`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
  (colRoot rowRoot rowVec rowVec_add rowVec_zero colVec_update_zero rowVec_update_zero
    projectionMatrix projectionMatrix_mul projectionMatrix_one stab_conj_rowVec)
open scoped Matrix

variable {n : ℕ} {R : Type*} [CommRing R]

/-- The automorphism `w ↦ w M_g⁻¹` of row vectors `R^n`, written multiplicatively. -/
def vdkOmega_rowAut (g : St n R) : MulAut (Multiplicative (Fin n → R)) where
  toFun v := Multiplicative.ofAdd (v.toAdd ᵥ* projectionMatrix g⁻¹)
  invFun v := Multiplicative.ofAdd (v.toAdd ᵥ* projectionMatrix g)
  left_inv v := by
    change Multiplicative.ofAdd (v.toAdd ᵥ* projectionMatrix g⁻¹ ᵥ* projectionMatrix g) = v
    rw [Matrix.vecMul_vecMul, ← projectionMatrix_mul, inv_mul_cancel, projectionMatrix_one,
      Matrix.vecMul_one, ofAdd_toAdd]
  right_inv v := by
    change Multiplicative.ofAdd (v.toAdd ᵥ* projectionMatrix g ᵥ* projectionMatrix g⁻¹) = v
    rw [Matrix.vecMul_vecMul, ← projectionMatrix_mul, mul_inv_cancel, projectionMatrix_one,
      Matrix.vecMul_one, ofAdd_toAdd]
  map_mul' a b := by
    change Multiplicative.ofAdd ((a.toAdd + b.toAdd) ᵥ* projectionMatrix g⁻¹) =
      Multiplicative.ofAdd (a.toAdd ᵥ* projectionMatrix g⁻¹) *
        Multiplicative.ofAdd (b.toAdd ᵥ* projectionMatrix g⁻¹)
    rw [Matrix.add_vecMul, ofAdd_add]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmega_rowAut

/-- The left action of `St_n(R)` on row vectors, `w ↦ w M_g⁻¹`. -/
def vdkOmega_rowAct : St n R →* MulAut (Multiplicative (Fin n → R)) where
  toFun := vdkOmega_rowAut
  map_one' := by
    refine MulEquiv.ext fun v ↦ ?_
    change Multiplicative.ofAdd (v.toAdd ᵥ* projectionMatrix (1 : St n R)⁻¹) = v
    rw [inv_one, projectionMatrix_one, Matrix.vecMul_one, ofAdd_toAdd]
  map_mul' g h := by
    refine MulEquiv.ext fun v ↦ ?_
    change Multiplicative.ofAdd (v.toAdd ᵥ* projectionMatrix (g * h)⁻¹) =
      Multiplicative.ofAdd (v.toAdd ᵥ* projectionMatrix h⁻¹ ᵥ* projectionMatrix g⁻¹)
    rw [Matrix.vecMul_vecMul, ← projectionMatrix_mul, mul_inv_rev]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmega_rowAct

variable (n R) in
/-- The abstract opposite parabolic `P̃⁻ = R^n ⋊ St_n(R)` (row vectors). -/
abbrev vdkOmega_TildeMinus : Type _ :=
  SemidirectProduct (Multiplicative (Fin n → R)) (St n R) (vdkOmega_rowAct (n := n) (R := R))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmega_TildeMinus

/-- The `St_n(R)` factor of `P̃⁻`. -/
def vdkOmega_inrMinus : St n R →* vdkOmega_TildeMinus n R :=
  SemidirectProduct.inr

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmega_inrMinus

/-- `rowVec` as a homomorphism out of `R^n`, written multiplicatively. -/
def vdkOmega_rowHom : Multiplicative (Fin n → R) →* St (n + 1) R where
  toFun v := rowVec v.toAdd
  map_one' := rowVec_zero
  map_mul' a b := rowVec_add a.toAdd b.toAdd

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmega_rowHom

/-- The compatibility of `rowVec` and `stab` with the row action: `stab_conj_rowVec`. -/
theorem vdkOmega_compatMinus (g : St n R) :
    vdkOmega_rowHom.comp (vdkOmega_rowAct g).toMonoidHom =
      (MulAut.conj (stab n R g)).toMonoidHom.comp vdkOmega_rowHom := by
  refine MonoidHom.ext fun v ↦ ?_
  change rowVec (v.toAdd ᵥ* projectionMatrix g⁻¹) =
    stab n R g * rowVec v.toAdd * (stab n R g)⁻¹
  rw [stab_conj_rowVec]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmega_compatMinus

/-- The canonical map `Π⁻ : P̃⁻ →* St_{n+1}(R)`, `(w, g) ↦ rowVec w · stab g`. -/
def vdkOmega_PiMinus : vdkOmega_TildeMinus n R →* St (n + 1) R :=
  SemidirectProduct.lift vdkOmega_rowHom (stab n R) vdkOmega_compatMinus

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmega_PiMinus

theorem vdkOmega_PiMinus_inr (g : St n R) :
    vdkOmega_PiMinus (vdkOmega_inrMinus g) = stab n R g :=
  SemidirectProduct.lift_inr vdkOmega_rowHom (stab n R) vdkOmega_compatMinus g

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmega_PiMinus_inr

/-- `Π⁻` sends the unit row vector `b e_k` to the root `x_{last,k}(b)`. -/
theorem vdkOmega_PiMinus_inl_single (k : Fin n) (b : R) :
    vdkOmega_PiMinus (SemidirectProduct.inl (Multiplicative.ofAdd (Pi.single k b))) =
      rowRoot k b :=
  (SemidirectProduct.lift_inl vdkOmega_rowHom (stab n R) vdkOmega_compatMinus
    (Multiplicative.ofAdd (Pi.single k b))).trans
    (rowVec_update_zero k b)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmega_PiMinus_inl_single

/-- `Π` sends the unit column vector `a e_i` to the root `x_{i,last}(a)`. -/
theorem vdkOmega_Pi_inl_single (i : Fin n) (a : R) :
    vdkParPres_Pi (SemidirectProduct.inl (Multiplicative.ofAdd (Pi.single i a))) =
      colRoot i a :=
  (SemidirectProduct.lift_inl vdkParPres_colHom (stab n R) vdkParPres_compat
    (Multiplicative.ofAdd (Pi.single i a))).trans
    (colVec_update_zero i a)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmega_Pi_inl_single

end GroupApproximation.BooneHigman.Metabelian.ElemFP
