import Mathlib.Algebra.Polynomial.Eval.Defs
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2OneVarNilCube
import GroupApproximation.Meta.AxiomGuard

/-!
# Substitutions on `B[t][y]` for the Quillen patching of the nil part of `K₂`

Lane `bh-met-46`, helper module.  Let `B` be a commutative ring, `P = B[t]` and `Q = P[y] = B[t][y]`.
Four ring maps, all fixing `B`:

* `quillenShift B a : P → Q`, `t ↦ t + a y`;
* `quillenScale B c : Q → Q`, `y ↦ c y`, fixing `P`;
* `quillenTranslate B b : Q → Q`, `t ↦ t + b y`, `y ↦ y`;
* `quillenCollapse B : Q → P`, `t ↦ 0`, `y ↦ t`.

Their values on the constants and on the variables are recorded here.  The composition identities
used by the patching argument are in `ElemFPK2LocalQuillenComp`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

section QuillenMaps

variable {B : Type*} [CommRing B]

variable (B) in
/-- `quillenShift B a : B[t] → B[t][y]`, `t ↦ t + a y`. -/
noncomputable def quillenShift (a : B) : Polynomial B →+* Polynomial (Polynomial B) :=
  Polynomial.eval₂RingHom
    (RingHom.comp (Polynomial.C : Polynomial B →+* Polynomial (Polynomial B))
      (Polynomial.C : B →+* Polynomial B))
    (Polynomial.C Polynomial.X + Polynomial.C (Polynomial.C a) * Polynomial.X)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.quillenShift

variable (B) in
/-- `quillenScale B c : B[t][y] → B[t][y]`, `y ↦ c y`, fixing `B[t]`. -/
noncomputable def quillenScale (c : B) :
    Polynomial (Polynomial B) →+* Polynomial (Polynomial B) :=
  Polynomial.eval₂RingHom (Polynomial.C : Polynomial B →+* Polynomial (Polynomial B))
    (Polynomial.C (Polynomial.C c) * Polynomial.X)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.quillenScale

variable (B) in
/-- `quillenTranslate B b : B[t][y] → B[t][y]`, `t ↦ t + b y`, `y ↦ y`. -/
noncomputable def quillenTranslate (b : B) :
    Polynomial (Polynomial B) →+* Polynomial (Polynomial B) :=
  Polynomial.eval₂RingHom (quillenShift B b) Polynomial.X

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.quillenTranslate

variable (B) in
/-- `quillenCollapse B : B[t][y] → B[t]`, `t ↦ 0`, `y ↦ t`. -/
noncomputable def quillenCollapse : Polynomial (Polynomial B) →+* Polynomial B :=
  Polynomial.eval₂RingHom
    (RingHom.comp (Polynomial.C : B →+* Polynomial B)
      (Polynomial.evalRingHom 0 : Polynomial B →+* B))
    Polynomial.X

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.quillenCollapse

theorem quillenShift_C (a b : B) :
    quillenShift B a (Polynomial.C b) = Polynomial.C (Polynomial.C b) := by
  rw [quillenShift, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, RingHom.comp_apply]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.quillenShift_C

theorem quillenShift_X (a : B) :
    quillenShift B a Polynomial.X =
      Polynomial.C Polynomial.X + Polynomial.C (Polynomial.C a) * Polynomial.X := by
  rw [quillenShift, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.quillenShift_X

theorem quillenScale_C (c : B) (f : Polynomial B) :
    quillenScale B c (Polynomial.C f) = Polynomial.C f := by
  rw [quillenScale, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.quillenScale_C

theorem quillenScale_X (c : B) :
    quillenScale B c Polynomial.X = Polynomial.C (Polynomial.C c) * Polynomial.X := by
  rw [quillenScale, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.quillenScale_X

theorem quillenTranslate_C (b : B) (f : Polynomial B) :
    quillenTranslate B b (Polynomial.C f) = quillenShift B b f := by
  rw [quillenTranslate, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.quillenTranslate_C

theorem quillenTranslate_X (b : B) :
    quillenTranslate B b Polynomial.X = Polynomial.X := by
  rw [quillenTranslate, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.quillenTranslate_X

theorem quillenCollapse_C (f : Polynomial B) :
    quillenCollapse B (Polynomial.C f) = Polynomial.C (Polynomial.eval 0 f) := by
  rw [quillenCollapse, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, RingHom.comp_apply,
    Polynomial.coe_evalRingHom]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.quillenCollapse_C

theorem quillenCollapse_X :
    quillenCollapse B Polynomial.X = (Polynomial.X : Polynomial B) := by
  rw [quillenCollapse, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.quillenCollapse_X

end QuillenMaps

end GroupApproximation.BooneHigman.Metabelian.ElemFP
