import Mathlib.Data.Matrix.Basis
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwoRootSpan
import GroupApproximation.Meta.AxiomGuard

/-!
# The vector action of a Steinberg group (lane sk-leavitt-23)

`act g v` is the column vector `projection g *ᵥ v`.  A root acts by
`act (x_ij(a)) v k = v k + [k = i] a v_j`.  Two consequences:

* if no generating root of `rootSpan p` has row `k`, the span fixes coordinate `k`;
* if every generating root `x_ij` of `rootSpan p` has `w j = 0`, the span fixes `w`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo

open GroupApproximation.SteinbergGroup
open scoped Matrix

variable {I R : Type*} [Fintype I] [DecidableEq I] [Ring R]

/-- The action of `St_I(R)` on column vectors through the elementary projection. -/
def act (g : SteinbergGroup I R) (v : I → R) : I → R :=
  ((projection g : (Matrix I I R)ˣ) : Matrix I I R) *ᵥ v

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.act

theorem act_mul (g h : SteinbergGroup I R) (v : I → R) :
    act (g * h) v = act g (act h v) := by
  simp only [act, map_mul, Subgroup.coe_mul, Units.val_mul, Matrix.mulVec_mulVec]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.act_mul

theorem act_one (v : I → R) : act (1 : SteinbergGroup I R) v = v := by
  simp only [act, map_one, Subgroup.coe_one, Units.val_one, Matrix.one_mulVec]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.act_one

theorem act_of_projection_eq_one {g : SteinbergGroup I R} (hg : projection g = 1)
    (v : I → R) : act g v = v := by
  simp only [act, hg, Subgroup.coe_one, Units.val_one, Matrix.one_mulVec]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.act_of_projection_eq_one

theorem act_x_apply (i j : I) (h : i ≠ j) (a : R) (v : I → R) (k : I) :
    act (x i j h a) v k = v k + if k = i then a * v j else 0 := by
  simp only [act, projection_x, elementaryRoot_val]
  show ((1 + Matrix.single i j a) *ᵥ v) k = _
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec, Pi.add_apply,
    Function.update_apply, Pi.zero_apply]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.act_x_apply

/-- The standard basis vector `e_k`. -/
def unitVec (k : I) : I → R := fun m => if m = k then 1 else 0

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.unitVec

theorem unitVec_apply (k m : I) : unitVec (R := R) k m = if m = k then 1 else 0 := rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.unitVec_apply

/-- If no generating root of `rootSpan p` has row `k`, the span fixes coordinate `k`. -/
theorem act_apply_of_rootSpan {p : I → I → Prop} {k : I} (hk : ∀ i j, p i j → i ≠ k)
    {g : SteinbergGroup I R} (hg : g ∈ rootSpan (R := R) p) (v : I → R) :
    act g v k = v k := by
  refine (rootSpan_induction (Q := fun g => ∀ v : I → R, act g v k = v k) ?_ ?_ ?_ hg) v
  · intro i j h a hp v
    rw [act_x_apply, if_neg (hk i j hp).symm, add_zero]
  · intro v
    rw [act_one]
  · intro g g' _ _ h1 h2 v
    show act (g * g') v k = v k
    rw [act_mul, h1, h2]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.act_apply_of_rootSpan

/-- If every generating root `x_ij` of `rootSpan p` has `w j = 0`, the span fixes `w`. -/
theorem act_eq_self_of_rootSpan {p : I → I → Prop} {w : I → R}
    (hw : ∀ i j, p i j → w j = 0)
    {g : SteinbergGroup I R} (hg : g ∈ rootSpan (R := R) p) : act g w = w := by
  refine rootSpan_induction (Q := fun g => act g w = w) ?_ (act_one w) ?_ hg
  · intro i j h a hp
    show act (x i j h a) w = w
    funext k
    rw [act_x_apply, hw i j hp, mul_zero, ite_self, add_zero]
  · intro g g' _ _ h1 h2
    show act (g * g') w = w
    rw [act_mul, h2, h1]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.act_eq_self_of_rootSpan

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo
