import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.Basic
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.RingTheory.TwoSidedIdeal.Kernel
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import GroupApproximation.Meta.AxiomGuard

/-!
# `C_2 / (p) ≅ L_k(1,2)`

Lane `sk-leavitt-18`, second module.

In a noncommutative ring the quotient by `Ideal.span` needs a two-sidedness
instance, so the ideal `I = (p)` is taken as `TwoSidedIdeal.span {p}` and the
quotient is `I.ringCon.Quotient`.

Route.
* `quotientToLeavitt`: `toLeavitt` kills `p`, hence all of `I`, and descends
  (`RingCon.liftₐ`).
* `leavittToQuotient`: the Cohn relations hold in `C_2 / I` by construction and
  `ee* + ff* = 1` holds because `1 - (ee* + ff*) = p ∈ I` (`RingQuot.liftAlgHom`).
* Both composites are the identity on generators (`RingCon.Quotient.hom_extₐ`,
  `RingQuot.ringQuot_ext'`, `FreeAlgebra.hom_ext`).
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

namespace CohnTwo

variable (k : Type*) [Field k]

/-- The two-sided ideal `I = (p)` of `C_2`. -/
abbrev pIdeal : TwoSidedIdeal (CohnTwo k) := TwoSidedIdeal.span {cohnP k}

theorem pIdeal_le_ker : pIdeal k ≤ TwoSidedIdeal.ker (toLeavitt k) := by
  refine TwoSidedIdeal.span_le.mpr ?_
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact (TwoSidedIdeal.mem_ker (toLeavitt k)).mpr (toLeavitt_p k)

theorem pIdeal_ringCon_le : (pIdeal k).ringCon ≤ RingCon.ker (toLeavitt k).toRingHom := by
  refine RingCon.le_def.mpr ?_
  intro x y h
  rw [RingCon.ker_apply]
  have hxy : x - y ∈ pIdeal k := (TwoSidedIdeal.rel_iff (pIdeal k) x y).mp h
  have h0 := (TwoSidedIdeal.mem_ker (toLeavitt k)).mp (pIdeal_le_ker k hxy)
  rw [map_sub, sub_eq_zero] at h0
  exact h0

/-- `C_2 / I → L_k(1,2)`. -/
def quotientToLeavitt :
    (pIdeal k).ringCon.Quotient →ₐ[k] BinaryLeavitt.BinaryLeavittAlgebra k :=
  RingCon.liftₐ (pIdeal k).ringCon (toLeavitt k) (pIdeal_ringCon_le k)

theorem quotientToLeavitt_mk (x : CohnTwo k) :
    quotientToLeavitt k ((pIdeal k).ringCon.mkₐ k x) = toLeavitt k x := rfl

theorem mk_eq_mk_of_sub_mem {x y : CohnTwo k} (h : x - y ∈ pIdeal k) :
    (pIdeal k).ringCon.mkₐ k x = (pIdeal k).ringCon.mkₐ k y :=
  (RingCon.eq (pIdeal k).ringCon).mpr ((TwoSidedIdeal.rel_iff (pIdeal k) x y).mpr h)

theorem leavittToQuotient_respects :
    ∀ ⦃x y : BinaryLeavitt.Free k⦄, BinaryLeavitt.Relation k x y →
      ((pIdeal k).ringCon.mkₐ k).comp (quotientMap k) x =
        ((pIdeal k).ringCon.mkₐ k).comp (quotientMap k) y := by
  intro x y h
  rw [AlgHom.comp_apply, AlgHom.comp_apply]
  cases h
  · exact congrArg ((pIdeal k).ringCon.mkₐ k)
      (RingQuot.mkAlgHom_rel k (CohnRelation.t0_s0 (k := k)))
  · exact congrArg ((pIdeal k).ringCon.mkₐ k)
      (RingQuot.mkAlgHom_rel k (CohnRelation.t0_s1 (k := k)))
  · exact congrArg ((pIdeal k).ringCon.mkₐ k)
      (RingQuot.mkAlgHom_rel k (CohnRelation.t1_s0 (k := k)))
  · exact congrArg ((pIdeal k).ringCon.mkₐ k)
      (RingQuot.mkAlgHom_rel k (CohnRelation.t1_s1 (k := k)))
  · refine mk_eq_mk_of_sub_mem k ?_
    have hp : cohnP k ∈ pIdeal k := TwoSidedIdeal.subset_span (Set.mem_singleton _)
    have hneg := TwoSidedIdeal.neg_mem (pIdeal k) hp
    have heq : quotientMap k
        (FreeAlgebra.ι k BinaryLeavitt.s0 * FreeAlgebra.ι k BinaryLeavitt.t0 +
          FreeAlgebra.ι k BinaryLeavitt.s1 * FreeAlgebra.ι k BinaryLeavitt.t1) -
          quotientMap k 1 = -cohnP k := by
      rw [cohnP_eq, sub_sub, neg_sub, map_add, map_mul, map_mul, map_one]
      rfl
    rw [heq]
    exact hneg

/-- `L_k(1,2) → C_2 / I`. -/
def leavittToQuotient :
    BinaryLeavitt.BinaryLeavittAlgebra k →ₐ[k] (pIdeal k).ringCon.Quotient :=
  RingQuot.liftAlgHom k
    ⟨((pIdeal k).ringCon.mkₐ k).comp (quotientMap k), leavittToQuotient_respects k⟩

theorem leavittToQuotient_quotientMap (x : BinaryLeavitt.Free k) :
    leavittToQuotient k (BinaryLeavitt.quotientMap k x) =
      (pIdeal k).ringCon.mkₐ k (quotientMap k x) :=
  RingQuot.liftAlgHom_mkAlgHom_apply k _ (leavittToQuotient_respects k) x

theorem quotientToLeavitt_comp_leavittToQuotient :
    (quotientToLeavitt k).comp (leavittToQuotient k) =
      AlgHom.id k (BinaryLeavitt.BinaryLeavittAlgebra k) := by
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext g
  change quotientToLeavitt k
      (leavittToQuotient k (BinaryLeavitt.quotientMap k (FreeAlgebra.ι k g))) =
    BinaryLeavitt.quotientMap k (FreeAlgebra.ι k g)
  rw [leavittToQuotient_quotientMap, quotientToLeavitt_mk, toLeavitt_quotientMap]

theorem leavittToQuotient_comp_quotientToLeavitt :
    (leavittToQuotient k).comp (quotientToLeavitt k) =
      AlgHom.id k (pIdeal k).ringCon.Quotient := by
  apply RingCon.Quotient.hom_extₐ
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext g
  change leavittToQuotient k
      (quotientToLeavitt k ((pIdeal k).ringCon.mkₐ k (quotientMap k (FreeAlgebra.ι k g)))) =
    (pIdeal k).ringCon.mkₐ k (quotientMap k (FreeAlgebra.ι k g))
  rw [quotientToLeavitt_mk, toLeavitt_quotientMap, leavittToQuotient_quotientMap]

/-- The algebra isomorphism `C_2 / (p) ≃ₐ L_k(1,2)`. -/
def quotientAlgEquiv :
    (pIdeal k).ringCon.Quotient ≃ₐ[k] BinaryLeavitt.BinaryLeavittAlgebra k :=
  AlgEquiv.ofAlgHom (quotientToLeavitt k) (leavittToQuotient k)
    (quotientToLeavitt_comp_leavittToQuotient k) (leavittToQuotient_comp_quotientToLeavitt k)

end CohnTwo

/-- **Lane endpoint.** `C_2 / (p) ≃+* L_k(1,2)`, with `(p)` the two-sided ideal
generated by `p = 1 - ee* - ff*`. -/
def cohnTwo_quotient_equiv (k : Type*) [Field k] :
    (CohnTwo.pIdeal k).ringCon.Quotient ≃+* BinaryLeavitt.BinaryLeavittAlgebra k :=
  (CohnTwo.quotientAlgEquiv k).toRingEquiv

theorem cohnTwo_quotient_equiv_mk (k : Type*) [Field k] (x : CohnTwo k) :
    cohnTwo_quotient_equiv k ((CohnTwo.pIdeal k).ringCon.mkₐ k x) = CohnTwo.toLeavitt k x :=
  rfl

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.pIdeal
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.pIdeal_le_ker
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.pIdeal_ringCon_le
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.quotientToLeavitt
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.quotientToLeavitt_mk
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.mk_eq_mk_of_sub_mem
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.leavittToQuotient_respects
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.leavittToQuotient
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.leavittToQuotient_quotientMap
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.quotientToLeavitt_comp_leavittToQuotient
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.leavittToQuotient_comp_quotientToLeavitt
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.quotientAlgEquiv
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.cohnTwo_quotient_equiv
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.cohnTwo_quotient_equiv_mk
