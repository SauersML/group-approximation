import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVSkewLaurentK2.HalfUltraRev

/-!
# The backward map `t ↦ t⁻¹` (lane sk-lv-03, part 2)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii; `frontier/SK.md`,
section 2b, items 10-11.  This file defines the ring map
`skHalfK2_bwd S : (skHalfK2_Rev S)[t,t⁻¹] →+* S[t,t⁻¹;φ]`, `a t^g ↦ a t^{-g}`, which is
inverse to `skHalfK2_fwd S` (`HalfUltraEquiv.lean`).
-/

namespace GroupApproximation.Full.LVSkewLaurentK2

section Backward

variable (S : Type*) [Ring S] [MulSemiringAction (Multiplicative ℤ) S]

/-- The constants of the backward map, `a ↦ a t⁰`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def skHalfK2_bwdConst : skHalfK2_Rev S →+* SkewLaurent S :=
  (SkewMonoidAlgebra.singleOneRingHom (k := S) (G := Multiplicative ℤ)).comp
    (skHalfK2_toRevRingEquiv S).symm.toRingHom

#audit_axioms GroupApproximation.Full.LVSkewLaurentK2.skHalfK2_bwdConst

/-- Values of `skHalfK2_bwdConst`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skHalfK2_bwdConst_apply (a : skHalfK2_Rev S) :
    skHalfK2_bwdConst S a = SkewMonoidAlgebra.single 1 ((skHalfK2_toRevRingEquiv S).symm a) :=
  rfl

#audit_axioms GroupApproximation.Full.LVSkewLaurentK2.skHalfK2_bwdConst_apply

/-- The monomials of the backward map, `g ↦ t^{g⁻¹}`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def skHalfK2_bwdT : Multiplicative ℤ →* SkewLaurent S :=
  (SkewMonoidAlgebra.of S (Multiplicative ℤ)).comp invMonoidHom

#audit_axioms GroupApproximation.Full.LVSkewLaurentK2.skHalfK2_bwdT

/-- Values of `skHalfK2_bwdT`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skHalfK2_bwdT_apply (g : Multiplicative ℤ) :
    skHalfK2_bwdT S g = SkewMonoidAlgebra.single g⁻¹ (1 : S) :=
  rfl

#audit_axioms GroupApproximation.Full.LVSkewLaurentK2.skHalfK2_bwdT_apply

/-- The commutation rule for the backward map.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skHalfK2_bwd_comm (x : skHalfK2_Rev S) (y : Multiplicative ℤ) :
    skHalfK2_bwdConst S (y • x) * skHalfK2_bwdT S y =
      skHalfK2_bwdT S y * skHalfK2_bwdConst S x := by
  rw [skHalfK2_bwdConst_apply, skHalfK2_bwdConst_apply, skHalfK2_bwdT_apply]
  simp only [SkewMonoidAlgebra.single_mul_single, one_mul, mul_one, one_smul,
    skHalfK2_symm_smul]

#audit_axioms GroupApproximation.Full.LVSkewLaurentK2.skHalfK2_bwd_comm

/-- The backward map `(skHalfK2_Rev S)[t,t⁻¹] → S[t,t⁻¹;φ]`, `a t^g ↦ a t^{-g}`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def skHalfK2_bwd : SkewLaurent (skHalfK2_Rev S) →+* SkewLaurent S :=
  SkewMonoidAlgebra.liftNCRingHom (skHalfK2_bwdConst S) (skHalfK2_bwdT S)
    (fun {x y} => skHalfK2_bwd_comm S x y)

#audit_axioms GroupApproximation.Full.LVSkewLaurentK2.skHalfK2_bwd

/-- The backward map on monomials.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skHalfK2_bwd_single (g : Multiplicative ℤ) (a : skHalfK2_Rev S) :
    skHalfK2_bwd S (SkewMonoidAlgebra.single g a) =
      SkewMonoidAlgebra.single g⁻¹ ((skHalfK2_toRevRingEquiv S).symm a) := by
  show SkewMonoidAlgebra.liftNC ((skHalfK2_bwdConst S : skHalfK2_Rev S →+* _) :
    skHalfK2_Rev S →+ _) (skHalfK2_bwdT S) (SkewMonoidAlgebra.single g a) = _
  rw [SkewMonoidAlgebra.liftNC_single]
  show SkewMonoidAlgebra.single 1 ((skHalfK2_toRevRingEquiv S).symm a) *
    SkewMonoidAlgebra.single g⁻¹ (1 : S) = _
  simp only [SkewMonoidAlgebra.single_mul_single, one_mul, one_smul, mul_one]

#audit_axioms GroupApproximation.Full.LVSkewLaurentK2.skHalfK2_bwd_single

end Backward

end GroupApproximation.Full.LVSkewLaurentK2
