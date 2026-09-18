import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVSkewLaurentK2.Interface
import GroupApproximation.Meta.AxiomGuard

/-!
# The reversed action and `t ↦ t⁻¹` (lane sk-lv-03, part 1)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii; `frontier/SK.md`,
section 2b, items 10-11.  The negative half ring `S[t⁻¹;φ⁻¹] = skewHalf S (-1)` is the positive
half ring of the *reversed* action `g • a := g⁻¹ • a`.  This file sets up

* `skHalfK2_Rev S`: a type synonym of `S` carrying the reversed action;
* `skHalfK2_toRevRingEquiv S : S ≃+* skHalfK2_Rev S`: the identity;
* `skHalfK2_fwd S : SkewLaurent S →+* SkewLaurent (skHalfK2_Rev S)`, `a t^g ↦ a t^{-g}`;
* `skHalfK2_bwd S`: the map in the other direction, `a t^g ↦ a t^{-g}`.

`HalfUltraEquiv.lean` shows that these are mutually inverse and send `skewHalf S (-1)` onto
`skewHalf (skHalfK2_Rev S) 1`.
-/

namespace GroupApproximation.Full.LVSkewLaurentK2

/-- A type synonym of `S`, which carries the reversed action `g • a := g⁻¹ • a`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def skHalfK2_Rev (S : Type*) : Type _ := S

#audit_axioms GroupApproximation.Full.LVSkewLaurentK2.skHalfK2_Rev

section RingPart

variable (S : Type*) [Ring S]

/-- The ring structure of `skHalfK2_Rev S` is that of `S`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
instance skHalfK2_instRingRev : Ring (skHalfK2_Rev S) := inferInstanceAs (Ring S)

#audit_axioms GroupApproximation.Full.LVSkewLaurentK2.skHalfK2_instRingRev

/-- The identity `S ≃+* skHalfK2_Rev S`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def skHalfK2_toRevRingEquiv : S ≃+* skHalfK2_Rev S where
  toFun a := a
  invFun a := a
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

#audit_axioms GroupApproximation.Full.LVSkewLaurentK2.skHalfK2_toRevRingEquiv

/-- Ultramatricity does not see the action, so it passes to `skHalfK2_Rev S`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skHalfK2_isUltramatricialF2_rev (hS : IsUltramatricialF2 S) :
    IsUltramatricialF2 (skHalfK2_Rev S) :=
  hS

#audit_axioms GroupApproximation.Full.LVSkewLaurentK2.skHalfK2_isUltramatricialF2_rev

end RingPart

section ActionPart

variable (S : Type*) [Ring S] [MulSemiringAction (Multiplicative ℤ) S]

/-- The reversed action `g • a := g⁻¹ • a` on `skHalfK2_Rev S`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
instance skHalfK2_instActionRev : MulSemiringAction (Multiplicative ℤ) (skHalfK2_Rev S) :=
  MulSemiringAction.compHom S (invMonoidHom : Multiplicative ℤ →* Multiplicative ℤ)

#audit_axioms GroupApproximation.Full.LVSkewLaurentK2.skHalfK2_instActionRev

/-- The reversed action, read through `skHalfK2_toRevRingEquiv`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skHalfK2_rev_smul (g : Multiplicative ℤ) (a : S) :
    g • skHalfK2_toRevRingEquiv S a = skHalfK2_toRevRingEquiv S (g⁻¹ • a) :=
  rfl

#audit_axioms GroupApproximation.Full.LVSkewLaurentK2.skHalfK2_rev_smul

/-- The reversed action, read through the inverse of `skHalfK2_toRevRingEquiv`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skHalfK2_symm_smul (g : Multiplicative ℤ) (a : skHalfK2_Rev S) :
    (skHalfK2_toRevRingEquiv S).symm (g • a) = g⁻¹ • (skHalfK2_toRevRingEquiv S).symm a :=
  rfl

#audit_axioms GroupApproximation.Full.LVSkewLaurentK2.skHalfK2_symm_smul

/-- The constants of the forward map, `a ↦ a t⁰`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def skHalfK2_fwdConst : S →+* SkewLaurent (skHalfK2_Rev S) :=
  (SkewMonoidAlgebra.singleOneRingHom (k := skHalfK2_Rev S) (G := Multiplicative ℤ)).comp
    (skHalfK2_toRevRingEquiv S).toRingHom

#audit_axioms GroupApproximation.Full.LVSkewLaurentK2.skHalfK2_fwdConst

/-- Values of `skHalfK2_fwdConst`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skHalfK2_fwdConst_apply (a : S) :
    skHalfK2_fwdConst S a = SkewMonoidAlgebra.single 1 (skHalfK2_toRevRingEquiv S a) :=
  rfl

#audit_axioms GroupApproximation.Full.LVSkewLaurentK2.skHalfK2_fwdConst_apply

/-- The monomials of the forward map, `g ↦ t^{g⁻¹}`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def skHalfK2_fwdT : Multiplicative ℤ →* SkewLaurent (skHalfK2_Rev S) :=
  (SkewMonoidAlgebra.of (skHalfK2_Rev S) (Multiplicative ℤ)).comp invMonoidHom

#audit_axioms GroupApproximation.Full.LVSkewLaurentK2.skHalfK2_fwdT

/-- Values of `skHalfK2_fwdT`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skHalfK2_fwdT_apply (g : Multiplicative ℤ) :
    skHalfK2_fwdT S g = SkewMonoidAlgebra.single g⁻¹ (1 : skHalfK2_Rev S) :=
  rfl

#audit_axioms GroupApproximation.Full.LVSkewLaurentK2.skHalfK2_fwdT_apply

/-- The commutation rule `t^{-g} a = (g • a) t^{-g}` for the reversed action.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skHalfK2_fwd_comm (x : S) (y : Multiplicative ℤ) :
    skHalfK2_fwdConst S (y • x) * skHalfK2_fwdT S y =
      skHalfK2_fwdT S y * skHalfK2_fwdConst S x := by
  rw [skHalfK2_fwdConst_apply, skHalfK2_fwdConst_apply, skHalfK2_fwdT_apply]
  simp only [SkewMonoidAlgebra.single_mul_single, one_mul, mul_one, one_smul,
    skHalfK2_rev_smul, inv_inv]

#audit_axioms GroupApproximation.Full.LVSkewLaurentK2.skHalfK2_fwd_comm

/-- The forward map `S[t,t⁻¹;φ] → (skHalfK2_Rev S)[t,t⁻¹]`, `a t^g ↦ a t^{-g}`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def skHalfK2_fwd : SkewLaurent S →+* SkewLaurent (skHalfK2_Rev S) :=
  SkewMonoidAlgebra.liftNCRingHom (skHalfK2_fwdConst S) (skHalfK2_fwdT S)
    (fun {x y} => skHalfK2_fwd_comm S x y)

#audit_axioms GroupApproximation.Full.LVSkewLaurentK2.skHalfK2_fwd

/-- The forward map on monomials.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skHalfK2_fwd_single (g : Multiplicative ℤ) (a : S) :
    skHalfK2_fwd S (SkewMonoidAlgebra.single g a) =
      SkewMonoidAlgebra.single g⁻¹ (skHalfK2_toRevRingEquiv S a) := by
  show SkewMonoidAlgebra.liftNC ((skHalfK2_fwdConst S : S →+* _) : S →+ _) ⇑(skHalfK2_fwdT S)
    (SkewMonoidAlgebra.single g a) = _
  rw [SkewMonoidAlgebra.liftNC_single]
  show SkewMonoidAlgebra.single 1 (skHalfK2_toRevRingEquiv S a) *
    SkewMonoidAlgebra.single g⁻¹ (1 : skHalfK2_Rev S) = _
  simp only [SkewMonoidAlgebra.single_mul_single, one_mul, one_smul, mul_one]

#audit_axioms GroupApproximation.Full.LVSkewLaurentK2.skHalfK2_fwd_single

end ActionPart

end GroupApproximation.Full.LVSkewLaurentK2
