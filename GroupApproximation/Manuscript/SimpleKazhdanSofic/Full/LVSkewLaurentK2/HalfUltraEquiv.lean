import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVSkewLaurentK2.HalfUltraBwd

/-!
# `S[t⁻¹;φ⁻¹] ≅ S'[t;φ⁻¹]` (lane sk-lv-03, part 3)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii; `frontier/SK.md`,
section 2b, items 10-11.  The maps `skHalfK2_fwd` and `skHalfK2_bwd` are mutually inverse.
The resulting isomorphism `skHalfK2_revEquiv S` sends `constMap S a` to the constant `a` and
`t⁻¹` to `t`, so it restricts to

`skHalfK2_negHalfEquiv S : skewHalf S (-1) ≃+* skewHalf (skHalfK2_Rev S) 1`.

The negative half ring of `(S, φ)` is therefore the positive half ring of `(S, φ⁻¹)`.
-/

namespace GroupApproximation.Full.LVSkewLaurentK2

section Equiv

variable (S : Type*) [Ring S] [MulSemiringAction (Multiplicative ℤ) S]

/-- `fwd ∘ bwd = id`.  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skHalfK2_fwd_comp_bwd :
    (skHalfK2_fwd S).comp (skHalfK2_bwd S) = RingHom.id (SkewLaurent (skHalfK2_Rev S)) := by
  refine RingHom.ext fun x => ?_
  induction x using SkewMonoidAlgebra.induction_on with
  | zero => simp only [map_zero]
  | single g a =>
    rw [RingHom.comp_apply, skHalfK2_bwd_single, skHalfK2_fwd_single, inv_inv,
      RingEquiv.apply_symm_apply, RingHom.id_apply]
  | add p q hp hq => rw [map_add, map_add, hp, hq]

#audit_axioms GroupApproximation.Full.LVSkewLaurentK2.skHalfK2_fwd_comp_bwd

/-- `bwd ∘ fwd = id`.  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skHalfK2_bwd_comp_fwd :
    (skHalfK2_bwd S).comp (skHalfK2_fwd S) = RingHom.id (SkewLaurent S) := by
  refine RingHom.ext fun x => ?_
  induction x using SkewMonoidAlgebra.induction_on with
  | zero => simp only [map_zero]
  | single g a =>
    rw [RingHom.comp_apply, skHalfK2_fwd_single, skHalfK2_bwd_single, inv_inv,
      RingEquiv.symm_apply_apply, RingHom.id_apply]
  | add p q hp hq => rw [map_add, map_add, hp, hq]

#audit_axioms GroupApproximation.Full.LVSkewLaurentK2.skHalfK2_bwd_comp_fwd

/-- The isomorphism `S[t,t⁻¹;φ] ≅ (skHalfK2_Rev S)[t,t⁻¹]`, `a t^g ↦ a t^{-g}`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def skHalfK2_revEquiv : SkewLaurent S ≃+* SkewLaurent (skHalfK2_Rev S) :=
  RingEquiv.ofRingHom (skHalfK2_fwd S) (skHalfK2_bwd S) (skHalfK2_fwd_comp_bwd S)
    (skHalfK2_bwd_comp_fwd S)

#audit_axioms GroupApproximation.Full.LVSkewLaurentK2.skHalfK2_revEquiv

/-- `skHalfK2_revEquiv` on constants.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skHalfK2_revEquiv_constMap (a : S) :
    (skHalfK2_revEquiv S).toRingHom (constMap S a) =
      constMap (skHalfK2_Rev S) (skHalfK2_toRevRingEquiv S a) := by
  show skHalfK2_fwd S (SkewMonoidAlgebra.single 1 a) =
    SkewMonoidAlgebra.single 1 (skHalfK2_toRevRingEquiv S a)
  rw [skHalfK2_fwd_single, inv_one]

#audit_axioms GroupApproximation.Full.LVSkewLaurentK2.skHalfK2_revEquiv_constMap

/-- `skHalfK2_revEquiv` sends `t⁻¹` to `t`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skHalfK2_revEquiv_tPow :
    (skHalfK2_revEquiv S).toRingHom (tPow S (-1)) = tPow (skHalfK2_Rev S) 1 := by
  show skHalfK2_fwd S (SkewMonoidAlgebra.single (Multiplicative.ofAdd (-1 : ℤ)) (1 : S)) =
    SkewMonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) (1 : skHalfK2_Rev S)
  rw [skHalfK2_fwd_single, map_one (skHalfK2_toRevRingEquiv S), ofAdd_neg, inv_inv]

#audit_axioms GroupApproximation.Full.LVSkewLaurentK2.skHalfK2_revEquiv_tPow

/-- `skHalfK2_revEquiv` maps `S[t⁻¹;φ⁻¹]` onto `(skHalfK2_Rev S)[t;φ⁻¹]`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skHalfK2_map_skewHalf :
    (skewHalf S (-1)).map (skHalfK2_revEquiv S).toRingHom = skewHalf (skHalfK2_Rev S) 1 := by
  have hfun : ⇑(skHalfK2_revEquiv S).toRingHom ∘ ⇑(constMap S) =
      ⇑(constMap (skHalfK2_Rev S)) ∘ ⇑(skHalfK2_toRevRingEquiv S) :=
    funext fun a => skHalfK2_revEquiv_constMap S a
  have himg : ⇑(skHalfK2_revEquiv S).toRingHom '' (Set.range (constMap S) ∪ {tPow S (-1)}) =
      Set.range (constMap (skHalfK2_Rev S)) ∪ {tPow (skHalfK2_Rev S) 1} := by
    rw [Set.image_union, Set.image_singleton, ← Set.range_comp, hfun,
      (skHalfK2_toRevRingEquiv S).surjective.range_comp, skHalfK2_revEquiv_tPow]
  unfold skewHalf
  rw [RingHom.map_closure, himg]

#audit_axioms GroupApproximation.Full.LVSkewLaurentK2.skHalfK2_map_skewHalf

/-- **The negative half ring is a positive half ring**:
`S[t⁻¹;φ⁻¹] ≅ (skHalfK2_Rev S)[t;φ⁻¹]`.
(`yaoseq6.tex` `thm:skewyao`, Step 1, the symmetry `t₊ ↔ t₋`;
`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def skHalfK2_negHalfEquiv : skewHalf S (-1) ≃+* skewHalf (skHalfK2_Rev S) 1 :=
  ((skHalfK2_revEquiv S).subringMap (s := skewHalf S (-1))).trans
    (RingEquiv.subringCongr (skHalfK2_map_skewHalf S))

#audit_axioms GroupApproximation.Full.LVSkewLaurentK2.skHalfK2_negHalfEquiv

end Equiv

end GroupApproximation.Full.LVSkewLaurentK2
