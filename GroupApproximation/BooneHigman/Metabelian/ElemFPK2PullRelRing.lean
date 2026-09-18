import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PullExcStatement
import GroupApproximation.BooneHigman.SteinbergBasic.Naturality
import GroupApproximation.Meta.AxiomGuard

/-!
# Ring maps of the pullback `P = A ×_L L[X]`

Lane `bh-met-91g`, ring module.  Here `L = A_s`, `λ = algebraMap A L` and
`P = k2DilateSt_pullback s = {(a, h) : λ a = h(0)}`.

* `k2PullRel_fst : P →+* A` and `k2PullRel_snd : P →+* L[X]`, the two projections.
* `k2PullRel_const : A →+* P`, `a ↦ (a, C (λ a))`.  It is `ι_0 ∘ C`, and `fst ∘ const = id`.
* `k2PullRel_lift h = (0, h - C (h(0)))`.  This is the additive section of `snd` on
  `ker fst`.  It kills constants (`k2PullRel_lift_C`), is additive (`k2PullRel_lift_add`),
  inverts `snd` on `ker fst` (`k2PullRel_lift_snd`) and satisfies the product identity
  `k2PullRel_lift_mul` behind the adjacent Steinberg relator.
* `k2PullRel_fst_comp_toPullback` and `k2PullRel_snd_comp_toPullback`: on `ι_0` the two
  projections are `f ↦ f(0)` and `f ↦ λ f`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup

section PullRelRing

variable {A : Type*} [CommRing A]

/-- The projection `P → A`. -/
def k2PullRel_fst (s : A) : k2DilateSt_pullback s →+* A :=
  (RingHom.fst A (Polynomial (Localization.Away s))).comp (k2DilateSt_pullback s).subtype

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_fst

/-- The projection `P → L[X]`. -/
def k2PullRel_snd (s : A) : k2DilateSt_pullback s →+* Polynomial (Localization.Away s) :=
  (RingHom.snd A (Polynomial (Localization.Away s))).comp (k2DilateSt_pullback s).subtype

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_snd

theorem k2PullRel_ext {s : A} {b b' : k2DilateSt_pullback s}
    (h₁ : k2PullRel_fst s b = k2PullRel_fst s b') (h₂ : k2PullRel_snd s b = k2PullRel_snd s b') :
    b = b' :=
  Subtype.ext (Prod.ext h₁ h₂)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_ext

/-- The defining equation of `P`: `(snd b)(0) = λ (fst b)`. -/
theorem k2PullRel_eval_snd {s : A} (b : k2DilateSt_pullback s) :
    (k2PullRel_snd s b).eval 0 = algebraMap A (Localization.Away s) (k2PullRel_fst s b) :=
  ((k2DilateSt_mem_pullback s b).mp b.2).symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_eval_snd

/-- The constants `A → P`, `a ↦ (a, C (λ a))`. -/
noncomputable def k2PullRel_const (s : A) : A →+* k2DilateSt_pullback s :=
  (k2DilateSt_toPullback s 0).comp Polynomial.C

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_const

theorem k2PullRel_fst_const (s : A) (a : A) : k2PullRel_fst s (k2PullRel_const s a) = a :=
  congrArg Prod.fst (k2DilateSt_stage_C s 0 a)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_fst_const

theorem k2PullRel_snd_const (s : A) (a : A) :
    k2PullRel_snd s (k2PullRel_const s a) =
      Polynomial.C (algebraMap A (Localization.Away s) a) :=
  congrArg Prod.snd (k2DilateSt_stage_C s 0 a)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_snd_const

theorem k2PullRel_fst_comp_const (s : A) :
    (k2PullRel_fst s).comp (k2PullRel_const s) = RingHom.id A :=
  RingHom.ext (k2PullRel_fst_const s)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_fst_comp_const

theorem k2PullRel_snd_comp_const (s : A) :
    (k2PullRel_snd s).comp (k2PullRel_const s) =
      Polynomial.C.comp (algebraMap A (Localization.Away s)) :=
  RingHom.ext (k2PullRel_snd_const s)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_snd_comp_const

theorem k2PullRel_fst_comp_toPullback (s : A) :
    (k2PullRel_fst s).comp (k2DilateSt_toPullback s 0) = Polynomial.evalRingHom 0 :=
  RingHom.ext fun _ ↦ rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_fst_comp_toPullback

theorem k2PullRel_snd_comp_toPullback (s : A) :
    (k2PullRel_snd s).comp (k2DilateSt_toPullback s 0) =
      Polynomial.mapRingHom (algebraMap A (Localization.Away s)) := by
  refine RingHom.ext fun f ↦ ?_
  show k2CubeDilate_scale (Localization.Away s) (k2DilateSt_inv s ^ 0)
      (f.map (algebraMap A (Localization.Away s))) =
    Polynomial.mapRingHom (algebraMap A (Localization.Away s)) f
  rw [pow_zero, k2CubeDilate_scale_one, RingHom.id_apply, Polynomial.coe_mapRingHom]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_snd_comp_toPullback

/-- The section of `snd` on `ker fst`: `h ↦ (0, h - C (h(0)))`. -/
noncomputable def k2PullRel_lift (s : A) (h : Polynomial (Localization.Away s)) :
    k2DilateSt_pullback s :=
  ⟨(0, h - Polynomial.C (h.eval 0)), by
    show algebraMap A (Localization.Away s) 0 = (h - Polynomial.C (h.eval 0)).eval 0
    rw [map_zero, Polynomial.eval_sub, Polynomial.eval_C, sub_self]⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_lift

theorem k2PullRel_fst_lift (s : A) (h : Polynomial (Localization.Away s)) :
    k2PullRel_fst s (k2PullRel_lift s h) = 0 :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_fst_lift

theorem k2PullRel_snd_lift (s : A) (h : Polynomial (Localization.Away s)) :
    k2PullRel_snd s (k2PullRel_lift s h) = h - Polynomial.C (h.eval 0) :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_snd_lift

theorem k2PullRel_lift_add (s : A) (a b : Polynomial (Localization.Away s)) :
    k2PullRel_lift s a + k2PullRel_lift s b = k2PullRel_lift s (a + b) := by
  refine k2PullRel_ext ?_ ?_
  · simp only [map_add, k2PullRel_fst_lift, add_zero]
  · simp only [map_add, k2PullRel_snd_lift, Polynomial.eval_add]
    ring

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_lift_add

theorem k2PullRel_lift_C (s : A) (t : Localization.Away s) :
    k2PullRel_lift s (Polynomial.C t) = 0 := by
  refine k2PullRel_ext ?_ ?_
  · rw [k2PullRel_fst_lift, map_zero]
  · rw [k2PullRel_snd_lift, Polynomial.eval_C, sub_self, map_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_lift_C

theorem k2PullRel_lift_snd {s : A} {b : k2DilateSt_pullback s} (hb : k2PullRel_fst s b = 0) :
    k2PullRel_lift s (k2PullRel_snd s b) = b := by
  refine k2PullRel_ext ?_ ?_
  · rw [k2PullRel_fst_lift, hb]
  · rw [k2PullRel_snd_lift, k2PullRel_eval_snd, hb, map_zero, map_zero, sub_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_lift_snd

/-- **Product identity** in `P`, behind the adjacent relator:
`lift (C a(0) · b) + lift a · lift b = lift (a b) + lift (-(a · C b(0)))`. -/
theorem k2PullRel_lift_mul (s : A) (a b : Polynomial (Localization.Away s)) :
    k2PullRel_lift s (Polynomial.C (a.eval 0) * b) + k2PullRel_lift s a * k2PullRel_lift s b =
      k2PullRel_lift s (a * b) + k2PullRel_lift s (-(a * Polynomial.C (b.eval 0))) := by
  refine k2PullRel_ext ?_ ?_
  · simp only [map_add, map_mul, k2PullRel_fst_lift, mul_zero, add_zero]
  · simp only [map_add, map_mul, map_neg, k2PullRel_snd_lift, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_neg]
    ring

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_lift_mul

end PullRelRing

end GroupApproximation.BooneHigman.Metabelian.ElemFP
