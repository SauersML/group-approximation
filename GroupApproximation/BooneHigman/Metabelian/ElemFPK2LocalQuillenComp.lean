import GroupApproximation.BooneHigman.Metabelian.ElemFPK2LocalQuillenMaps
import GroupApproximation.Meta.AxiomGuard

/-!
# Composition identities for the Quillen patching of the nil part of `K₂`

Lane `bh-met-46`, helper module.  With `σ_a = quillenShift B a`, `μ_c = quillenScale B c`,
`τ_b = quillenTranslate B b`, `ρ = quillenCollapse B` (module `ElemFPK2LocalQuillenMaps`) and
`C : B[t] → B[t][y]`:

* `quillenShift_zero`: `σ_0 = C`;
* `quillenScale_comp_shift`, `quillenScale_comp_C`: `μ_c ∘ σ_a = σ_{c a}` and `μ_c ∘ C = C`;
* `quillenTranslate_comp_shift`, `quillenTranslate_comp_C`: `τ_b ∘ σ_a = σ_{a + b}` and
  `τ_b ∘ C = σ_b`;
* `quillenCollapse_comp_shift_one`, `quillenCollapse_comp_C`: `ρ ∘ σ_1 = id` and
  `ρ ∘ C = C ∘ ev_{t=0}`.

Each identity between maps out of `B[t]` is checked on the constants and on `t`
(`Polynomial.ringHom_ext`); each identity between maps out of `B[t][y]` composed with `C` is checked
pointwise.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

section QuillenComp

variable {B : Type*} [CommRing B]

/-- `σ_0 = C`. -/
theorem quillenShift_zero :
    quillenShift B 0 = (Polynomial.C : Polynomial B →+* Polynomial (Polynomial B)) :=
  Polynomial.ringHom_ext (fun b ↦ by rw [quillenShift_C]) (by
    rw [quillenShift_X, map_zero, map_zero, zero_mul, add_zero])

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.quillenShift_zero

/-- `μ_c ∘ σ_a = σ_{c a}`. -/
theorem quillenScale_comp_shift (c a : B) :
    (quillenScale B c).comp (quillenShift B a) = quillenShift B (c * a) :=
  Polynomial.ringHom_ext
    (fun b ↦ by rw [RingHom.comp_apply, quillenShift_C, quillenShift_C, quillenScale_C]) (by
      rw [RingHom.comp_apply, quillenShift_X, quillenShift_X, map_add (quillenScale B c),
        map_mul (quillenScale B c), quillenScale_C, quillenScale_C, quillenScale_X,
        Polynomial.C_mul, Polynomial.C_mul]
      ring)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.quillenScale_comp_shift

/-- `μ_c ∘ C = C`. -/
theorem quillenScale_comp_C (c : B) :
    (quillenScale B c).comp (Polynomial.C : Polynomial B →+* Polynomial (Polynomial B)) =
      Polynomial.C :=
  RingHom.ext fun f ↦ by rw [RingHom.comp_apply, quillenScale_C]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.quillenScale_comp_C

/-- `τ_b ∘ σ_a = σ_{a + b}`. -/
theorem quillenTranslate_comp_shift (a b : B) :
    (quillenTranslate B b).comp (quillenShift B a) = quillenShift B (a + b) :=
  Polynomial.ringHom_ext
    (fun r ↦ by
      rw [RingHom.comp_apply, quillenShift_C, quillenShift_C, quillenTranslate_C, quillenShift_C])
    (by
      rw [RingHom.comp_apply, quillenShift_X, quillenShift_X, map_add (quillenTranslate B b),
        map_mul (quillenTranslate B b), quillenTranslate_C, quillenTranslate_C,
        quillenTranslate_X, quillenShift_X, quillenShift_C, Polynomial.C_add, Polynomial.C_add]
      ring)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.quillenTranslate_comp_shift

/-- `τ_b ∘ C = σ_b`. -/
theorem quillenTranslate_comp_C (b : B) :
    (quillenTranslate B b).comp (Polynomial.C : Polynomial B →+* Polynomial (Polynomial B)) =
      quillenShift B b :=
  RingHom.ext fun f ↦ by rw [RingHom.comp_apply, quillenTranslate_C]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.quillenTranslate_comp_C

/-- `ρ ∘ σ_1 = id`. -/
theorem quillenCollapse_comp_shift_one :
    (quillenCollapse B).comp (quillenShift B 1) = RingHom.id (Polynomial B) :=
  Polynomial.ringHom_ext
    (fun r ↦ by
      rw [RingHom.comp_apply, RingHom.id_apply, quillenShift_C, quillenCollapse_C,
        Polynomial.eval_C])
    (by
      rw [RingHom.comp_apply, RingHom.id_apply, quillenShift_X, map_add (quillenCollapse B),
        map_mul (quillenCollapse B), quillenCollapse_C, quillenCollapse_C, quillenCollapse_X,
        Polynomial.eval_X, Polynomial.eval_C, map_zero, map_one, zero_add, one_mul])

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.quillenCollapse_comp_shift_one

/-- `ρ ∘ C = C ∘ ev_{t=0}`. -/
theorem quillenCollapse_comp_C :
    (quillenCollapse B).comp (Polynomial.C : Polynomial B →+* Polynomial (Polynomial B)) =
      RingHom.comp (Polynomial.C : B →+* Polynomial B)
        (Polynomial.evalRingHom 0 : Polynomial B →+* B) :=
  RingHom.ext fun f ↦ by
    rw [RingHom.comp_apply, RingHom.comp_apply, quillenCollapse_C, Polynomial.coe_evalRingHom]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.quillenCollapse_comp_C

end QuillenComp

end GroupApproximation.BooneHigman.Metabelian.ElemFP
