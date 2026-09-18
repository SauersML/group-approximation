import Mathlib.Algebra.MvPolynomial.Equiv
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2InjStabRetract
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2SplitStab
import GroupApproximation.BooneHigman.Metabelian.ElemFPFieldK2BruhatEndpoint
import GroupApproximation.BooneHigman.Metabelian.ElemFPFieldK2BruhatBigCellEndpoint
import GroupApproximation.Meta.AxiomGuard

/-!
# The field case of the row-extension gap, discharged outright

Lane `bh-met-90b`, helper module.  Target chain: `VdKRowExtensionStatement`
(module `ElemFPK2VdKEndpoint`).

The deepest existing residual below `VdKRowExtensionStatement` is lane `bh-met-80`'s
`K2InjStabSpecializationStatement` (module `ElemFPK2InjStabSpecial`).  Its `k = 0` instances
are injective stability of `K₂(N, F_p)` for `N ≥ 5`, stated over `MvPolynomial (Fin 0) (ZMod p)`.
Lane `bh-met-64c` proved `BruhatBigCellStatement` outright (`FieldK2.bruhatBigCell`), and lane
`bh-met-55` derived `FieldK2VanishingStatement` from it.  This module composes those:

* `vdkRowExt_fieldK2Vanishing`: `K₂(N, F_p) = 0` for `N ≥ 5`, unconditionally.
* `vdkRowExt_K2Stab_injective_zmod`: hence `K2Stab N (ZMod p)` is injective (its domain is
  trivial).
* `vdkRowExt_fieldStab`: the same over `MvPolynomial (Fin 0) (ZMod p)`, transported along the
  ring isomorphism `MvPolynomial.isEmptyRingEquiv` with `k2InjStab_injective_of_retract`.

The last statement is exactly the hypothesis `h0` of
`k2InjStab_specialization_of_nilPos_of_fieldStab`, so that hypothesis is now discharged.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic

/-- `K₂(N, F_p) = 0` for `N ≥ 5`, unconditionally (big Bruhat cell, lanes `bh-met-64c` and
`bh-met-55`). -/
theorem vdkRowExt_fieldK2Vanishing : FieldK2VanishingStatement :=
  FieldK2.fieldK2Vanishing_of_bruhatBigCell FieldK2.bruhatBigCell

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowExt_fieldK2Vanishing

/-- Injective stability of `K₂(N, F_p)` for `N ≥ 5`: the domain is trivial. -/
theorem vdkRowExt_K2Stab_injective_zmod {p : ℕ} (hp : p.Prime) {N : ℕ} (hN : 5 ≤ N) :
    Function.Injective (K2Stab N (ZMod p)) := by
  intro a b _
  rw [eq_one_of_K2_eq_bot (vdkRowExt_fieldK2Vanishing p hp N hN) a,
    eq_one_of_K2_eq_bot (vdkRowExt_fieldK2Vanishing p hp N hN) b]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowExt_K2Stab_injective_zmod

/-- **The field case, outright**: injective stability of `K₂(N, -)` over the polynomial ring in
no variables over `F_p`, for `N ≥ 5`.  This is the hypothesis `h0` of
`k2InjStab_specialization_of_nilPos_of_fieldStab`. -/
theorem vdkRowExt_fieldStab : ∀ p : ℕ, p.Prime → ∀ N : ℕ, 5 ≤ N →
    Function.Injective (K2Stab N (MvPolynomial (Fin 0) (ZMod p))) := fun p hp N hN ↦
  k2InjStab_injective_of_retract
    (MvPolynomial.isEmptyRingEquiv (ZMod p) (Fin 0)).toRingHom
    (MvPolynomial.isEmptyRingEquiv (ZMod p) (Fin 0)).symm.toRingHom
    (MvPolynomial.isEmptyRingEquiv (ZMod p) (Fin 0)).symm_toRingHom_comp_toRingHom
    (vdkRowExt_K2Stab_injective_zmod hp hN)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowExt_fieldStab

end GroupApproximation.BooneHigman.Metabelian.ElemFP
