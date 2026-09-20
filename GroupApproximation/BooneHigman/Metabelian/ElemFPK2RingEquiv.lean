import GroupApproximation.BooneHigman.Metabelian.ElemFPK2OneVarTransport
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2SplitStab
import GroupApproximation.Meta.AxiomGuard

/-!
# Transport of `K₂` vanishing along ring isomorphisms

This generic functoriality argument is independent of polynomial normal forms and the
Boone–Higman endpoint constructions.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic

/-- `K₂(I, -) = ⊥` transfers along a ring isomorphism (from `K2Map`'s functoriality). -/
theorem bhNagaoWire_K2_bot_of_ringEquiv {I R S : Type*} [Fintype I] [DecidableEq I] [Ring R]
    [Ring S] (e : R ≃+* S) (h : K2 I S = ⊥) : K2 I R = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun g hg ↦ ?_
  have h2 := K2Map_K2Map_of_comp_eq_id e.symm.toRingHom e.toRingHom
    e.symm_toRingHom_comp_toRingHom (⟨g, hg⟩ : K2 I R)
  rw [eq_one_of_K2_eq_bot h (K2Map e.toRingHom (⟨g, hg⟩ : K2 I R)), map_one] at h2
  exact congrArg Subtype.val h2.symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.bhNagaoWire_K2_bot_of_ringEquiv

end GroupApproximation.BooneHigman.Metabelian.ElemFP
