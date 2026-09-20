import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCSwindleCodeAction
import GroupApproximation.Meta.AxiomGuard

/-!
# Seed naturality for a generating swap

Any lift with the code-shuffle action conjugates a swap of two code leaves to
its diagonal clone. The equality follows from the splitting and conjugation
relators in the presented group, not from faithfulness of boundary evaluation.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- Splitting a leaf swap and transporting its child cones gives exact conjugation. -/
theorem higSw_codeAction_conj_swap {d : ℕ} (hd : 1 < d)
    {C : Finset (List (Fin d))} {q : higmanVCCommon_Q d}
    (hC : higmanVCTreeNFWitPivot_IsAC C) (hq : higSw_codeAction C q)
    {x y : List (Fin d)} (hx : x ∈ C) (hy : y ∈ C) (hxy : x ≠ y) :
    q * higmanVCCommon_mk d (FreeGroup.of (x, y)) * q⁻¹ =
      higSw_diag d (higmanVCCommon_mk d (FreeGroup.of (x, y))) := by
  have h1 : ¬ x <+: y := hC x hx y hy hxy
  have h2 : ¬ y <+: x := hC y hy x hx (Ne.symm hxy)
  let φ : higmanVCCommon_Q d →* higmanVCCommon_Q d := (MulAut.conj q).toMonoidHom
  change φ (higmanVCCommon_mk d (FreeGroup.of (x, y))) = _
  calc
    φ (higmanVCCommon_mk d (FreeGroup.of (x, y))) =
        ((List.finRange d).map fun a =>
          φ (higmanVCCommon_mk d (FreeGroup.of (x ++ [a], y ++ [a])))).prod := by
      rw [higmanVCCommon_mk_split h1 h2]
      simp only [higmanVC_splitAll, map_list_prod, List.map_map, Function.comp_def]
    _ = ((List.finRange d).map fun a =>
        higSw_phi d [a] (higmanVCCommon_mk d (FreeGroup.of (x, y)))).prod := by
      apply congrArg List.prod
      apply List.map_congr_left
      intro a _
      rw [higSw_phi_gen]
      exact higSw_conj_swap hd q
        (higmanVCLeafExp_incomp_append h1 h2 [a])
        (higmanVCLeafExp_incomp_append h2 h1 [a]) (hq x hx a) (hq y hy a)
    _ = higSw_diag d (higmanVCCommon_mk d (FreeGroup.of (x, y))) := rfl

/-- The seed form used before propagating naturality through matched expansions. -/
theorem higSw_codeAction_swap_naturality {d : ℕ} (hd : 1 < d)
    {C : Finset (List (Fin d))} {q : higmanVCCommon_Q d}
    (hC : higmanVCTreeNFWitPivot_IsAC C) (hq : higSw_codeAction C q)
    {x y : List (Fin d)} (hx : x ∈ C) (hy : y ∈ C) (hxy : x ≠ y) :
    q * higmanVCCommon_mk d (FreeGroup.of (x, y)) =
      higSw_diag d (higmanVCCommon_mk d (FreeGroup.of (x, y))) * q :=
  mul_inv_eq_iff_eq_mul.mp (higSw_codeAction_conj_swap hd hC hq hx hy hxy)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_codeAction_conj_swap
#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_codeAction_swap_naturality

end GroupApproximation.BooneHigman.Metabelian.Envelope
