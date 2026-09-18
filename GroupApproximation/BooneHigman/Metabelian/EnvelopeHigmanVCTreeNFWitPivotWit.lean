import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTreeNFWitPivotSwap
import GroupApproximation.Meta.AxiomGuard

/-!
# Antichain pivot closure gives the witness Statement (lane bh-met-77p)

`higmanVCTreeNFWitPivot_level_of_X`: the isolated Statement X
(`HigmanVCTreeNFWitPivotStatement`) gives `HigmanVCTreeLevelStatement`.  Take a kernel word `r`
whose class lies in `G_n`.  Then `mk r = u₁ * g * u₂` with `g ∈ H_C`
(`higmanVCTreeNFWitPivot_mem_S_of_G`).  So `E g ∈ E(U)`, the kernel step gives `g ∈ U`
(`higmanVCTreeNFWitPivot_mem_U`), and faithfulness of `U` finishes.

Endpoints:
* `higmanVCTreeNFWitPivot_ker_le_of_X`: X gives (1) at every `d > 1`.
* `higmanVCTreeNFWitPivot_wit_of_X`: X gives `HigmanVCTreeNFWitStatement`.
* `higmanVCTreeNFWitPivot_pivotClosed_of_X`: X gives pivot closure (iii) of the canonical `τ`,
  for every `t`.

See `EnvelopeHigmanVCTreeNFWitPivot` for the truth status of X.  **LOUD**: X is equivalent to
(1) as a Prop given the truth of (1).  It is smaller in proof content, not weaker as a Prop.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

theorem higmanVCTreeNFWitPivot_level_of_X (h : HigmanVCTreeNFWitPivotStatement) :
    HigmanVCTreeLevelStatement := by
  intro d hd N
  obtain ⟨n, hn, a, b, ha, hb, hab, hba, ht⟩ := h d hd N
  refine ⟨n, hn, a, b, ha, hb, hab, hba, fun r hr hq => ?_⟩
  obtain ⟨u₁, hu₁, C, hC, g, hg, u₂, hu₂, e⟩ :=
    higmanVCTreeNFWitPivot_mem_S.mp (higmanVCTreeNFWitPivot_mem_S_of_G ht hq)
  have hE : higmanVCTreeNF_E d (u₁ * g * u₂) = 1 := by
    rw [← e, higmanVCTreeNF_E_mk]
    exact MonoidHom.mem_ker.mp hr
  rw [map_mul, map_mul] at hE
  have h1 : higmanVCTreeNF_E d u₁ * higmanVCTreeNF_E d g = (higmanVCTreeNF_E d u₂)⁻¹ :=
    mul_eq_one_iff_eq_inv.mp hE
  have h2 : higmanVCTreeNF_E d g =
      (higmanVCTreeNF_E d u₁)⁻¹ * (higmanVCTreeNF_E d u₂)⁻¹ :=
    eq_inv_mul_of_mul_eq h1
  have h3 : higmanVCTreeNF_E d g = higmanVCTreeNF_E d (u₁⁻¹ * u₂⁻¹) := by
    rw [map_mul, map_inv, map_inv]
    exact h2
  have hgU := higmanVCTreeNFWitPivot_mem_U hd hC hg
    ((higmanVCTreeNF_U d).mul_mem ((higmanVCTreeNF_U d).inv_mem hu₁)
      ((higmanVCTreeNF_U d).inv_mem hu₂)) h3
  refine higmanVCTreeNF_U_faithful (by omega) hr ?_
  rw [e]
  exact (higmanVCTreeNF_U d).mul_mem ((higmanVCTreeNF_U d).mul_mem hu₁ hgU) hu₂

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWitPivot_level_of_X

theorem higmanVCTreeNFWitPivot_ker_le_of_X (h : HigmanVCTreeNFWitPivotStatement) (d : ℕ)
    (hd : 1 < d) :
    (higmanVC_evalAll d).ker ≤ Subgroup.normalClosure (higmanVC_rels d fun _ => True) :=
  higmanVCTreeLevel_ker_le_of_level (higmanVCTreeNFWitPivot_level_of_X h) d hd

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWitPivot_ker_le_of_X

/-- **The lane endpoint**: X gives the witness Statement. -/
theorem higmanVCTreeNFWitPivot_wit_of_X (h : HigmanVCTreeNFWitPivotStatement) :
    HigmanVCTreeNFWitStatement :=
  higmanVCTreeNFWit_of_ker_le fun d hd => higmanVCTreeNFWitPivot_ker_le_of_X h d hd

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWitPivot_wit_of_X

theorem higmanVCTreeNFWitPivot_pivotClosed_of_X (h : HigmanVCTreeNFWitPivotStatement) (d : ℕ)
    (hd : 1 < d) (t : higmanVCCommon_Q d) :
    higmanVCTreeNFWit_PivotClosed d (higmanVCTreeNFWit_tau d) t :=
  higmanVCTreeNFWit_pivot_of_ker_le (higmanVCTreeNFWitPivot_ker_le_of_X h d hd) t

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWitPivot_pivotClosed_of_X

end GroupApproximation.BooneHigman.Metabelian.Envelope
