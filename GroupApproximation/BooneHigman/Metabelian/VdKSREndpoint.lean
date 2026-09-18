import GroupApproximation.BooneHigman.Metabelian.VdKSRPoly
import GroupApproximation.BooneHigman.Metabelian.VdKStabEndpoint
import GroupApproximation.Meta.AxiomGuard

/-!
# `vdkStab_PolyStableRangeHighStatement`, proved

Lane `bh-met-90m`, endpoint.  `vdkSR_stableRangeLE_mvPolynomial` gives `sr(K[x₁, …, x_k]) ≤ k + 1`
for every field `K` and every `k`; specialising to `K = ZMod p` proves both
`vdkStab_PolyStableRangeStatement` and its `k ≥ 2` part outright.  Consequently
`VdKRowExtensionStatement` follows from `vdkStab_InjStabStatement` alone.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

/-- **(A)**, proved: `sr(𝔽_p[x₁, …, x_k]) ≤ k + 1` for every prime `p` and every `k`. -/
theorem vdkSR_polyStableRange : vdkStab_PolyStableRangeStatement := by
  intro p hp k
  haveI : Fact p.Prime := ⟨hp⟩
  exact vdkSR_stableRangeLE_mvPolynomial (ZMod p) k

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkSR_polyStableRange

/-- **(A), `k ≥ 2`**, proved. -/
theorem vdkSR_polyStableRangeHigh : vdkStab_PolyStableRangeHighStatement := by
  intro p hp k _
  exact vdkSR_polyStableRange p hp k

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkSR_polyStableRangeHigh

/-- **Endpoint**: `VdKRowExtensionStatement` from injective stability (B) alone. -/
theorem vdkSR_vdkRowExt_of_injStab (hB : vdkStab_InjStabStatement) : VdKRowExtensionStatement :=
  vdkStab_vdkRowExt_of_high_injStab vdkSR_polyStableRangeHigh hB

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkSR_vdkRowExt_of_injStab

end GroupApproximation.BooneHigman.Metabelian.ElemFP
