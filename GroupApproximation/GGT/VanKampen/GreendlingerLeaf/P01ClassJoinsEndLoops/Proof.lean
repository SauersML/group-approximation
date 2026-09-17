import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.Bubble
import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundSameCellPocketAssembly
import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundSameCellPocketCellFree
import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundSameCellPocketLoopCut
import GroupApproximation.Meta.AxiomGuard

/-!
# End loops of the class producer

This module proves `OsinLemma94ClassJoinsEndLoopsInput` with `eps0 = 0`,
`B = (2 ε + 2) ⌈c / λ⌉₊` and `rho0 = max rho1 (2 ⌈c / λ⌉₊ + 3)`, where `rho1` comes from the
same-cell pocket value input (`osinLemma94SameCellPocketInput_of_loopCut`).

The class loops and the region loops are `classEnd` and `regionEnd` (`Bubble.lean`) at budget
`⌈c / λ⌉₊`, a bound on the pocket lengths.  The covering clause takes a longest pocket through
the unbound dart (`exists_pocket_through`, `exists_max_pocket`) and applies `covered_of_pocket`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded

open scoped Classical

/-- `c < λ ρ` once `⌈c / λ⌉₊ + 1 ≤ ρ`. -/
theorem endLoops_c_lt_lambda_mul {lambda c : ℝ} (hlambda : 0 < lambda) {rho : ℕ}
    (hrho : ⌈c / lambda⌉₊ + 1 ≤ rho) : c < lambda * rho := by
  have hceil : c / lambda ≤ ⌈c / lambda⌉₊ := Nat.le_ceil _
  have hcast : ((⌈c / lambda⌉₊ : ℕ) : ℝ) + 1 ≤ rho := by
    exact_mod_cast hrho
  have hlt : c < rho * lambda := (div_lt_iff₀ hlambda).mp (by linarith)
  linarith [mul_comm lambda (rho : ℝ)]

/-- **The end loops input.** -/
theorem proof : OsinLemma94ClassJoinsEndLoopsInput.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨0, fun eps _ => ?_⟩
  have hpocket : OsinLemma94SameCellPocketInput.{u, w, v} :=
    osinLemma94SameCellPocketInput_of_loopCut sameCellPocketCellFreeValue sameCellPocketLoopCut
  obtain ⟨rho1, hrho1, hP⟩ := hpocket D hhyper lambda c mu hlambda hlambda1 hc hmu hmu16 eps
  refine ⟨(2 * eps + 2) * ⌈c / lambda⌉₊, max rho1 (2 * ⌈c / lambda⌉₊ + 3),
    lt_of_lt_of_le hrho1 (le_max_left _ _),
    fun rho hrho W hW Delta cuts hleast _ hbelow S _ _ P _ => ?_⟩
  have hrho2 : 2 * ⌈c / lambda⌉₊ + 3 ≤ rho := (max_le_iff.mp hrho).2
  have hvalue := S.cell_listVal_ne_one hW hlambda (endLoops_c_lt_lambda_mul hlambda (by omega))
  have hleastX : S.diagram.LeastArea := S.equiv.leastArea hleast
  have hbelowX : ∀ (Xi : DiscDiagram.{u, w, v} W)
      (cutsXi : SectionCuts D lambda c Xi.boundaryWord),
      Xi.LeastArea → 0 < Xi.rCellCount → Xi.rCellCount < S.diagram.rCellCount →
        ∃ T : RealizedSectionFamily D lambda c eps Xi cutsXi, OsinLemma97bConclusion mu T :=
    fun Xi cutsXi h1 h2 h3 => hbelow Xi cutsXi h1 h2 (h3.trans_eq S.equiv.rCellCount_eq)
  have hpv : OsinUnboundSameCellBlocks.PocketValue S.diagram :=
    hP rho (max_le_iff.mp hrho).1 W hW S.diagram hleastX hbelowX
  have hlen : ∀ i : Fin S.diagram.rCellCount, 1 < (cellDarts S.diagram i).length :=
    S.one_lt_cellDarts_length hW (by omega)
  have hlong : ∀ i : Fin S.diagram.rCellCount,
      2 * ⌈c / lambda⌉₊ + 2 < (cellDarts S.diagram i).length := by
    intro i
    rw [CellBoundaryPartition.cellDarts_length_eq_word_length]
    have hl := hW.long _ (cell S.diagram i).word_mem
    omega
  have hB : ⌈c / lambda⌉₊ ≤ (2 * eps + 2) * ⌈c / lambda⌉₊ :=
    (Nat.one_mul _).symm.le.trans (Nat.mul_le_mul_right _ (by omega))
  refine ⟨classEnd (P.joinQ hW hc) ⌈c / lambda⌉₊, regionEnd ⌈c / lambda⌉₊,
    fun k _ i _ b => (length_classEnd (P.joinQ hW hc) _ k i b).trans hB,
    fun a _ t => length_regionEnd _ a t, ?_⟩
  intro i d hdoff _ k s hcount hs hrel hds
  have hdmem : d ∈ cellDarts S.diagram i :=
    List.mem_toFinset.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hdoff).1).1
  obtain ⟨l0, hl0⟩ := exists_pocket_through (P.joinQ hW hc) hdmem hcount hs hrel hds
  obtain ⟨J, hJ, hmax⟩ := exists_max_pocket hW hlambda hl0
  obtain ⟨x, t, ht, hxt, hx⟩ := hJ
  exact covered_of_pocket (P.joinQ hW hc) hvalue hlen hpv
    (fun _ _ h => h.le_ceil hW hlambda) (hlong i) hdoff hx ht hxt hmax

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.proof
