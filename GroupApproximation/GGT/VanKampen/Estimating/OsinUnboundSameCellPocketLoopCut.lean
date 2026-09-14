import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundSameCellPocketEnclosed
import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedBridgeDoublingArc
import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedPocketRegion
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketLoopCut
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketGlueCellTransport
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellArcs
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixCutSections
import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundSameCellPocketAssembly
import GroupApproximation.Meta.AxiomGuard

/-!
# The loop cut of a same-cell pocket holding a relator cell

Osin (math/0411039v3, §9), proof of Lemma 9.4.  `SameCellPocketLoopCutStatement`
(`Estimating/OsinUnboundSameCellPocketAssembly`): under `C(ε, μ, λ, c, ρ)`, let `Δ` be least area and
`d` a dart of cell `i` whose reverse lies on cell `i`, oriented toward the exterior, with a relator
cell other than `i` on the far side.  Then `Δ` has a loop cut.

The route needs no letter labels and no collar.

* `SameCellPocketEnclosed.exists_enclosedPocket`: the far faces are enclosed, in successor form, by
  the pocket walk of `d`, an arc of cell `i`, with the far relator cell inside and cell `i` outside.
* `EnclosedBridgeDoubling.arcDoublingOutput`: on an O-equivalent copy, every bridge of the walk is
  doubled, the walk stays an arc of the transported cell, and the relator cells correspond with their
  membership in the enclosed faces.
* `EnclosedPocketRegion.enclosedPocketRegionSucc`: the bridge-free enclosed face set is a pocket
  region whose complement cycle is the arc and follows its boundary.
* `OsinLoopCut.ofPocketRegion` with the side `s = []` and the arc read backwards as `t`.  The arc is
  `(λ, c)`-quasi-geodesic by the `C`-condition, which also gives `0 ≤ c`, so the empty side is too.
  The transport is `PocketRegion.twoSectionCuts_cellTransport pocketCellTransport`.

With `osinLemma94SameCellPocketInput_of_loopCut sameCellPocketCellFreeValue` (w1-binder-5), this
closes `OsinLemma94SameCellPocketInput`.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, "Hull's small cancellation theorem", through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded SimpleClosedWalkSides

/-- **`SameCellPocketLoopCutStatement` holds.** -/
theorem sameCellPocketLoopCut : SameCellPocketLoopCutStatement.{u, w, v} := by
  intro G _ Lambda D lambda c mu eps rho W hW Delta hlea i d hd hface hor C hC hCi x hx hch
  classical
  obtain ⟨A, E, hCmem, himem⟩ :=
    SameCellPocketEnclosed.exists_enclosedPocket Delta i hd hface hor hCi hx hch
  obtain ⟨Delta', faces', i', A', ⟨equiv⟩, E', hfree', hi', e, he⟩ :=
    EnclosedBridgeDoubling.arcDoublingOutput _ Delta _ i A rfl E himem
  obtain ⟨kC, hkC, hkCeq⟩ := List.getElem_of_mem hC
  have hcellC : cell Delta ⟨kC, hkC⟩ = C := hkCeq
  have hC'f : (cell Delta' (e ⟨kC, hkC⟩)).face ∈ faces' := by
    refine (he ⟨kC, hkC⟩).2.mpr ?_
    rw [hcellC]
    exact hCmem
  obtain ⟨P, hPfaces, hPcycle, hfollows⟩ :=
    EnclosedPocketRegion.enclosedPocketRegionSucc Delta' faces' A'.darts E' hfree'
  have hdec : invDarts Delta' P.outer.cycle = [] ++ invDarts Delta' A'.darts := by
    rw [hPcycle, List.nil_append]
  have harc : IsLambdaCQuasiGeodesicWord D lambda c (dartWord Delta' (invDarts Delta' A'.darts)) :=
    CyclicArc.isLambdaCQuasiGeodesicWord_invDarts_darts_cellDarts hW A'
  have hquasi : ∀ part ∈ [([] : List Delta'.toCombMap.Dart), invDarts Delta' A'.darts],
      IsLambdaCQuasiGeodesicWord D lambda c (dartWord Delta' part) := by
    intro part hpart
    rcases List.mem_cons.mp hpart with rfl | hpart
    · exact isLambdaCQuasiGeodesicWord_nil D lambda c
        (CutSections.c_nonneg_of_isLambdaCQuasiGeodesicWord harc)
    · rw [List.mem_singleton] at hpart
      subst hpart
      exact harc
  have hinP : (cell Delta' (e ⟨kC, hkC⟩)).face ∈ P.faces := by
    rw [hPfaces]
    exact hC'f
  have houtP : (cell Delta' i').face ∉ P.faces := by
    rw [hPfaces]
    exact hi'
  exact ⟨OsinLoopCut.ofPocketRegion equiv hlea P (cell_mem Delta' (e ⟨kC, hkC⟩)) hinP
    (cell_mem Delta' i') houtP [] (invDarts Delta' A'.darts) hdec hquasi (Nat.zero_le _)
    (PocketRegion.twoSectionCuts_cellTransport pocketCellTransport P hfollows houtP A' [] hdec
      hquasi)⟩

end GroupApproximation.GGT.VanKampen

#audit_closed_axioms GroupApproximation.GGT.VanKampen.sameCellPocketLoopCut
