import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixO52Surgery
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixO52Values
import GroupApproximation.Meta.AxiomGuard

/-!
# O52 at least area

Osin, arXiv:math/0411039v3, O52: "If the third condition is not [satisfied], then
`φ(s_1) φ(∂Π) φ(s_1)⁻¹ = φ(∂Σ)` … we can cut the subdiagram … and fill the obtained hole
with a diagram without `R`-cells reducing the number of `R`-cells by 2.  This contradicts
the assumption that `Δ` is reduced."  Here "reduced" is least area
(`DiscDiagram.LeastArea`).

`Embedded.o52LeastArea` proves `O52LeastAreaStatement`.  For a contiguity region `Γ` of a
relator cell `Π` to a different relator cell `Σ`, with both arcs nonempty, suppose the
inverse target carrier equals the conjugated source carrier.  Collapse `Γ`
(`ContiguityGeometry.innerGRegion`); `Π` meets it along the last dart of the source arc
and `Σ` along the last dart of the target arc.  The merged word reads `1`
(`o52_mergedValue_eq_one`, from the region's own boundary value and the assumed
equality), so the boundary value is a relator product with two relator factors fewer
(`Surgery.InnerGRegion.isRelatorProduct_sub_two`), contradicting least area.
-/

namespace GroupApproximation.GGT.VanKampen.Embedded

open HullSC RelatorDefectBudget

universe u w v

/-- **O52 at least area.** -/
theorem o52LeastArea : O52LeastAreaStatement.{u, w, v} := by
  intro G _ Lambda D W eps Delta faces Gamma target htarget hlea hne hs ht heq
  classical
  have hsd : Gamma.sourceArc.darts ≠ [] := Gamma.sourceArc.darts_ne_nil_of_length_pos hs
  obtain ⟨arcT, harcT⟩ : ∃ a : CyclicArc (cellDarts Delta target),
      a = Gamma.targetArcAtSome target htarget := ⟨_, rfl⟩
  have hlenT : arcT.length = Gamma.targetArc.length :=
    (congrArg CyclicArc.length harcT).trans
      (CyclicArc.length_cast (congrArg (targetDarts Delta) htarget) Gamma.targetArc)
  have htd : arcT.darts ≠ [] :=
    arcT.darts_ne_nil_of_length_pos ((congrArg (fun n => 0 < n) hlenT).mpr ht)
  have hTB : targetBoundaryDarts Delta Gamma.target Gamma.targetArc = arcT.reverseDarts := by
    rw [harcT]
    exact targetBoundaryDarts_cast htarget Gamma.targetArc
  -- the boundary cycle of the region, from the two shared edges
  have hcycle : (Gamma.innerGRegion hlea).boundary.cycle =
      Delta.toCombMap.alpha (Gamma.sourceArc.darts.getLast hsd) ::
        ((Gamma.sourceArc.darts.dropLast.reverse.map Delta.toCombMap.alpha ++
            Gamma.rightSide) ++
          Delta.toCombMap.alpha (arcT.darts.getLast htd) ::
            (arcT.darts.dropLast.reverse.map Delta.toCombMap.alpha ++ Gamma.leftSide)) := by
    show Gamma.boundary.cycle = _
    rw [Gamma.boundary_decomposition, hTB, Gamma.sourceArc.reverseDarts_eq_cons hsd,
      arcT.reverseDarts_eq_cons htd]
    simp only [List.cons_append, List.append_assoc]
  -- the two cells, read from the shared edges
  have hPcyc : Delta.toCombMap.IsFaceCycle (Gamma.sourceArc.darts.getLast hsd ::
      (Gamma.sourceArc.rotated.drop Gamma.sourceArc.length ++
        Gamma.sourceArc.darts.dropLast)) := by
    rw [← Gamma.sourceArc.rotated_rotate_pred hsd, Gamma.sourceArc.rotated_eq_rotate,
      List.rotate_rotate]
    exact (Delta.faceBoundary (cell Delta Gamma.source).face).isFaceCycle.rotate _
  have hPface : Delta.toCombMap.faceOf (Gamma.sourceArc.darts.getLast hsd) =
      (cell Delta Gamma.source).face :=
    ((Delta.faceBoundary (cell Delta Gamma.source).face).mem_iff _).mp
      (Gamma.sourceArc.mem_cycle_of_mem_darts (List.getLast_mem hsd))
  have hScyc : Delta.toCombMap.IsFaceCycle (arcT.darts.getLast htd ::
      (arcT.rotated.drop arcT.length ++ arcT.darts.dropLast)) := by
    rw [← arcT.rotated_rotate_pred htd, arcT.rotated_eq_rotate, List.rotate_rotate]
    exact (Delta.faceBoundary (cell Delta target).face).isFaceCycle.rotate _
  have hSface : Delta.toCombMap.faceOf (arcT.darts.getLast htd) = (cell Delta target).face :=
    ((Delta.faceBoundary (cell Delta target).face).mem_iff _).mp
      (arcT.mem_cycle_of_mem_darts (List.getLast_mem htd))
  -- values
  have hdS := listVal_dartWord_darts (Delta := Delta) Gamma.sourceArc hsd
  have hdT := listVal_dartWord_darts (Delta := Delta) arcT htd
  have hrS := listVal_dartWord_rotated (Delta := Delta) Gamma.sourceArc
  have hcar : RelLetter.listVal (Gamma.targetInverseCarrier target htarget) =
      (RelLetter.listVal (dartWord Delta arcT.darts))⁻¹ *
        (RelLetter.listVal (dartWord Delta (arcT.rotated.drop arcT.length)))⁻¹ := by
    rw [harcT]
    exact listVal_revInv_rotate _
  have F1 : (RelLetter.listVal (dartWord Delta Gamma.sourceArc.darts.dropLast) *
        (Delta.label (Gamma.sourceArc.darts.getLast hsd)).val)⁻¹ *
      RelLetter.listVal (dartWord Delta Gamma.rightSide) *
      (RelLetter.listVal (dartWord Delta arcT.darts.dropLast) *
        (Delta.label (arcT.darts.getLast htd)).val)⁻¹ *
      RelLetter.listVal (dartWord Delta Gamma.leftSide) = 1 := by
    have h := cycle_value_eq_one_of_shelling Gamma.boundary Gamma.pasting.choose_spec
    rw [Gamma.boundary_decomposition, hTB] at h
    simp only [dartWord_append, RelWord.listVal_append, CyclicArc.reverseDarts,
      listVal_dartWord_reverse_alpha, hdS, hdT] at h
    exact h
  have F2 : (RelLetter.listVal (dartWord Delta arcT.darts.dropLast) *
        (Delta.label (arcT.darts.getLast htd)).val)⁻¹ *
      (RelLetter.listVal (dartWord Delta (arcT.rotated.drop arcT.length)))⁻¹ =
      (RelLetter.listVal (dartWord Delta Gamma.rightSide))⁻¹ *
        (RelLetter.listVal (dartWord Delta Gamma.sourceArc.darts.dropLast) *
          (Delta.label (Gamma.sourceArc.darts.getLast hsd)).val *
          RelLetter.listVal
            (dartWord Delta (Gamma.sourceArc.rotated.drop Gamma.sourceArc.length))) *
        RelLetter.listVal (dartWord Delta Gamma.rightSide) := by
    rw [← hdT, ← hdS, ← hrS, ← hcar]
    exact heq
  have hval : RelLetter.listVal (dartWord Delta
      ((arcT.darts.dropLast.reverse.map Delta.toCombMap.alpha ++ Gamma.leftSide) ++
        (Gamma.sourceArc.rotated.drop Gamma.sourceArc.length ++
          Gamma.sourceArc.darts.dropLast) ++
        (Gamma.sourceArc.darts.dropLast.reverse.map Delta.toCombMap.alpha ++
          Gamma.rightSide) ++
        (arcT.rotated.drop arcT.length ++ arcT.darts.dropLast))) = 1 := by
    simp only [dartWord_append, RelWord.listVal_append, listVal_dartWord_reverse_alpha]
    exact o52_mergedValue_eq_one _ _ _ _ _ _ _ _ F1 F2
  -- the surgery
  have hprod := (Gamma.innerGRegion hlea).isRelatorProduct_sub_two hne hPcyc hPface hScyc
    hSface hcycle hval
  have hcount : 2 ≤ Delta.rCellCount := by
    have h1 := Gamma.source.isLt
    have h2 := target.isLt
    have h3 : (Gamma.source : ℕ) ≠ target := fun h => hne (Fin.ext h)
    omega
  have hle := hlea hprod
  omega

end GroupApproximation.GGT.VanKampen.Embedded

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.o52LeastArea
