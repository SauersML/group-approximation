import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepDescentStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepPinchArcProof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepPinchParityProof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepSkipProof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepCornerProof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepBlockProof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepSideProof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessCurveStepProof
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-58: the pinch residuals from the winding-one residual

Lane gl-p07-58.  Certifies no printed sentence on its own.  NOT COMPILED.

* `witnessStepDescent_false_of_entry` (pure lists): take a pinch `(x, y)` with
  `w = pre ++ y :: (mid ++ x :: post)` and an entry step `(x', y')` with `x' ∉ pre`, `y' ∈ pre`.
  These are two distinct descents of `l` against `w`.  So the gap sum is at least `2 |w|`, and
  `|w| > 0`, which contradicts the bound `≤ |w|`.
* `witnessStepDescent_parity_of_descent`: `WitnessStepPinchParityStatement` from
  `WitnessStepDescentStatement`.
* `witnessStepDescent_arc_of_descent`: `WitnessStepPinchArcStatement` from it.
* `witnessStepDescent_skip_of_descent`: the wire to `WitnessStepSkipStatement`.
* `witnessStepDescent_curveStep_of_descent`: up the chain to `WitnessCurveSublistStepStatement`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- **A pinch together with an entry step into the prefix breaks the winding-one bound.**
`(x, y)` is a descent because `y` sits at `|pre|` and `x` after it.  `(x', y')` is a descent
because `y'` sits before `|pre|` and `x'` at or after it.  They differ because `y ∉ pre` while
`y' ∈ pre`. -/
theorem witnessStepDescent_false_of_entry {α : Type*} {w l s t s' t' pre mid post : List α}
    {n n' : ℕ} {x y x' y' : α} (hw : w.Nodup)
    (hbound : witnessStepDescent_gapSum (fun e => witnessStepDescent_pos e w) w.length
      (witnessStepDescent_steps l) ≤ w.length)
    (hr : l.rotate n = s ++ x :: y :: t) (hcurve : w = pre ++ y :: (mid ++ x :: post))
    (hr' : l.rotate n' = s' ++ x' :: y' :: t') (hx' : x' ∉ pre) (hy' : y' ∈ pre) : False := by
  have hw' := hw
  rw [hcurve] at hw'
  have hy : y ∉ pre := fun hy => (List.nodup_append.mp hw').2.2 y hy y (by simp) rfl
  have hx : x ∉ pre := witnessStepDescent_not_mem_pre_right hw hcurve
  have e1 : witnessStepDescent_pos y w = pre.length := by
    rw [hcurve]
    exact witnessStepDescent_pos_split hy
  have e2 : pre.length ≤ witnessStepDescent_pos x w := by
    rw [hcurve]
    exact witnessStepDescent_length_le_pos hx
  have e3 : witnessStepDescent_pos y' w < pre.length := by
    rw [hcurve]
    exact witnessStepDescent_pos_lt_of_mem _ pre hy'
  have e4 : pre.length ≤ witnessStepDescent_pos x' w := by
    rw [hcurve]
    exact witnessStepDescent_length_le_pos hx'
  have hd1 : ¬ witnessStepDescent_pos x w < witnessStepDescent_pos y w := by omega
  have hd2 : ¬ witnessStepDescent_pos x' w < witnessStepDescent_pos y' w := by omega
  have hne : (x, y) ≠ (x', y') := by
    intro heq
    have hyy : y = y' := congrArg Prod.snd heq
    exact hy (by rw [hyy]; exact hy')
  have htwo := witnessStepDescent_two_le_turnSum (f := fun e => witnessStepDescent_pos e w)
    (N := w.length) hne hd1 hd2 (witnessStepDescent_steps l) (witnessStepDescent_mem_steps hr)
    (witnessStepDescent_mem_steps hr')
  have heq := witnessStepDescent_gapSum_steps (fun e => witnessStepDescent_pos e w) w.length l
    (fun e => witnessStepDescent_pos_le_length e w)
  have hlen : 0 < w.length := List.length_pos_of_mem (a := y) (by rw [hcurve]; simp)
  omega

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepDescent_false_of_entry

/-- **Lane gl-p07-58: the entry-step residual from the winding-one residual.**  The pinch and
the entry step of the parity statement are two distinct descents
(`witnessStepDescent_false_of_entry`).  The curve-first, face and fan data are not used. -/
theorem witnessStepDescent_parity_of_descent (h : WitnessStepDescentStatement.{u, w, v}) :
    WitnessStepPinchParityStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst
    hsecond G₁ hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb hlab
  rcases h D eps X a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst hsecond G₁
      hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb
      hlab with hfwd | hbwd
  · refine Or.inl fun _ _ _ _ _ hr _ _ _ _ _ _ _ _ hcurve _ _ _ _ _ hr' hx' hy' _ _ => ?_
    exact witnessStepDescent_false_of_entry (witnessSublist_curve_nodup a b G₁ G₂) hfwd hr
      hcurve hr' hx' hy'
  · exact Or.inr hbwd

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepDescent_parity_of_descent

/-- **Lane gl-p07-58: the curve-first residual from the winding-one residual.** -/
theorem witnessStepDescent_arc_of_descent (h : WitnessStepDescentStatement.{u, w, v}) :
    WitnessStepPinchArcStatement.{u, w, v} :=
  witnessStepPinchArc_arc_of_parity (witnessStepDescent_parity_of_descent h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepDescent_arc_of_descent

/-- **Lane gl-p07-58: the skip residual from the winding-one residual.** -/
theorem witnessStepDescent_skip_of_descent (h : WitnessStepDescentStatement.{u, w, v}) :
    WitnessStepSkipStatement.{u, w, v} :=
  witnessStepPinchParity_skip_of_parity (witnessStepDescent_parity_of_descent h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepDescent_skip_of_descent

/-- **Lane gl-p07-58: the local step residual from the winding-one residual**, through the
skip, corner, block, side and step residuals. -/
theorem witnessStepDescent_curveStep_of_descent (h : WitnessStepDescentStatement.{u, w, v}) :
    WitnessCurveSublistStepStatement.{u, w, v} :=
  witnessCurveSublistStep_of_witnessStepResidual
    (witnessStepResidual_of_witnessStepSide
      (witnessStepSideResidual_of_witnessStepBlock
        (witnessStepBlockResidual_of_witnessStepCorner
          (witnessStepCorner_of_witnessStepSkip (witnessStepDescent_skip_of_descent h)))))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepDescent_curveStep_of_descent

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
