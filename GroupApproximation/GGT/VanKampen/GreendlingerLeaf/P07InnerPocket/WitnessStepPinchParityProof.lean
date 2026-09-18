import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepPinchParityStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepPinchProof
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-56: the open-entry residual from the entry-step residual

Lane gl-p07-56.  Certifies no printed sentence on its own.  NOT COMPILED.

* `witnessStepPinchParity_pinchLobe_of_parity`: `WitnessStepPinchLobeStatement` from
  `WitnessStepPinchParityStatement` (Pieces 1 and 2 of `WitnessStepPinchParityWalk.lean`).
* `witnessStepPinchParity_parity_of_pinchLobe`: the converse.
* `witnessStepPinchParity_iff_pinchLobe`: LOUD, the two are equivalent.
* `witnessStepPinchParity_pinchOff_of_parity`, `witnessStepPinchParity_pinch_of_parity`,
  `witnessStepPinchParity_skip_of_parity`: the wires to `PinchOff`, `Pinch` and `WitnessStepSkip`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- **Lane gl-p07-56: the open-entry residual from the entry-step residual.**  An open `e ∈ pre`
on the walk, with `y ∈ l` off `pre`, gives an entry step into `pre` (Piece 2); it is a fan
(Piece 1) and looks into `F` (`hnb`). -/
theorem witnessStepPinchParity_pinchLobe_of_parity
    (h : WitnessStepPinchParityStatement.{u, w, v}) :
    WitnessStepPinchLobeStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst
    hsecond G₁ hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb hlab
  rcases h D eps X a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst hsecond G₁
      hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb
      hlab with hfwd | hbwd
  · refine Or.inl fun n s t x y hr hcell hside hblock hcorner hpinch pre mid post hcurve e he
      _ hel => ?_
    obtain ⟨n', s', x', y', t', hr', hx', hy'⟩ :=
      witnessStepPinchParity_entry hel he (witnessStepPinchParity_mem_of_rotate hr)
        (witnessStepPinchParity_not_mem_pre (witnessSublist_curve_nodup a b G₁ G₂) hcurve)
    exact hfwd n s t x y hr hcell hside hblock hcorner hpinch pre mid post hcurve n' s' t' x' y'
      hr' hx' hy' (witnessStepPinchParity_face_of_rotate hnb hr')
      (witnessStepPinchParity_turn_fan E hr')
  · exact Or.inr hbwd

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinchParity_pinchLobe_of_parity

/-- **The converse.**  The second dart `y'` of an entry step lies in `pre` and on the walk, and its
face is in `F`, so it is open.  The open-entry residual rules it out. -/
theorem witnessStepPinchParity_parity_of_pinchLobe
    (h : WitnessStepPinchLobeStatement.{u, w, v}) :
    WitnessStepPinchParityStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst
    hsecond G₁ hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb hlab
  rcases h D eps X a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst hsecond G₁
      hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb
      hlab with hfwd | hbwd
  · refine Or.inl fun n s t x y hr hcell hside hblock hcorner hpinch pre mid post hcurve n' s' t'
      x' y' hr' _ hy' hF _ => ?_
    exact hfwd n s t x y hr hcell hside hblock hcorner hpinch pre mid post hcurve y' hy'
      (mem_witnessFaces_iff.mp hF).1 (witnessStepPinchParity_mem_of_rotate hr')
  · exact Or.inr hbwd

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinchParity_parity_of_pinchLobe

/-- **LOUD: the entry-step residual is equivalent to the open-entry residual.** -/
theorem witnessStepPinchParity_iff_pinchLobe :
    WitnessStepPinchParityStatement.{u, w, v} ↔ WitnessStepPinchLobeStatement.{u, w, v} :=
  ⟨witnessStepPinchParity_pinchLobe_of_parity, witnessStepPinchParity_parity_of_pinchLobe⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinchParity_iff_pinchLobe

/-- **The off-lobe pinch residual from the entry-step residual.** -/
theorem witnessStepPinchParity_pinchOff_of_parity
    (h : WitnessStepPinchParityStatement.{u, w, v}) :
    WitnessStepPinchOffStatement.{u, w, v} :=
  witnessStepPinchLobe_pinchOff_of_pinchLobe (witnessStepPinchParity_pinchLobe_of_parity h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinchParity_pinchOff_of_parity

/-- **The pinch residual from the entry-step residual.** -/
theorem witnessStepPinchParity_pinch_of_parity
    (h : WitnessStepPinchParityStatement.{u, w, v}) :
    WitnessStepPinchStatement.{u, w, v} :=
  witnessStepPinch_of_witnessStepPinchOff (witnessStepPinchParity_pinchOff_of_parity h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinchParity_pinch_of_parity

/-- **The skip residual from the entry-step residual.** -/
theorem witnessStepPinchParity_skip_of_parity
    (h : WitnessStepPinchParityStatement.{u, w, v}) :
    WitnessStepSkipStatement.{u, w, v} :=
  witnessStepSkip_of_witnessStepPinch (witnessStepPinchParity_pinch_of_parity h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinchParity_skip_of_parity

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
