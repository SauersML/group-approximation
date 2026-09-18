import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepPinchLobeFace
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-55: the prefix residual from the open-entry residual

Lane gl-p07-55.  Certifies no printed sentence on its own.  NOT COMPILED.

* `witnessStepPinchLobe_pinchCut_of_pinchLobe`: `WitnessStepPinchCutStatement` from
  `WitnessStepPinchLobeStatement`.
* `witnessStepPinchLobe_pinchLobe_of_pinchCut`: the converse.
* `witnessStepPinchLobe_pinchCut_of_pinchOff`: `WitnessStepPinchCutStatement` from
  `WitnessStepPinchOffStatement` (the converse of gl-p07-54, argued there on paper).
* `witnessStepPinchLobe_iff_pinchOff`: so `PinchLobe ↔ PinchOff`, and both are equivalent to
  `PinchCut`.

See `WitnessStepPinchLobeStatement.lean` for the route, the truth check and the LOUD notes.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- **Lane gl-p07-55: the prefix residual from the open-entry residual.** -/
theorem witnessStepPinchLobe_pinchCut_of_pinchLobe (h : WitnessStepPinchLobeStatement.{u, w, v}) :
    WitnessStepPinchCutStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst
    hsecond G₁ hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb hlab
  obtain ⟨hFa, hFb, hFi, hFj⟩ := witnessStepPinchLobe_faces (K := K) hw hCa hCb
  rcases h D eps X a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst hsecond G₁
      hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb
      hlab with hfwd | hbwd
  · refine Or.inl fun n s t x y hr hcell hside hblock hcorner hpinch pre mid post hcurve e he
      heF => ?_
    have hopen : IsOpenFace a b K C.face (X.toCombMap.faceOf e) :=
      (mem_witnessFaces_iff.mp heF).1
    have het : e ∈ witnessSublistCurve a b G₁ G₂ := by
      rw [hcurve]
      exact List.mem_append_left _ he
    exact hfwd n s t x y hr hcell hside hblock hcorner hpinch pre mid post hcurve e he hopen
      (witnessStepPinchLobe_mem_of_faceOf_mem E hFa hFb hFi hFj het heF)
  · exact Or.inr hbwd

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinchLobe_pinchCut_of_pinchLobe

/-- **The converse: the open-entry residual from the prefix residual.**  An entry of `pre` on the
inverted walk has its face in `F`, by `hnb`. -/
theorem witnessStepPinchLobe_pinchLobe_of_pinchCut (h : WitnessStepPinchCutStatement.{u, w, v}) :
    WitnessStepPinchLobeStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst
    hsecond G₁ hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb hlab
  rcases h D eps X a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst hsecond G₁
      hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb
      hlab with hfwd | hbwd
  · refine Or.inl fun n s t x y hr hcell hside hblock hcorner hpinch pre mid post hcurve e he
      _ hel => ?_
    have hF := hnb _ (witnessStepCorner_alpha_mem_of_mem_invDarts hel)
    rw [X.toCombMap.alpha_involutive e] at hF
    exact hfwd n s t x y hr hcell hside hblock hcorner hpinch pre mid post hcurve e he hF
  · exact Or.inr hbwd

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinchLobe_pinchLobe_of_pinchCut

/-- **The converse of gl-p07-54: the prefix residual from the off-lobe pinch residual.**  With `y`
before `x`, the forward `StepNext` cannot be its first clause (`witnessStepPinchLobe_not_both`),
so it is the wrap-around clause, whose prefix is `pre` and is off the inverted walk. -/
theorem witnessStepPinchLobe_pinchCut_of_pinchOff (h : WitnessStepPinchOffStatement.{u, w, v}) :
    WitnessStepPinchCutStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst
    hsecond G₁ hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb hlab
  obtain ⟨hFa, hFb, hFi, hFj⟩ := witnessStepPinchLobe_faces (K := K) hw hCa hCb
  rcases h D eps X a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst hsecond G₁
      hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb
      hlab with hfwd | hbwd
  · refine Or.inl fun n s t x y hr hcell hside hblock hcorner hpinch pre mid post hcurve e he
      heF => ?_
    have hnd := witnessSublist_curve_nodup a b G₁ G₂
    have het : e ∈ witnessSublistCurve a b G₁ G₂ := by
      rw [hcurve]
      exact List.mem_append_left _ he
    rcases hfwd n s t x y hr hcell hside hblock hcorner hpinch with
      ⟨u', v', z', hxy⟩ | ⟨u', z', hyz, hu'⟩
    · exact witnessStepPinchLobe_not_both hnd hcurve hxy
    · have hnd' : (u' ++ y :: z').Nodup := by
        rw [← hyz]
        exact hnd
      obtain ⟨hup, -⟩ :=
        WitnessCurveSublistList.append_cons_inj_of_nodup hnd' (hyz.symm.trans hcurve)
      rw [← hup] at he
      exact hu' e he (witnessStepPinchLobe_mem_of_faceOf_mem E hFa hFb hFi hFj het heF)
  · exact Or.inr hbwd

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinchLobe_pinchCut_of_pinchOff

/-- **The off-lobe pinch residual from the open-entry residual.** -/
theorem witnessStepPinchLobe_pinchOff_of_pinchLobe (h : WitnessStepPinchLobeStatement.{u, w, v}) :
    WitnessStepPinchOffStatement.{u, w, v} :=
  witnessStepPinchCut_pinchOff_of_pinchCut (witnessStepPinchLobe_pinchCut_of_pinchLobe h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinchLobe_pinchOff_of_pinchLobe

/-- **LOUD: the three residuals are equivalent.**  `PinchLobe ↔ PinchOff`; with the lemmas above,
both are equivalent to `PinchCut`. -/
theorem witnessStepPinchLobe_iff_pinchOff :
    WitnessStepPinchLobeStatement.{u, w, v} ↔ WitnessStepPinchOffStatement.{u, w, v} :=
  ⟨witnessStepPinchLobe_pinchOff_of_pinchLobe, fun h =>
    witnessStepPinchLobe_pinchLobe_of_pinchCut (witnessStepPinchLobe_pinchCut_of_pinchOff h)⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinchLobe_iff_pinchOff

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
