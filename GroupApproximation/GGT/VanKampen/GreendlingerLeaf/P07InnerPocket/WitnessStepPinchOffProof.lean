import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepPinchOffFace
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitnessDart
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-53: the pinch residual from the off-lobe pinch residual

Lane gl-p07-53.  Certifies no printed sentence on its own.  NOT COMPILED.

`witnessStepPinch_of_witnessStepPinchOff` proves `WitnessStepPinchStatement` from
`WitnessStepPinchOffStatement`.  Run the off-lobe residual on the same data.  The backward
disjunct passes through unchanged.  In the forward disjunct, every pinch is an off-lobe pinch
(`witnessStepPinchOff_at_of_pinchAt`), using the face facts of the premises:
* the witness faces are off `a` and `b` (`not_mem_left/right_of_mem_witnessFaces`);
* the faces of `Π_i` and `Π_j` are off the witness faces, since the witness faces lie on the side
  of `K.walk` (`witnessFaces_subset_sideFaces`) and the cells do not
  (`PocketClass.cell_face_not_mem_sideFaces` on `K.firstArc` and `K.secondArc`).

See `WitnessStepPinchOffStatement.lean` for the truth check and the LOUD notes: the two residuals
are logically equivalent, and the off-lobe one is smaller only in proof content.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- **Lane gl-p07-53: the pinch residual from the residual at off-lobe pinches.** -/
theorem witnessStepPinch_of_witnessStepPinchOff (h : WitnessStepPinchOffStatement.{u, w, v}) :
    WitnessStepPinchStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst
    hsecond G₁ hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb hlab
  rcases h D eps X a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst hsecond G₁
      hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb
      hlab with hfwd | hbwd
  · refine Or.inl fun n s t x y hr hcell hside hblock hcorner hpinch => ?_
    have hFa : ∀ f ∈ witnessFaces a b K C.face, f ∉ a.1 :=
      fun f hf => not_mem_left_of_mem_witnessFaces hCa hf
    have hFb : ∀ f ∈ witnessFaces a b K C.face, f ∉ b.1 :=
      fun f hf => not_mem_right_of_mem_witnessFaces hCb hf
    have hFi : (cell X i).face ∉ witnessFaces a b K C.face := fun hf =>
      PocketClass.cell_face_not_mem_sideFaces hw K.firstArc K.firstArc_pos
        (fun _ hd => PocketClass.mem_walk_of_mem_invDarts_firstArc K hd)
        (witnessFaces_subset_sideFaces hf)
    have hFj : (cell X j).face ∉ witnessFaces a b K C.face := fun hf =>
      PocketClass.cell_face_not_mem_sideFaces hw K.secondArc K.secondArc_pos
        (fun _ hd => PocketClass.mem_walk_of_mem_invDarts_secondArc K hd)
        (witnessFaces_subset_sideFaces hf)
    exact hfwd n s t x y hr hcell hside hblock hcorner
      (witnessStepPinchOff_at_of_pinchAt E hnb hFa hFb hFi hFj hG₁ hG₂ hr hpinch)
  · exact Or.inr hbwd

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinch_of_witnessStepPinchOff

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
