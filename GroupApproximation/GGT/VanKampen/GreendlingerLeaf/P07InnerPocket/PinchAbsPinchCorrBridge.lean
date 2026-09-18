import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchAbsPinchCorrStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.Assembly
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-82: bridges to the corrected enclosed inner pocket

This file links the widened statements of `PinchAbsPinchCorrStatement.lean` to
`GroupApproximation.Full.GL03BPinch.InnerPocketEnclosedTwoArcCorrected` and its pinched form
(`GL03BPinch/Statement.lean`).

* `pinchAbsPinchCorr_pinch_ofPCorr`: the pinched corrected statement gives the
  corrected pinched half.  Drop `hcase` and `hP`, pack `G₁`, `G₂` into the existentials, and take
  the right disjunct.
* `pinchAbsPinchCorr_pinch_ofCorr`: the same, through
  `innerPocketEnclosedTwoArcPinchedCorrected_of_corrected`.
* `pinchAbsPinchCorr_off_ofCorr`: the corrected statement gives the widened four-piece
  reading (right disjunct).
* `pinchAbsPinchCorr_consumer`: **the consumer absorbs the widening.**  The widened
  four-piece reading gives `InnerPocketEnclosedTwoArcCorrected`.  On the left disjunct, rerun the
  proof of `innerPocketEnclosed_of_pieces` (`Assembly.lean`) with `pocketSideBound` and
  `enclosedNormalForm`, and land in the corrected first disjunct.  On the right disjunct the
  corrected conclusion is given.

**LOUD.**  The last two bridges show that `pinchAbsPinchCorr_OffStatement` is EQUIVALENT to
`InnerPocketEnclosedTwoArcCorrected`.  `InnerPocketEnclosedTwoArcCorrected` is not yet proved in
the library.  `GL03BPinch/Endpoint.lean` is a draft outside the library.  It imports the missing
module `GL03BPinchOrder.ORDERMODULE` and uses `GL03BPinchOrder.lakeWalk_reverse_map_alpha_sublist`,
which is defined nowhere.  So this file imports nothing from it, and the endpoints here are
reductions to that statement.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **The corrected pinched half from the pinched corrected enclosed inner pocket.** -/
theorem pinchAbsPinchCorr_pinch_ofPCorr
    (h : GroupApproximation.Full.GL03BPinch.InnerPocketEnclosedTwoArcPinchedCorrected.{u, w, v}) :
    pinchAbsPinchCorr_PinchPart.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hfo hout hinner houter C hC hCf hCa hCb _ _
  exact Or.inr (h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond ⟨G₁, hG₁⟩ ⟨G₂, hG₂⟩ hw
    hout hinner houter hfo C hC hCf hCa hCb)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsPinchCorr_pinch_ofPCorr

/-- **The corrected pinched half from the corrected enclosed inner pocket.** -/
theorem pinchAbsPinchCorr_pinch_ofCorr
    (h : GroupApproximation.Full.GL03BPinch.InnerPocketEnclosedTwoArcCorrected.{u, w, v}) :
    pinchAbsPinchCorr_PinchPart.{u, w, v} :=
  pinchAbsPinchCorr_pinch_ofPCorr
    (GroupApproximation.Full.GL03BPinch.innerPocketEnclosedTwoArcPinchedCorrected_of_corrected h)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsPinchCorr_pinch_ofCorr

/-- **The widened four-piece reading from the corrected enclosed inner pocket.** -/
theorem pinchAbsPinchCorr_off_ofCorr
    (h : GroupApproximation.Full.GL03BPinch.InnerPocketEnclosedTwoArcCorrected.{u, w, v}) :
    pinchAbsPinchCorr_OffStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond h₁ h₂ hw hoff
    hinner houter C hC hCf hCa hCb
  exact Or.inr (h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond h₁ h₂ hw hoff hinner
    houter C hC hCf hCa hCb)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsPinchCorr_off_ofCorr

/-- **The consumer absorbs the widening**: the widened four-piece reading gives the corrected
enclosed inner pocket.  The left branch is the proof of `innerPocketEnclosed_of_pieces`. -/
theorem pinchAbsPinchCorr_consumer (h : pinchAbsPinchCorr_OffStatement.{u, w, v}) :
    GroupApproximation.Full.GL03BPinch.InnerPocketEnclosedTwoArcCorrected.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond h₁ h₂ hw hoff
    hinner houter C hC hCf hCa hCb
  rcases h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond h₁ h₂ hw hoff hinner houter C
    hC hCf hCa hCb with ⟨faces, outerWalk, n, R₁, R₂, A₁, A₂, E, hCF, hdec, hcase, hk₀⟩ | hc
  · left
    have hoff₁ : 0 < A₁.length → (cell X i).face ∉ faces :=
      Assembly.cell_face_not_mem_of_arc_on_walk E A₁ n (fun x hx => by
        rw [hdec]
        exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
          (List.mem_append.mpr (Or.inr hx))))))
    have hoff₂ : 0 < A₂.length → (cell X j).face ∉ faces :=
      Assembly.cell_face_not_mem_of_arc_on_walk E A₂ n (fun x hx => by
        rw [hdec]
        exact List.mem_append.mpr (Or.inr hx))
    have hcell : ∃ k₀ : Fin X.rCellCount, (cell X k₀).face ∉ faces := by
      by_cases hp₁ : 0 < A₁.length
      · exact ⟨i, hoff₁ hp₁⟩
      · by_cases hp₂ : 0 < A₂.length
        · exact ⟨j, hoff₂ hp₂⟩
        · exact hk₀ (by omega) (by omega)
    obtain ⟨k₀, hk₀'⟩ := hcell
    obtain ⟨m, S₁, V₁, S₂, V₂, hdec', hS₁, hS₂, hV⟩ :=
      pocketSideBound D eps X i j a b outerWalk n R₁ (invDarts X A₁.darts) R₂
        (invDarts X A₂.darts) E.nodup hdec
        (by
          rcases hcase with hc | ⟨hfar, hA⟩
          · exact Or.inl hc
          · exact Or.inr ⟨hfar, hA.imp (sideBound_invDarts_eq_nil_iff A₁).mpr
              (sideBound_invDarts_eq_nil_iff A₂).mpr⟩)
    rcases hV with ⟨rfl, rfl⟩ | ⟨_, rfl, rfl⟩
    · exact enclosedNormalForm eps X faces (outerWalk.rotate m) (EnclosedFaceSetSucc.rotate E m) C
        hC hCF k₀ i j A₁ A₂ S₁ S₂ hdec' hoff₁ hoff₂ hk₀' hS₁ hS₂
    · exact enclosedNormalForm eps X faces (outerWalk.rotate m) (EnclosedFaceSetSucc.rotate E m) C
        hC hCF k₀ k₀ i (P07LakeExclusion.emptyArc (cellDarts X k₀)) A₁ S₁ S₂
        (by rw [P07LakeExclusion.invDarts_emptyArc]; exact hdec') (fun _ => hk₀') hoff₁ hk₀' hS₁
        hS₂
  · exact hc

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsPinchCorr_consumer

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
