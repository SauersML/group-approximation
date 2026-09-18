import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.NoPlanarDegenPinchStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.NoPlanarDegenStepProof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceArcsAuditPinchProof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitnessDart
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-33: the corrected consumer through the pinch-bounded audit

This module proves `FourPieceWitness.arcAuditResidual_of_noPlanarDegenerate_pinch`.  It takes the
no-walk residual, the proved `ArcsAuditPinchStatement`, and the one gap
`NoPlanarDegenPinchReadStatement` (`NoPlanarDegenPinchStatement.lean`).  It does not take the
FALSE `ArcsAuditStatement`, `PocketFourPieceWitnessNoninterleaveStatement` or `FourBlockStatement`.

## Proof route

Split on whether `F = witnessFaces a b K C.face` has a witness walk.
* **No walk:** the residual `hdeg`.
* **A walk, right disjunct of the gap:** the target conclusion directly.
* **A walk, left disjunct:** branch 1 with `faces = F`, built as in lane 28:
  * `C.face ∈ F` is `mem_witnessFaces_self`;
  * `F ⊆ sideFaces K.walk` is `witnessFaces_subset_sideFaces`;
  * clause 2' comes from `dart_clause`;
  * clause 3 is the left disjunct.
  Clauses 4a and 4b come from `hpinch`.
  * 4a: an off-`G₁` complement entry of a rotation block is an off-`G₁` entry of the inverse walk
    (`exists_not_mem_invDarts_of_block`).  So (good-a) supplies pinch-freeness of `G₁`.
  * 4b: under an all-`G₁` inverse walk, (good-b) supplies the pinch bound.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

section Block

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {X : DiscDiagram.{u, w, v} W}

/-- **A rotation block with an off-`S` complement entry gives an off-`S` entry of the walk.** -/
theorem exists_not_mem_invDarts_of_block {ow U V S : List X.toCombMap.Dart} {m : ℕ}
    (hm : (invDarts X ow).rotate m = U ++ V) (hV : ∃ e ∈ V, e ∉ S) :
    ∃ e ∈ invDarts X ow, e ∉ S := by
  obtain ⟨e, he, hne⟩ := hV
  have h1 : e ∈ (invDarts X ow).rotate m := by
    rw [hm]
    exact List.mem_append.mpr (Or.inr he)
  exact ⟨e, List.mem_rotate.mp h1, hne⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.exists_not_mem_invDarts_of_block

end Block

/-- **The gap is weaker than the target**: take the right disjunct. -/
theorem pinchRead_of_arcAuditResidual
    (h : PocketFourPieceArcAuditResidualStatement.{u, w, v}) :
    NoPlanarDegenPinchReadStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw
    hout hinner houter C hC hCf hCa hCb _ _ _
  exact Or.inr (h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout
    hinner houter C hC hCf hCa hCb)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.pinchRead_of_arcAuditResidual

/-- **Lane gl-p07-33: the corrected consumer.**  The target from the no-walk residual, the proved
pinch-bounded arc audit, and the one gap `NoPlanarDegenPinchReadStatement`. -/
theorem arcAuditResidual_of_noPlanarDegenerate_pinch
    (hdeg : NoPlanarDegenerateStatement.{u, w, v})
    (hpinch : ArcsAuditPinchStatement.{u, w, v})
    (hread : NoPlanarDegenPinchReadStatement.{u, w, v}) :
    PocketFourPieceArcAuditResidualStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hout hinner houter C hC hCf hCa hCb
  rcases Classical.em (∃ outerWalk : List X.toCombMap.Dart,
      EnclosedFaceSetSucc X (witnessFaces a b K C.face) outerWalk ∧
        ∀ d ∈ outerWalk,
          X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ witnessFaces a b K C.face) with
    ⟨outerWalk, E, hnb⟩ | hno
  · rcases hread D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout
        hinner houter C hC hCf hCa hCb outerWalk E hnb with
      ⟨hn1, hn2, hn3, hn4, hg₁a, hg₁b, hg₂a, hg₂b⟩ | hres
    · obtain ⟨h4a₁, h4b₁, h4a₂, h4b₂⟩ := hpinch D eps X a b K hij hai hbi hab hlabel hW hfirst
        hsecond G₁ hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb
      exact Or.inl ⟨witnessFaces a b K C.face, outerWalk, E, mem_witnessFaces_self hCf,
        witnessFaces_subset_sideFaces,
        fun d hd => Or.inr (Or.inr (dart_clause hw hCa hCb E hnb d hd)),
        hn1, hn2, hn3, hn4,
        fun m U V hm hU hV =>
          h4a₁ (hg₁a (exists_not_mem_invDarts_of_block hm hV)) m U V hm hU hV,
        fun hall => h4b₁ (hg₁b hall) hall,
        fun m U V hm hU hV =>
          h4a₂ (hg₂a (exists_not_mem_invDarts_of_block hm hV)) m U V hm hU hV,
        fun hall => h4b₂ (hg₂b hall) hall⟩
    · exact hres
  · exact hdeg D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout
      hinner houter C hC hCf hCa hCb hno

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.arcAuditResidual_of_noPlanarDegenerate_pinch

/-- **The corrected consumer with the arc audit discharged** by the proved `arcsAuditPinch`. -/
theorem arcAuditResidual_of_noPlanarDegenerate_pinchRead
    (hdeg : NoPlanarDegenerateStatement.{u, w, v})
    (hread : NoPlanarDegenPinchReadStatement.{u, w, v}) :
    PocketFourPieceArcAuditResidualStatement.{u, w, v} :=
  arcAuditResidual_of_noPlanarDegenerate_pinch hdeg arcsAuditPinch hread

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.arcAuditResidual_of_noPlanarDegenerate_pinchRead

/-- **The target from the two gaps of lane gl-p07-33**: the local-step no-walk statement and
the pinched reading. -/
theorem arcAuditResidual_of_noPlanarDegenStep_pinchRead
    (hstep : NoPlanarDegenStepStatement.{u, w, v})
    (hread : NoPlanarDegenPinchReadStatement.{u, w, v}) :
    PocketFourPieceArcAuditResidualStatement.{u, w, v} :=
  arcAuditResidual_of_noPlanarDegenerate_pinchRead (noPlanarDegenerate_of_step hstep) hread

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.arcAuditResidual_of_noPlanarDegenStep_pinchRead

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
