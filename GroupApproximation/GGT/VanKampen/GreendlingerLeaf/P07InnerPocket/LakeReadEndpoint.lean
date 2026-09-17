import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.LakeReadStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.LakeReadRotation
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-18: reductions around the corrected lake reading

The context is Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).

`PocketFourPieceLakeReadStatement` is **false** (see `LakeReadStatement.lean`).  So the endpoints
`pocketFourPieceLakeRead`, `pocketFourPieceOff := pocketFourPieceOff_of_lakeRead …` and
`innerPocketEnclosed := innerPocketEnclosed_of_lakeRead …` are **not** authored here.  This file
proves instead:
* `lakeReadCore_of_lakeRead`: the corrected statement is a weakening of the target.
* `lakeReadCore_of_some`: the residual gives the corrected statement.  Every outer walk with the
  same darts is a rotation (`EnclosedFaceSetSucc.eq_rotate_of_mem_iff`), so shift `n`.
* `lakeReadSome_of_core`: the corrected statement gives the residual, by the lake fill.
* `fourPieceInput_of_lakeReadSome` and `boundedFourPiece_of_lakeReadSome`: the residual gives lane
  11's `SideBoundFourPieceInputStatement`, and so the ε-bounded four-piece decomposition.

The remaining gap to `innerPocketEnclosed` is the degenerate off-cell clause of
`PocketFourPieceOffStatement` (both contact arcs empty, both arcs empty).  That clause needs a face
set that is **not** lake-filled.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse
  Surgery.MapCollapse.ExteriorComponent

/-- **Every rotation of a rotation of a nonempty list can be rotated back to any given rotation.** -/
theorem LakeRead.exists_rotate_rotate_eq {α : Type*} (l : List α) (k n₀ : ℕ) (hl : l ≠ []) :
    ∃ n, (l.rotate k).rotate n = l.rotate n₀ := by
  have hℓ : 0 < l.length := List.length_pos_iff.mpr hl
  have hlt : k % l.length < l.length := Nat.mod_lt _ hℓ
  refine ⟨l.length - k % l.length + n₀, ?_⟩
  rw [← List.rotate_mod l k, List.rotate_rotate]
  have hidx : k % l.length + (l.length - k % l.length + n₀) = l.length + n₀ := by omega
  rw [hidx, ← List.rotate_rotate l l.length n₀, List.rotate_length]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.LakeRead.exists_rotate_rotate_eq

/-- **The corrected lake reading is a weakening of the (false) target.** -/
theorem lakeReadCore_of_lakeRead (h : PocketFourPieceLakeReadStatement.{u, w, v}) :
    PocketFourPieceLakeReadCoreStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond h₁ h₂ hw hoff
    hinner houter C hC hCf hCa hCb
  obtain ⟨L, hL, hCL, hP, hread⟩ :=
    h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond h₁ h₂ hw hoff hinner houter C hC hCf
      hCa hCb
  refine ⟨L, hL, hCL, hP, fun outerWalk E hmem => ?_⟩
  obtain ⟨n, R₁, R₂, A₁, A₂, hdec, hcase, _⟩ := hread outerWalk E hmem
  exact ⟨n, R₁, R₂, A₁, A₂, hdec, hcase⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.lakeReadCore_of_lakeRead

/-- **The reading of one outer walk gives the reading of every outer walk.**  Two outer walks with
the same darts are rotations of each other (part (a), `LakeReadRotation.lean`). -/
theorem lakeReadCore_of_some (h : PocketFourPieceLakeReadSomeStatement.{u, w, v}) :
    PocketFourPieceLakeReadCoreStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond h₁ h₂ hw hoff
    hinner houter C hC hCf hCa hCb
  obtain ⟨L, hL, hCL, hP, ow₀, E₀, hmem₀, n₀, R₁, R₂, A₁, A₂, hdec, hcase⟩ :=
    h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond h₁ h₂ hw hoff hinner houter C hC hCf
      hCa hCb
  refine ⟨L, hL, hCL, hP, fun outerWalk E hmem => ?_⟩
  have hsame : ∀ d, d ∈ ow₀ ↔ d ∈ outerWalk := fun d => (hmem₀ d).trans (hmem d).symm
  obtain ⟨k, hk⟩ := EnclosedFaceSetSucc.eq_rotate_of_mem_iff E₀ E hsame
  obtain ⟨n, hn⟩ := LakeRead.exists_rotate_rotate_eq ow₀ k n₀ E₀.ne_nil
  refine ⟨n, R₁, R₂, A₁, A₂, ?_, hcase⟩
  rw [hk, hn]
  exact hdec

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.lakeReadCore_of_some

/-- **The corrected lake reading gives the residual**, by the lake fill of lane gl-p07-06. -/
theorem lakeReadSome_of_core (h : PocketFourPieceLakeReadCoreStatement.{u, w, v}) :
    PocketFourPieceLakeReadSomeStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond h₁ h₂ hw hoff
    hinner houter C hC hCf hCa hCb
  obtain ⟨L, hL, hCL, hP, hread⟩ :=
    h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond h₁ h₂ hw hoff hinner houter C hC hCf
      hCa hCb
  have hLout : X.outerFace ∉ sideFaces X.toCombMap L := fun ho => hoff (hP _ ho).1
  obtain ⟨outerWalk, E, _, hmem⟩ := exists_lakeFill_of_noncrossing X hL hLout hCL
  exact ⟨L, hL, hCL, hP, outerWalk, E, hmem, hread outerWalk E hmem⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.lakeReadSome_of_core

/-- **The residual gives lane 11's four-piece input**: take the lake fill of `L` as the face set. -/
theorem fourPieceInput_of_lakeReadSome (h : PocketFourPieceLakeReadSomeStatement.{u, w, v}) :
    SideBoundFourPieceInputStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond h₁ h₂ hw hoff
    hinner houter C hC hCf hCa hCb
  obtain ⟨L, hL, hCL, hP, outerWalk, E, _, n, R₁, R₂, A₁, A₂, hdec, hcase⟩ :=
    h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond h₁ h₂ hw hoff hinner houter C hC hCf
      hCa hCb
  have hLout : X.outerFace ∉ sideFaces X.toCombMap L := fun ho => hoff (hP _ ho).1
  obtain ⟨_, _, hCF, _⟩ := exists_lakeFill_of_noncrossing X hL hLout hCL
  exact ⟨absorbed X.toCombMap (sideFaces X.toCombMap L) X.outerFace, outerWalk, n, R₁, R₂, A₁,
    A₂, E, hCF, hdec, hcase⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.fourPieceInput_of_lakeReadSome

/-- **The ε-bounded four-piece decomposition from the residual**, by lane 11's
`boundedFourPiece_of_fourPieceInput`. -/
theorem boundedFourPiece_of_lakeReadSome (h : PocketFourPieceLakeReadSomeStatement.{u, w, v}) :
    PocketBoundedFourPieceStatement.{u, w, v} :=
  boundedFourPiece_of_fourPieceInput (fourPieceInput_of_lakeReadSome h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.boundedFourPiece_of_lakeReadSome

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
