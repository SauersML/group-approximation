import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.LakeReadFixStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceOff
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.Assembly
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-42b: the rerouted lake endpoint

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Certifies no printed sentence on its own.

* `lakeReadFix_of_lakeRead`: the false `PocketFourPieceLakeReadStatement` implies the corrected
  `LakeReadFixStatement` (take the lake fill and the same reading as the alternative witness).
* `lakeReadFix_core`: the corrected statement implies gl-p07-18's `…LakeReadCoreStatement`.
* `lakeReadFix_pocketFourPieceOff`: **the rerouted endpoint**, `LakeReadFixStatement →
  PocketFourPieceOffStatement`.  It replaces `pocketFourPieceOff_of_lakeRead`.  Proof: take the
  lake fill of `L` (`exists_lakeFill_of_noncrossing`) and its reading.
  - Both contact arcs on `Π_i` nonempty: lake-fill witness, off cell by
    `FourPieceOff.exists_cell_not_mem_absorbed_of_contact` (lane gl-p07-07).
  - Otherwise, both read arcs empty: the alternative witness is exactly the target's tuple.
  - Otherwise: lake-fill witness, off-cell clause vacuous.
* `lakeReadFix_innerPocketEnclosed`: composed with `innerPocketEnclosed_of_fourPieceOff`.
* `lakeReadFix_of_core_off`: the truth reduction, core reading plus `PocketFourPieceOffStatement`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse
  Surgery.MapCollapse.ExteriorComponent

/-- **The corrected lake reading is a weakening of the (false) target.**  The lake fill with the
same reading is an alternative witness, with the target's off cell. -/
theorem lakeReadFix_of_lakeRead (h : PocketFourPieceLakeReadStatement.{u, w, v}) :
    LakeReadFixStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond h₁ h₂ hw hoff
    hinner houter C hC hCf hCa hCb
  obtain ⟨L, hL, hCL, hP, hread⟩ :=
    h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond h₁ h₂ hw hoff hinner houter C hC hCf
      hCa hCb
  have hLout : X.outerFace ∉ sideFaces X.toCombMap L := fun ho => hoff (hP _ ho).1
  obtain ⟨_, _, hCF, _⟩ := exists_lakeFill_of_noncrossing X hL hLout hCL
  refine ⟨L, hL, hCL, hP, fun outerWalk E hmem => ?_⟩
  obtain ⟨n, R₁, R₂, A₁, A₂, hdec, hcase, hk₀⟩ := hread outerWalk E hmem
  exact ⟨n, R₁, R₂, A₁, A₂, hdec, hcase, fun hpos hA₁ hA₂ =>
    ⟨absorbed X.toCombMap (sideFaces X.toCombMap L) X.outerFace, outerWalk, n, R₁, R₂, A₁, A₂,
      E, hCF, hdec, hcase, fun _ _ => hk₀ hpos hA₁ hA₂⟩⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.lakeReadFix_of_lakeRead

/-- **The corrected lake reading gives gl-p07-18's core reading**: drop the degenerate clause. -/
theorem lakeReadFix_core (h : LakeReadFixStatement.{u, w, v}) :
    PocketFourPieceLakeReadCoreStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond h₁ h₂ hw hoff
    hinner houter C hC hCf hCa hCb
  obtain ⟨L, hL, hCL, hP, hread⟩ :=
    h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond h₁ h₂ hw hoff hinner houter C hC hCf
      hCa hCb
  refine ⟨L, hL, hCL, hP, fun outerWalk E hmem => ?_⟩
  obtain ⟨n, R₁, R₂, A₁, A₂, hdec, hcase, _⟩ := hread outerWalk E hmem
  exact ⟨n, R₁, R₂, A₁, A₂, hdec, hcase⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.lakeReadFix_core

/-- **Rerouted endpoint: the four-piece off statement from the corrected lake reading.**  It
replaces `pocketFourPieceOff_of_lakeRead`, whose input is false. -/
theorem lakeReadFix_pocketFourPieceOff (h : LakeReadFixStatement.{u, w, v}) :
    PocketFourPieceOffStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond h₁ h₂ hw hoff
    hinner houter C hC hCf hCa hCb
  obtain ⟨L, hL, hCL, hP, hread⟩ :=
    h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond h₁ h₂ hw hoff hinner houter C hC hCf
      hCa hCb
  have hLout : X.outerFace ∉ sideFaces X.toCombMap L := fun ho => hoff (hP _ ho).1
  obtain ⟨outerWalk, E, hCF, hmem⟩ := exists_lakeFill_of_noncrossing X hL hLout hCL
  obtain ⟨n, R₁, R₂, A₁, A₂, hdec, hcase, halt⟩ := hread outerWalk E hmem
  by_cases hpos : 0 < (a.cellArcList i).length ∧ 0 < (b.cellArcList i).length
  · exact ⟨absorbed X.toCombMap (sideFaces X.toCombMap L) X.outerFace, outerWalk, n, R₁, R₂, A₁,
      A₂, E, hCF, hdec, hcase, fun _ _ =>
        FourPieceOff.exists_cell_not_mem_absorbed_of_contact K hij hai hbi hfirst hsecond hw hoff
          hP hpos.1 hpos.2⟩
  · by_cases hA : A₁.length = 0 ∧ A₂.length = 0
    · exact halt hpos hA.1 hA.2
    · exact ⟨absorbed X.toCombMap (sideFaces X.toCombMap L) X.outerFace, outerWalk, n, R₁, R₂,
        A₁, A₂, E, hCF, hdec, hcase, fun hA₁ hA₂ => (hA ⟨hA₁, hA₂⟩).elim⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.lakeReadFix_pocketFourPieceOff

/-- **The enclosed inner pocket from the corrected lake reading.**  It replaces
`innerPocketEnclosed_of_lakeRead`. -/
theorem lakeReadFix_innerPocketEnclosed (h : LakeReadFixStatement.{u, w, v}) :
    P07LakeExclusion.InnerPocketEnclosedTwoArcStatement.{u, w, v} :=
  innerPocketEnclosed_of_fourPieceOff (lakeReadFix_pocketFourPieceOff h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.lakeReadFix_innerPocketEnclosed

/-- **Truth reduction: the corrected lake reading from the core reading and the four-piece off
statement.**  The core supplies `L` and the reading; the off statement supplies the alternative
witness. -/
theorem lakeReadFix_of_core_off (hcore : PocketFourPieceLakeReadCoreStatement.{u, w, v})
    (hfour : PocketFourPieceOffStatement.{u, w, v}) : LakeReadFixStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond h₁ h₂ hw hoff
    hinner houter C hC hCf hCa hCb
  obtain ⟨L, hL, hCL, hP, hread⟩ :=
    hcore D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond h₁ h₂ hw hoff hinner houter C hC
      hCf hCa hCb
  refine ⟨L, hL, hCL, hP, fun outerWalk E hmem => ?_⟩
  obtain ⟨n, R₁, R₂, A₁, A₂, hdec, hcase⟩ := hread outerWalk E hmem
  exact ⟨n, R₁, R₂, A₁, A₂, hdec, hcase, fun _ _ _ =>
    hfour D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond h₁ h₂ hw hoff hinner houter C hC
      hCf hCa hCb⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.lakeReadFix_of_core_off

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
