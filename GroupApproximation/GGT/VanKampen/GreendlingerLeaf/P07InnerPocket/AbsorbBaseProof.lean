import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.AbsorbBaseStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.AbsorbFaceSetProof
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-46: the reduction to `AbsorbFaceSetStatement`

* `FourPieceWitness.absorbFaceSet_of_absorbBase`: split Base on `AbsorbBaseCase`.  In the case,
  `absorbBase_basic_of_case` gives a basic pair.  Outside it, Base is the new hypothesis.  Improve
  passes through unchanged.
* `FourPieceWitness.absorbBase_of_absorbFaceSet`: the converse, which drops the case hypothesis.
* `FourPieceWitness.absorbBase_iff_absorbFaceSet` and
  `FourPieceWitness.absorbBase_iff_noPlanarDegenStep`.

## LOUD: EQUIVALENT to the target

See the docstring of `AbsorbBaseStatement.lean`.  The statement is smaller in proof content, not
weaker as a `Prop`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- **The target from Base outside the lake-filled case.** -/
theorem absorbFaceSet_of_absorbBase (h : AbsorbBaseStatement.{u, w, v}) :
    AbsorbFaceSetStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbj hdisj hlet hW hK1 hK2 G₁ hG₁ G₂ hG₂ hw
    hout hinE houtE C hC hCf hCa hCb hno hnc
  obtain ⟨hbase, himp⟩ := h D eps X a b K hij hai hbj hdisj hlet hW hK1 hK2 G₁ hG₁ G₂ hG₂ hw
    hout hinE houtE C hC hCf hCa hCb hno hnc
  refine ⟨?_, himp⟩
  by_cases hcase : AbsorbBaseCase a b K G₁ G₂ C.face
  · exact Or.inl (absorbBase_basic_of_case hw hout hCf hCa hCb hcase)
  · exact hbase hcase

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.absorbFaceSet_of_absorbBase

/-- **The converse**: drop the case hypothesis. -/
theorem absorbBase_of_absorbFaceSet (h : AbsorbFaceSetStatement.{u, w, v}) :
    AbsorbBaseStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbj hdisj hlet hW hK1 hK2 G₁ hG₁ G₂ hG₂ hw
    hout hinE houtE C hC hCf hCa hCb hno hnc
  obtain ⟨hbase, himp⟩ := h D eps X a b K hij hai hbj hdisj hlet hW hK1 hK2 G₁ hG₁ G₂ hG₂ hw
    hout hinE houtE C hC hCf hCa hCb hno hnc
  exact ⟨fun _ => hbase, himp⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.absorbBase_of_absorbFaceSet

/-- **Base outside the lake-filled case and the absorption iteration are equivalent.** -/
theorem absorbBase_iff_absorbFaceSet :
    AbsorbBaseStatement.{u, w, v} ↔ AbsorbFaceSetStatement.{u, w, v} :=
  ⟨absorbFaceSet_of_absorbBase, absorbBase_of_absorbFaceSet⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.absorbBase_iff_absorbFaceSet

/-- **Base outside the lake-filled case and the target are equivalent.** -/
theorem absorbBase_iff_noPlanarDegenStep :
    AbsorbBaseStatement.{u, w, v} ↔ NoPlanarDegenStepStatement.{u, w, v} :=
  absorbBase_iff_absorbFaceSet.trans absorbFaceSet_iff_noPlanarDegenStep

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.absorbBase_iff_noPlanarDegenStep

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
