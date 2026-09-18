import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WalkDegenCaseStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitnessDart
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-39b: Base in the case N holds

`PinchCase.walkDegenCase_witness_basic`: if the witness walk satisfies the four noninterleave
clauses (N), then the witness pair `(witnessFaces a b K c, ow)` is a basic pair in the sense of
lane gl-p07-38 (`FourPieceWitness.AbsorbFaceSetBasic`).  The ingredients:
* `C.face ∈ F` (`FourPieceWitness.mem_witnessFaces_self`);
* `F ⊆ sideFaces K.walk` (`FourPieceWitness.witnessFaces_subset_sideFaces`);
* the dart clause, third disjunct (`FourPieceWitness.dart_clause`, from the bridge-free
  hypothesis).
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCase

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **The witness pair is basic when N holds.** -/
theorem walkDegenCase_witness_basic {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} {G₁ : CyclicArc (cellDarts X i)}
    {G₂ : CyclicArc (cellDarts X j)} {c : X.toCombMap.Face}
    (hw : IsNoncrossingClosedWalk X.toCombMap K.walk) (hc : c ∈ sideFaces X.toCombMap K.walk)
    (hca : c ∉ a.1) (hcb : c ∉ b.1) {ow : List X.toCombMap.Dart}
    (E : EnclosedFaceSetSucc X (FourPieceWitness.witnessFaces a b K c) ow)
    (hnb : ∀ d ∈ ow,
      X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ FourPieceWitness.witnessFaces a b K c)
    (hN : WalkDegenCaseNoninterleave b G₁ G₂ ow) :
    FourPieceWitness.AbsorbFaceSetBasic a b K G₁ G₂ c
      (FourPieceWitness.witnessFaces a b K c) ow := by
  obtain ⟨h1, h2, h3, h4⟩ := hN
  exact ⟨E, FourPieceWitness.mem_witnessFaces_self hc,
    FourPieceWitness.witnessFaces_subset_sideFaces,
    fun d hd => Or.inr (Or.inr (FourPieceWitness.dart_clause hw hca hcb E hnb d hd)),
    h1, h2, h3, h4⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCase.walkDegenCase_witness_basic

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCase
