import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.InnerTwoArcLong
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketNoncrossingWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, inner pocket: the pocket orbit is a noncrossing closed walk

Lane `gl-p07-05`, endpoint module.  Infrastructure for
`P07LakeExclusion.InnerPocketEnclosedTwoArcStatement` (`P07LakeExclusion/InnerTwoArcLong.lean`),
Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Certifies no printed sentence on its own.

## Statement

Take the hypotheses `Hyp` of `InnerPocketEnclosedTwoArcStatement`, the retained edges
`Q₀ = pocketKeep K ∂a ∂b` (edges of the walk and of both region cycles), and the class
`cls C = faceClass Q₀ C.face`.  For any face orbit `L` of the class, as lane `gl-p07-04` delivers
it (`PocketOrbit`, its successor clause is not needed), `PocketOrbitNoncrossingStatement` asserts:
* `L` is a noncrossing closed walk;
* `sideFaces L = cls C`;
* the outer face is not on the side of `L`.

## Proof

* No bridge (`pocketKeep_bridge_free`) gives `alpha_not_mem`.  It is proved here directly from
  `hw.isBoundaryDart_sideFaces_iff` and the boundary cycles of `a` and `b`, so lane 03 is not needed.
* `isNoncrossingClosedWalk_of_orbit` and `sideFaces_eq_faceClass` give the first two clauses.
* The class lies in `sideFaces K`, since `K` is retained (`faceClass_subset_sideFaces`), and the
  outer face does not.

The endpoint `pocketOrbitNoncrossing` is unconditional.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse PocketNoncrossing

/-- **The general composite.**  A face orbit of the class of `c` for the edges of a noncrossing
closed walk `K` and two boundary cycles `c₁`, `c₂` (of face sets `F₁`, `F₂`) is a noncrossing
closed walk with side the class, and it avoids any face `o` off the side of `K`. -/
theorem PocketNoncrossing.noncrossing_of_pocketOrbit {M : CombMap.{u}} (hM : M.IsPlanar)
    {K c₁ c₂ : List M.Dart} (hw : IsNoncrossingClosedWalk M K) {F₁ F₂ : Finset M.Face}
    (hcyc₁ : ∀ d, d ∈ c₁ ↔ M.faceOf d ∈ F₁ ∧ M.faceOf (M.alpha d) ∉ F₁)
    (hcyc₂ : ∀ d, d ∈ c₂ ↔ M.faceOf d ∈ F₂ ∧ M.faceOf (M.alpha d) ∉ F₂)
    {o c : M.Face} (hoff : o ∉ sideFaces M K) (hcK : c ∈ sideFaces M K) (hc₁ : c ∉ F₁)
    (hc₂ : c ∉ F₂) {L : List M.Dart} (hL : PocketOrbit M (pocketKeep M K c₁ c₂) c L) :
    IsNoncrossingClosedWalk M L ∧ sideFaces M L = faceClass M (pocketKeep M K c₁ c₂) c ∧
      o ∉ sideFaces M L := by
  have hα : ∀ d, pocketKeep M K c₁ c₂ (M.alpha d) ↔ pocketKeep M K c₁ c₂ d :=
    pocketKeep_alpha M K c₁ c₂
  have hside : sideFaces M L = faceClass M (pocketKeep M K c₁ c₂) c :=
    sideFaces_eq_faceClass hα hL.ne_nil hL.mem_iff
  refine ⟨isNoncrossingClosedWalk_of_orbit hα hL
    (pocketKeep_bridge_free hM hw hcyc₁ hcyc₂ hcK hc₁ hc₂), hside, ?_⟩
  rw [hside]
  exact fun ho => hoff (faceClass_subset_sideFaces M (pocketKeep M K c₁ c₂)
    (fun x hx => Or.inl hx) hcK ho)

/-- **The pocket orbit is a noncrossing closed walk** (lane `gl-p07-05`).  Hypotheses: those of
`P07LakeExclusion.InnerPocketEnclosedTwoArcStatement`, and a face orbit `L` of the pocket class of
`C` (`PocketOrbit`, implied by lane `gl-p07-04`'s orbit).  Conclusion: `L` is a noncrossing closed
walk, its side is the class, and the outer face is off its side. -/
def PocketOrbitNoncrossingStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W)
    {i j : Fin X.rCellCount} (a b : RegionCandidate D eps X) (K : CellPocketWalk D eps X i j),
    i ≠ j → a.JoinsCells i j → b.JoinsCells i j → Disjoint a.1 b.1 →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    (∀ word ∈ W, 1 < word.length) →
    K.firstSide = b.sideFrom j → K.secondSide = a.sideFrom i →
    (∃ G₁ : CyclicArc (cellDarts X i),
      K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i) →
    (∃ G₂ : CyclicArc (cellDarts X j),
      K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j) →
    ∀ hw : IsNoncrossingClosedWalk X.toCombMap K.walk,
      X.outerFace ∉ sideFaces X.toCombMap K.walk →
      (reclosedMap X.toCombMap (sideFaces X.toCombMap K.walk)
          (hw.innerCycle X.planar)).eulerCharacteristic = X.toCombMap.eulerCharacteristic →
      (reclosedMap X.toCombMap (sideOutside X.toCombMap K.walk)
          (hw.outerCycle X.planar)).eulerCharacteristic = X.toCombMap.eulerCharacteristic →
      ∀ C ∈ X.relatorCells, C.face ∈ sideFaces X.toCombMap K.walk → C.face ∉ a.1 → C.face ∉ b.1 →
        ∀ L : List X.toCombMap.Dart,
          PocketOrbit X.toCombMap
              (pocketKeep X.toCombMap K.walk a.2.boundary.cycle b.2.boundary.cycle) C.face L →
            IsNoncrossingClosedWalk X.toCombMap L ∧
              sideFaces X.toCombMap L = faceClass X.toCombMap
                (pocketKeep X.toCombMap K.walk a.2.boundary.cycle b.2.boundary.cycle) C.face ∧
              X.outerFace ∉ sideFaces X.toCombMap L

/-- **Endpoint of lane `gl-p07-05`.** -/
theorem pocketOrbitNoncrossing : PocketOrbitNoncrossingStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond h₁ h₂ hw hoff
    hinner houter C hC hCf hCa hCb L hL
  exact PocketNoncrossing.noncrossing_of_pocketOrbit (K := K.walk)
    (c₁ := a.2.boundary.cycle) (c₂ := b.2.boundary.cycle) (F₁ := a.1) (F₂ := b.1)
    (o := X.outerFace) (c := C.face) (L := L) X.planar hw
    (fun d => a.2.boundary.cycle_mem_iff d) (fun d => b.2.boundary.cycle_mem_iff d)
    hoff hCf hCa hCb hL

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketNoncrossing.noncrossing_of_pocketOrbit
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketOrbitNoncrossingStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pocketOrbitNoncrossing
