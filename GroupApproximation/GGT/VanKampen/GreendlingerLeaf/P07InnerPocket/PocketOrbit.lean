import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.InnerTwoArc
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.KeepUnionStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketOrbitWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, inner pocket: the pocket face orbit `L_C`

Lane `gl-p07-04` of the route 3 cartography (`lanes/carto-gl-p07.md`), infrastructure for
`P07LakeExclusion.InnerPocketEnclosedTwoArcStatement` (`P07LakeExclusion/InnerTwoArcLong.lean`),
Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Certifies no printed sentence on its own.

## Truth check: the printed lane statement is FALSE

The lane asks, under the hypothesis block `Hyp` of `InnerPocketEnclosedTwoArcStatement` alone, for
one list `L` that is a closed vertex chain, whose darts are exactly the `Q₀`-darts based in
`cls C` (`Q₀ = walkKeep K.walk ∨ walkKeep ∂a ∨ walkKeep ∂b`), and whose successors are the first
`Q₀`-returns.  The successor clause makes `L` a single orbit of the face permutation of the map on
the `Q₀` edges, so `L` lies in one component of that map.  `Hyp` does not force that map to be
connected.  Model: both contact arcs of `a` are empty and `K.secondSide = a.sideFrom i = []`, so
`∂a` is only the far side of `a`, a short loop around `a.1` inside the pocket joined to `K` only
by edges outside `Q₀`.  (`ContiguityGeometry` does not tie an empty arc to the side endpoints.)
If `C` is a pocket face bordering both that loop and `K`, then the membership clause puts darts of
both components into `L`, which is impossible.  Lane `gl-p07-02`'s touch claim fails in the same
model.

## Corrected statement (proved here)

`PocketOrbitStatement` adds to `Hyp` the lane 02 inputs of lane 01
(`KeepUnionConnectedStatement`): `∂a` and `∂b` are vertex chains, and each starts a dart at a
vertex where `K.walk` starts a dart.  Under these, the conclusion holds with lane 05's
`PocketNoncrossing.PocketOrbit` plus the successor clause (`pocketOrbit`, unconditional).
`PocketOrbitConnectedStatement` instead assumes connectivity of the `Q₀` map directly
(`pocketOrbitConnected`).  Both are consequences of `PocketOrbit.exists_pocketOrbit_of_connected`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **The pocket face orbit, assuming the `Q₀` map is connected.** -/
def PocketOrbitConnectedStatement : Prop :=
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
        (PocketOrbit.keepMap X.toCombMap
            (PocketNoncrossing.pocketKeep X.toCombMap K.walk a.2.boundary.cycle b.2.boundary.cycle)
            (PocketNoncrossing.pocketKeep_alpha X.toCombMap K.walk a.2.boundary.cycle
              b.2.boundary.cycle)).IsConnected →
        ∃ L : List X.toCombMap.Dart,
          PocketNoncrossing.PocketOrbit X.toCombMap
              (PocketNoncrossing.pocketKeep X.toCombMap K.walk a.2.boundary.cycle
                b.2.boundary.cycle) C.face L ∧
            ∀ (k : ℕ) (hk : k < L.length) (m : ℕ), 0 < m →
              PocketNoncrossing.pocketKeep X.toCombMap K.walk a.2.boundary.cycle b.2.boundary.cycle
                ((X.toCombMap.sigma ^ m) (X.toCombMap.alpha L[k])) →
              (∀ n, 0 < n → n < m → ¬ PocketNoncrossing.pocketKeep X.toCombMap K.walk
                a.2.boundary.cycle b.2.boundary.cycle
                ((X.toCombMap.sigma ^ n) (X.toCombMap.alpha L[k]))) →
              (X.toCombMap.sigma ^ m) (X.toCombMap.alpha L[k]) =
                L[(k + 1) % L.length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le k) hk))

/-- **The pocket face orbit `L_C`** (lane `gl-p07-04`, corrected): `Hyp` plus the lane 02 inputs
(vertex chains `∂a`, `∂b` touching `K.walk`). -/
def PocketOrbitStatement : Prop :=
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
        a.2.boundary.cycle.IsChain
          (fun d e => X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e) →
        b.2.boundary.cycle.IsChain
          (fun d e => X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e) →
        (∃ d ∈ a.2.boundary.cycle, ∃ e ∈ K.walk,
          X.toCombMap.vertexOf d = X.toCombMap.vertexOf e) →
        (∃ d ∈ b.2.boundary.cycle, ∃ e ∈ K.walk,
          X.toCombMap.vertexOf d = X.toCombMap.vertexOf e) →
        ∃ L : List X.toCombMap.Dart,
          PocketNoncrossing.PocketOrbit X.toCombMap
              (PocketNoncrossing.pocketKeep X.toCombMap K.walk a.2.boundary.cycle
                b.2.boundary.cycle) C.face L ∧
            ∀ (k : ℕ) (hk : k < L.length) (m : ℕ), 0 < m →
              PocketNoncrossing.pocketKeep X.toCombMap K.walk a.2.boundary.cycle b.2.boundary.cycle
                ((X.toCombMap.sigma ^ m) (X.toCombMap.alpha L[k])) →
              (∀ n, 0 < n → n < m → ¬ PocketNoncrossing.pocketKeep X.toCombMap K.walk
                a.2.boundary.cycle b.2.boundary.cycle
                ((X.toCombMap.sigma ^ n) (X.toCombMap.alpha L[k]))) →
              (X.toCombMap.sigma ^ m) (X.toCombMap.alpha L[k]) =
                L[(k + 1) % L.length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le k) hk))

/-- **Lane `gl-p07-04`, connected form, closed.** -/
theorem pocketOrbitConnected : PocketOrbitConnectedStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K _ _ _ _ _ _ _ _ _ _ hw _ _ _ C _ _ _ _ hN
  have hd₀ : PocketNoncrossing.pocketKeep X.toCombMap K.walk a.2.boundary.cycle b.2.boundary.cycle
      (K.walk.head hw.ne_nil) := Or.inl (Or.inl (List.head_mem hw.ne_nil))
  exact PocketOrbit.exists_pocketOrbit_of_connected (M := X.toCombMap)
    (keep := PocketNoncrossing.pocketKeep X.toCombMap K.walk a.2.boundary.cycle b.2.boundary.cycle)
    (PocketNoncrossing.pocketKeep_alpha X.toCombMap K.walk a.2.boundary.cycle b.2.boundary.cycle)
    X.planar hN hd₀ C.face

/-- **Lane `gl-p07-04`, corrected, closed.**  Connectivity from lane 01. -/
theorem pocketOrbit : PocketOrbitStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ hw h₁₁ h₁₂ h₁₃ C hC h₁₄ h₁₅
    h₁₆ hcha hchb hta htb
  have hN : (PocketOrbit.keepMap X.toCombMap
      (PocketNoncrossing.pocketKeep X.toCombMap K.walk a.2.boundary.cycle b.2.boundary.cycle)
      (PocketNoncrossing.pocketKeep_alpha X.toCombMap K.walk a.2.boundary.cycle
        b.2.boundary.cycle)).IsConnected :=
    keepUnionConnectedStatement X.toCombMap K.walk a.2.boundary.cycle b.2.boundary.cycle
      hw.chain hcha hchb hta htb
  exact pocketOrbitConnected D eps X a b K h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ hw h₁₁ h₁₂ h₁₃ C hC
    h₁₄ h₁₅ h₁₆ hN

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketOrbitConnectedStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketOrbitStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pocketOrbitConnected
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pocketOrbit
