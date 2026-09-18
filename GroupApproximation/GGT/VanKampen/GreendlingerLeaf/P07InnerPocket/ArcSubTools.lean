import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.ArcSubInv
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.ArcSubSide
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, inner pocket: the sub-arc and sub-side tools

**Lane gl-p07-12, endpoint.**  Infrastructure for
`P07LakeExclusion.InnerPocketEnclosedTwoArcStatement`
(`GreendlingerLeaf/P07LakeExclusion/InnerTwoArcLong.lean`), Osin, arXiv:math/0411039v3, §9, proof
of Lemma 9.7(b).  Certifies no printed sentence on its own; it serves `thm:hull` (tex 2121) via
the Greendlinger leaf.

`ArcSubToolsStatement` bundles the four list tools the decomposition lanes use:

1. a contiguous piece of a cyclic arc is a cyclic arc of the same carrier
   (`CyclicArc.exists_subArc`, `ArcSubArc`; data form `CyclicArc.subArc`);
2. a contiguous piece of the backwards reading of a cyclic arc is the backwards reading of a
   cyclic arc of the same carrier (`CyclicArc.exists_subArc_of_invDarts`, `ArcSubInv`);
3. `invDarts X (a ++ b) = invDarts X b ++ invDarts X a` (`arcSub_invDarts_append`, reusing
   `P07LakeExclusion.LakeFill.lakeFill_invDarts_append`);
4. a sub-list of the side of a region leaving a cell has length at most `ε`
   (`arcSub_sideFrom_sublist_length_le`, `ArcSubSide`).

The proofs are in the docstrings of `ArcSubArc`, `ArcSubInv` and `ArcSubSide`; `arcSubTools`
assembles them.  The statement has no hypothesis beyond the list splits and the sub-list relation.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded

/-- **Lane gl-p07-12, statement.**  The sub-arc and sub-side list tools. -/
def ArcSubToolsStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W),
    (∀ (cyc : List X.toCombMap.Dart) (A : Embedded.CyclicArc cyc)
        (u₁ u₂ u₃ : List X.toCombMap.Dart), A.darts = u₁ ++ u₂ ++ u₃ →
        ∃ B : Embedded.CyclicArc cyc, B.darts = u₂) ∧
      (∀ (cyc : List X.toCombMap.Dart) (A : Embedded.CyclicArc cyc)
        (p q r : List X.toCombMap.Dart), invDarts X A.darts = p ++ q ++ r →
        ∃ B : Embedded.CyclicArc cyc, invDarts X B.darts = q) ∧
      (∀ a b : List X.toCombMap.Dart, invDarts X (a ++ b) = invDarts X b ++ invDarts X a) ∧
      (∀ (a : RegionCandidate D eps X) (k : Fin X.rCellCount) (l : List X.toCombMap.Dart),
        l.Sublist (a.sideFrom k) → l.length ≤ eps)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.ArcSubToolsStatement

/-- **Lane gl-p07-12, proof.** -/
theorem arcSubTools : ArcSubToolsStatement.{u, w, v} := by
  intro _ _ _ _ _ _ X
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro _ A _ _ _ h
    exact CyclicArc.exists_subArc A h
  · intro _ A _ _ _ h
    exact CyclicArc.exists_subArc_of_invDarts A h
  · intro a b
    exact arcSub_invDarts_append X a b
  · intro a k _ h
    exact arcSub_sideFrom_sublist_length_le a k h

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.arcSubTools

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
