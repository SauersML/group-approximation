import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.ArcSubArc
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFillArc
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, inner pocket: sub-arcs read backwards

Lane gl-p07-12 (sub-arc and sub-side list tools), infrastructure for
`P07LakeExclusion.InnerPocketEnclosedTwoArcStatement`
(`GreendlingerLeaf/P07LakeExclusion/InnerTwoArcLong.lean`), Osin, arXiv:math/0411039v3, §9, proof
of Lemma 9.7(b).  Certifies no printed sentence on its own; it serves `thm:hull` (tex 2121) via
the Greendlinger leaf.

The decomposition lanes (gl-p07-09 to gl-p07-11) cut the inverse walk `invDarts X outerWalk` into
runs; an arc run is a contiguous piece of `invDarts X A.darts` for an arc `A` of a cell.  This
module turns such a piece back into an arc.

## The mathematical proof

Write `ι l := (l.reverse).map α` for `invDarts X l`.

1. *Append.*  `ι (a ++ b) = ι b ++ ι a`, because `reverse (a ++ b) = reverse b ++ reverse a` and
   `map` distributes over `++` (`P07LakeExclusion.LakeFill.lakeFill_invDarts_append`).  Iterating,
   `ι (u ++ v ++ z) = ι z ++ ι v ++ ι u`.
2. *Involution.*  `ι (ι l) = l`, because `α` is an involution
   (`EnclosedBridgeDoubling.invDarts_invDarts_side`).
3. *Sub-arc of an inverse arc.*  If `ι A.darts = p ++ q ++ r`, then
   `A.darts = ι (ι A.darts) = ι (p ++ q ++ r) = ι r ++ ι q ++ ι p`.  The sub-arc tool
   (`CyclicArc.exists_subArc`, `ArcSubArc`) gives an arc `B` of the same carrier with
   `B.darts = ι q`, hence `ι B.darts = ι (ι q) = q`.

Truth check: steps 1 and 2 are list identities valid for all lists; step 3 uses only them and the
sub-arc tool, whose hypotheses are exactly the split of `A.darts`.  Empty `p`, `q` or `r` are
allowed (an empty `q` gives an arc of length `0`).
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **Inverse of a concatenation** (reuse of `LakeFill.lakeFill_invDarts_append`). -/
theorem arcSub_invDarts_append (X : DiscDiagram.{u, w, v} W) (a b : List X.toCombMap.Dart) :
    invDarts X (a ++ b) = invDarts X b ++ invDarts X a :=
  P07LakeExclusion.LakeFill.lakeFill_invDarts_append a b

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.arcSub_invDarts_append

/-- The inverse of a three-piece concatenation reads the pieces backwards in reverse order. -/
theorem arcSub_invDarts_append_three (X : DiscDiagram.{u, w, v} W)
    (u₁ u₂ u₃ : List X.toCombMap.Dart) :
    invDarts X (u₁ ++ u₂ ++ u₃) = invDarts X u₃ ++ invDarts X u₂ ++ invDarts X u₁ := by
  rw [arcSub_invDarts_append X (u₁ ++ u₂) u₃, arcSub_invDarts_append X u₁ u₂, List.append_assoc]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.arcSub_invDarts_append_three

/-- **Reverse orientation is an involution** (reuse of
`EnclosedBridgeDoubling.invDarts_invDarts_side`). -/
theorem arcSub_invDarts_invDarts (X : DiscDiagram.{u, w, v} W) (l : List X.toCombMap.Dart) :
    invDarts X (invDarts X l) = l :=
  EnclosedBridgeDoubling.invDarts_invDarts_side l

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.arcSub_invDarts_invDarts

namespace CyclicArc

variable {X : DiscDiagram.{u, w, v} W} {cyc : List X.toCombMap.Dart}

/-- A split of an arc reads, backwards, as the backwards pieces in reverse order. -/
theorem invDarts_darts_of_split (A : Embedded.CyclicArc cyc) {u₁ u₂ u₃ : List X.toCombMap.Dart}
    (h : A.darts = u₁ ++ u₂ ++ u₃) :
    invDarts X A.darts = invDarts X u₃ ++ invDarts X u₂ ++ invDarts X u₁ := by
  rw [h]
  exact arcSub_invDarts_append_three X u₁ u₂ u₃

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.CyclicArc.invDarts_darts_of_split

/-- A split of the backwards reading of an arc is the backwards reading of a split of the arc. -/
theorem darts_eq_of_invDarts_split (A : Embedded.CyclicArc cyc)
    {p q r : List X.toCombMap.Dart} (h : invDarts X A.darts = p ++ q ++ r) :
    A.darts = invDarts X r ++ invDarts X q ++ invDarts X p :=
  calc A.darts = invDarts X (invDarts X A.darts) := (arcSub_invDarts_invDarts X A.darts).symm
    _ = invDarts X (p ++ q ++ r) := by rw [h]
    _ = invDarts X r ++ invDarts X q ++ invDarts X p := arcSub_invDarts_append_three X p q r

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.CyclicArc.darts_eq_of_invDarts_split

/-- **Sub-arc of a backwards arc.**  A contiguous piece `q` of the backwards reading of an arc `A`
is the backwards reading of an arc of the same carrier. -/
theorem exists_subArc_of_invDarts (A : Embedded.CyclicArc cyc) {p q r : List X.toCombMap.Dart}
    (h : invDarts X A.darts = p ++ q ++ r) :
    ∃ B : Embedded.CyclicArc cyc, invDarts X B.darts = q := by
  obtain ⟨B, hB⟩ := exists_subArc A (darts_eq_of_invDarts_split A h)
  refine ⟨B, ?_⟩
  rw [hB]
  exact arcSub_invDarts_invDarts X q

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.CyclicArc.exists_subArc_of_invDarts

/-- A prefix of the backwards reading of an arc is the backwards reading of an arc. -/
theorem exists_subArc_of_invDarts_prefix (A : Embedded.CyclicArc cyc)
    {q r : List X.toCombMap.Dart} (h : invDarts X A.darts = q ++ r) :
    ∃ B : Embedded.CyclicArc cyc, invDarts X B.darts = q :=
  exists_subArc_of_invDarts A (p := []) (r := r) (by rw [h, List.nil_append])

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.CyclicArc.exists_subArc_of_invDarts_prefix

/-- A suffix of the backwards reading of an arc is the backwards reading of an arc. -/
theorem exists_subArc_of_invDarts_suffix (A : Embedded.CyclicArc cyc)
    {p q : List X.toCombMap.Dart} (h : invDarts X A.darts = p ++ q) :
    ∃ B : Embedded.CyclicArc cyc, invDarts X B.darts = q :=
  exists_subArc_of_invDarts A (p := p) (r := []) (by rw [h, List.append_nil])

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.CyclicArc.exists_subArc_of_invDarts_suffix

end CyclicArc

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
