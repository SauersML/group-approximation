import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim.JunctionCore
import GroupApproximation.Meta.AxiomGuard

/-!
# The lobe step as the filtered cycle in its own order

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  Lane gl-p10-50.

`P10RoseExtremalTrim.roseJunctionCore_LobeRemovalStatement` (gl-p10-48) asks for a lobe `rs` and
a listing `s₁ ++ t₁⁻¹ ++ s₂ ++ t₂` of the kept darts in any order (a `List.Perm`), with free
source and kept cells, and with the length, window and properness bounds as separate clauses.
The residual here, `roseLobe_FilterListingStatement`, fixes the listing: it is the kept part of the
cycle `K.firstSide ++ K.sourceArc⁻¹ ++ K.secondSide ++ K.targetArc` **in its own order**.  It asks
that the kept part of the source arc be (the inverse of) one arc `t₁` of the same source cell,
that the kept part of the target arc be one arc `t₂` of `∂X` inside the old window, that the kept
part of the whole cycle be a closed dart walk, and the source and kept cells of `K` stay on their
sides.  Then `s₁`, `s₂` are the kept parts of the old sides, the `List.Perm` is an equality, and
every bound (`s_i ≤ ε`, `lo ≤ t₂`, `t₂ ≤ hi`, both properness bounds) follows from the old ones,
because filtering never lengthens a list.

## LOUD: strength of the residual

`roseLobe_FilterListingStatement` is **logically STRONGER** than
`roseJunctionCore_LobeRemovalStatement`, not weaker: it fixes the order of the listing and the
source and kept cells.  It is strictly smaller in proof content: the `List.Perm`, the choice of
cells, and all eight length and window clauses are proved here
(`roseLobe_lobeRemoval_of_filterListing`).  What stays open is pure planarity: pick the lobe so
that the kept darts of the source arc and of the target arc are contiguous, and the kept cycle
closes up.

## Truth check (Python, `scratchpad/gl-p10-50/drive.py`, not formalised)

The check is at least as strict as the Lean statement.  It needs every dart of the source and
kept cells uncoloured, `t₁` an infix of the old `t₁`, and `t₂` a PREFIX of the old `t₂`: the
Lean worst case where `targetArc.start = |∂X|`, in which the window clause forces a prefix.
* gl-p10-48 models (base, one, two, three subdivisions), every decomposition
  `c = s₁ t₁⁻¹ s₂ t₂` of every rotation with sides `≤ ε` and proper arcs, every kept cell of the
  face set.  At `ε = 1`, `m = 0, 1, 2`: `15/15` each.  At `ε = 2`, `m = 1, 2, 3`: `90/90` each.
  The old statement holds on the same instances.
* Random planar maps (4 to 8 edges), every face set of up to 4 inner faces with a boundary circuit
  that passes `search.premises` (closed walk, some non-first turn, all non-first turns crossed),
  every source cell, rotation, decomposition with `ε ≤ 2`, and kept cell.  Seeds 0 to 4:
  `58120 + 15164 + 61862 + 47670 + 46740 = 229556` configurations, `0` failures of either
  statement.  Least area and `¬Unpinched` are not filtered, so the sample is a superset.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10RoseExtremalTrim

/-- Filtering a four-piece cycle filters each piece. -/
theorem roseLobe_filter_four {α : Type*} {p : α → Bool} {c a b s t b' t' : List α}
    (hc : c = a ++ b ++ s ++ t) (hb : b.filter p = b') (ht : t.filter p = t') :
    c.filter p = a.filter p ++ b' ++ s.filter p ++ t' := by
  rw [hc, List.filter_append, List.filter_append, List.filter_append, hb, ht]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobe_filter_four

/-- A filtered list is no longer than the list. -/
theorem roseLobe_length_le_of_filter_eq {α : Type*} {p : α → Bool} {l l' : List α}
    (h : l.filter p = l') : l'.length ≤ l.length := by
  rw [← h]
  exact List.length_filter_le p l

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobe_length_le_of_filter_eq

/-- The reversed darts of a list have its length. -/
theorem roseLobe_length_invDarts {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} (X : DiscDiagram.{u, w, v} W)
    (l : List X.toCombMap.Dart) : (invDarts X l).length = l.length := by
  simp only [invDarts, List.length_map, List.length_reverse]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobe_length_invDarts

/-- **The lobe step in the order of the cycle** (OPEN, PLAUSIBLE; truth-checked, see the module
docstring; LOUD: logically STRONGER than `roseJunctionCore_LobeRemovalStatement`, with smaller
proof content).  Under the rose hypotheses there are roots `rs` as in the lobe statement such
that, with `z = lobeColour rs`, the source cell of `K` stays outside and the kept cell of `K`
stays inside the flipped face set, the kept darts of `K.sourceArc⁻¹` are `t₁⁻¹` for one arc `t₁`
of the source cell, the kept darts of `K.targetArc` are one arc `t₂` of `∂X` inside the window
of `K.targetArc`, and the kept darts of the cycle form a closed dart walk. -/
def roseLobe_FilterListingStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ), X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
        ∃ rs : List X.toCombMap.Dart,
          ((rs ≠ [] ∧ ∀ r ∈ rs, r ∈ K.boundary.cycle) ∨
            ∃ r, rs = [r] ∧
              (∀ x, X.toCombMap.faceOf x = X.outerFace → ¬Relation.EqvGen
                (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r x) ∧
              ∃ y ∈ K.boundary.cycle, Relation.EqvGen
                (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r y ∨
                Relation.EqvGen (CombMap.FaceClassStep X.toCombMap
                  (walkKeep X.toCombMap K.boundary.cycle)) r (X.toCombMap.alpha y)) ∧
          (cell X K.source).face ∉ flipFaces X.toCombMap K.faces (roseJunctionCore_lobeColour
            X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) rs) ∧
          (cell X K.kept).face ∈ flipFaces X.toCombMap K.faces (roseJunctionCore_lobeColour
            X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) rs) ∧
          (∃ t₁ : CyclicArc (cellDarts X K.source),
            (invDarts X K.sourceArc.darts).filter (movePred X.toCombMap
              (roseJunctionCore_lobeColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)
                rs)) = invDarts X t₁.darts) ∧
          (∃ t₂ : CyclicArc (outerDarts X),
            K.targetArc.darts.filter (movePred X.toCombMap
              (roseJunctionCore_lobeColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)
                rs)) = t₂.darts ∧
            K.targetArc.start.1 ≤ t₂.start.1 ∧
            t₂.start.1 + t₂.length ≤ K.targetArc.start.1 + K.targetArc.length) ∧
          IsClosedDartWalk X.toCombMap (K.boundary.cycle.filter (movePred X.toCombMap
            (roseJunctionCore_lobeColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) rs)))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobe_FilterListingStatement

/-- **The lobe removal from the listing in the order of the cycle.**  The sides are the kept darts
of the old sides; the listing is the kept part of the cycle, so the `List.Perm` is an equality;
each bound follows from the old one since filtering never lengthens a list. -/
theorem roseLobe_lobeRemoval_of_filterListing (h : roseLobe_FilterListingStatement.{u, w, v}) :
    roseJunctionCore_LobeRemovalStatement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨rs, hcase, hsource, hkept, ⟨t₁, ht₁⟩, ⟨t₂, ht₂, hst, hend⟩, hwalk⟩ :=
    h D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  have hfilt := roseLobe_filter_four K.decomposition ht₁ ht₂
  have h₁ := roseLobe_length_le_of_filter_eq ht₁
  have h₂ := roseLobe_length_le_of_filter_eq ht₂
  simp only [roseLobe_length_invDarts, CyclicArc.darts_length] at h₁ h₂
  rw [hfilt] at hwalk
  exact ⟨rs, hcase, K.source, K.kept, hsource, hkept, t₁, t₂, _, _, List.Perm.of_eq hfilt.symm,
    hwalk, (List.length_filter_le _ _).trans K.firstSide_length_le,
    (List.length_filter_le _ _).trans K.secondSide_length_le, K.lo_le.trans hst,
    hend.trans K.le_hi, h₁.trans_lt hsrc, h₂.trans_lt htgt⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobe_lobeRemoval_of_filterListing

/-- **The Greendlinger leaf from the listing in the order of the cycle**: the route of
`roseJunctionCore_relativeGreendlinger_of_lobeRemoval` with the lobe residual replaced by
`roseLobe_FilterListingStatement`. -/
theorem roseLobe_relativeGreendlinger_of_filterListing
    (hoff : P07InnerPocket.PocketFourPieceOffStatement.{u, w, v})
    (h : roseLobe_FilterListingStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  roseJunctionCore_relativeGreendlinger_of_lobeRemoval hoff
    (roseLobe_lobeRemoval_of_filterListing h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobe_relativeGreendlinger_of_filterListing

/-- **The outer-pinch step from the listing in the order of the cycle.** -/
theorem roseLobe_outerPinchStep_of_filterListing (h : roseLobe_FilterListingStatement.{u, w, v}) :
    PocketOuterPinchStepSectionStatement.{u, w, v} :=
  Piece10.roseJunctionCore_proof_of_lobeRemoval (roseLobe_lobeRemoval_of_filterListing h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobe_outerPinchStep_of_filterListing

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe
