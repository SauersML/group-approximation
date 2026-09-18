import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.RegionColour
import GroupApproximation.Meta.AxiomGuard

/-!
# The region choice of the planar core, in class form

Lane gl-p10-62.  Notation: `M = X.toCombMap`, `c = K.boundary.cycle`,
`R = EqvGen (FaceClassStep M (walkKeep M c))`, `Γ = walkMap M c`,
`I = invDarts X K.sourceArc.darts`, `T = K.targetArc.darts`.  The `R`-classes are the regions of
`c`: by the hypotheses of `roseLobeCore_Statement` they are the faces of the planar map `Γ`, each
inside or outside `K.faces`.

`roseLobeRegion_Statement` is the planar core of `roseLobeCore_Statement` with the Boolean move
calculus stripped off: its conclusion names regions and positions on `c` only.  Either

* (lobe) a nonempty list `rs ⊆ c` (the union of their inside regions is removed), a dart of the
  kept cell in none of them, and `c = A ++ B ++ C` whose removed darts (`d` in some root region)
  are `B` or `A ++ C` (`roseLobeRegion_Block`), placed as in `roseLobeRegion_Place`; or
* (lake) a walk dart `y` whose outer region (the class of `α y`) meets neither the outer face nor
  the source cell, and `c = A ++ B ++ C` whose removed darts (`α d` in the region of `α y`) are
  `B` or `A ++ C`.

It takes the hypotheses of `roseLobeCore_Statement` and two more, both proved
(`roseLobeRegion_faceOf_alpha_inv`, `roseLobeRegion_faceOf_alpha_tgt`): the reverse of every dart
of `I` lies on the source cell, and that of every dart of `T` on the outer face.  So in the lake
case no dart of `I` or `T` is ever removed.

## Route of the reduction `roseLobeRegion_core_of`

With `z = lobeColour rs`: for roots on `c`, `movePred z d` holds on `c` iff `d` is in no root
class (`roseLobeRegion_movePred_in`); for the root `α y`, iff `α d` is not in the class of `α y`
(`roseLobeRegion_movePred_out`), since the class of `α y` holds no dart of `c` (side constancy).
The block and placement clauses then read off (`roseLobeRegion_block`, `roseLobeRegion_place`).
Source: inside roots lie in `K.faces`; a lake meeting no source dart leaves the source out
(`not_mem_flipFaces`).  Kept: the kept dart outside every root class keeps the kept cell
(`mem_flipFaces_iff`); a lake root is outside `K.faces` (`α y` crosses `c`).  Root:
`rs ⊆ c`, or `rs = [α y]` with `α y ~ α y`.  Placement of a lake is the first disjunct.

## LOUD: strength of the residual

`roseLobeRegion_Statement` is **NOT strictly weaker** than `roseLobeCore_Statement`: pointwise
(for each fixed pocket) its conclusion is **EQUIVALENT** to Core's under Core's hypotheses (the
converse is not formalised; sketch: an inside root off `c` is replaced by a walk dart of its class
(cover); a single root outside `K.faces` meets no walk dart (side), so it is `R`-joined to some
`α y`, and the source clause says no source dart is in its class).  As closed propositions the two
are equivalent only if both are true.  It is **strictly smaller in proof content**: the move
calculus (`movePred`, `flipFaces`, `lobeColour`, the root/source/kept Boolean clauses and the
lake placement) is discharged here, and the facing of `I` and `T` is supplied.  What remains is
the pure region choice: a set of faces of `Γ` whose walk darts form one cyclic block, placed
relative to `I` and `T`.

## Remaining gap

Choose the region(s).  Not proved here.  In the truth check an inside lobe suffices on every
model configuration, but a lake is needed on about a third of the random ones.

## Truth check (Python, not formalised)

`scratchpad/gl-p10-62/region.py`, extending `scratchpad/gl-p10-60/core.py` (the gl-p10-50 / 54 /
58 generator).  Per configuration it reruns the five planar checks of `core.py`, checks the two
added hypotheses, searches the class-form conclusion clause by clause, and compares with the
gl-p10-58 check of the NoBub conclusion (`AGREE`).  Models: `315` configurations, all with a
lobe witness, `0` failures.  Random seeds `0`-`7` (`300` each): `494752` configurations
(`327801` lobe, `166951` lake), `0` without a witness, `0` disagreements with gl-p10-58, `0`
failures of the planar or the added hypotheses.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10RoseExtremalTrim

/-- **The region choice of the planar core** (OPEN, PLAUSIBLE; truth-checked, see the module
docstring; LOUD: NOT strictly weaker than `roseLobeCore_Statement`, pointwise EQUIVALENT to its
conclusion under its hypotheses, strictly smaller in proof content).  The hypotheses of
`roseLobeCore_Statement`, plus the facing of `I` and `T` (both proved); the conclusion is a lobe
(inside roots on `c`, missing a dart of the kept cell) or a lake (the outer region of a walk dart,
meeting neither the exterior nor the source cell), whose removed darts form one block of `c`. -/
def roseLobeRegion_Statement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ), X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
      (walkMap X.toCombMap K.boundary.cycle).IsPlanar →
      (∀ x y : (walkMap X.toCombMap K.boundary.cycle).Dart,
        Relation.EqvGen (CombMap.FaceClassStep X.toCombMap
          (walkKeep X.toCombMap K.boundary.cycle)) x.1 y.1 ↔
          (walkMap X.toCombMap K.boundary.cycle).faceOf x =
            (walkMap X.toCombMap K.boundary.cycle).faceOf y) →
      (∀ x : X.toCombMap.Dart, ∃ y, walkKeep X.toCombMap K.boundary.cycle y ∧ Relation.EqvGen
        (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) x y) →
      (∀ x y : X.toCombMap.Dart, Relation.EqvGen (CombMap.FaceClassStep X.toCombMap
          (walkKeep X.toCombMap K.boundary.cycle)) x y →
        (X.toCombMap.faceOf x ∈ K.faces ↔ X.toCombMap.faceOf y ∈ K.faces)) →
      (∀ d ∈ invDarts X K.sourceArc.darts,
        X.toCombMap.faceOf (X.toCombMap.alpha d) = (cell X K.source).face) →
      (∀ d ∈ K.targetArc.darts, X.toCombMap.faceOf (X.toCombMap.alpha d) = X.outerFace) →
        (∃ rs : List X.toCombMap.Dart, rs ≠ [] ∧ (∀ r ∈ rs, r ∈ K.boundary.cycle) ∧
          (∃ x, X.toCombMap.faceOf x = (cell X K.kept).face ∧ ∀ r ∈ rs, ¬Relation.EqvGen
            (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r x) ∧
          ∃ A B C : List X.toCombMap.Dart,
            roseLobeRegion_Block K.boundary.cycle (fun d => ∀ r ∈ rs, ¬Relation.EqvGen
              (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r d)
              A B C ∧
            roseLobeRegion_Place (fun d => ∀ r ∈ rs, ¬Relation.EqvGen
              (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r d)
              (invDarts X K.sourceArc.darts) K.targetArc.darts A B C) ∨
        (∃ y ∈ K.boundary.cycle,
          (∀ x, X.toCombMap.faceOf x = X.outerFace → ¬Relation.EqvGen (CombMap.FaceClassStep
            X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) (X.toCombMap.alpha y) x) ∧
          (∀ x, X.toCombMap.faceOf x = (cell X K.source).face → ¬Relation.EqvGen
            (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle))
              (X.toCombMap.alpha y) x) ∧
          ∃ A B C : List X.toCombMap.Dart,
            roseLobeRegion_Block K.boundary.cycle (fun d => ¬Relation.EqvGen
              (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle))
                (X.toCombMap.alpha y) (X.toCombMap.alpha d)) A B C)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeRegion_Statement

/-- **The planar core from the region choice**: the move calculus is read off the regions
(`roseLobeRegion_movePred_in`, `_out`, `_block`, `_place`), and the facing of `I` and `T` is
`roseLobeRegion_faceOf_alpha_inv`, `_tgt`. -/
theorem roseLobeRegion_core_of (h : roseLobeRegion_Statement.{u, w, v}) :
    roseLobeCore_Statement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose hpl hiff hcov hside
  have hc := K.boundary.cycle_mem_iff
  rcases h D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose hpl hiff hcov hside
      (fun d hd => roseLobeRegion_faceOf_alpha_inv K hd)
      (fun d hd => roseLobeRegion_faceOf_alpha_tgt K hd) with
    ⟨rs, hne, hrs, ⟨x, hxk, hx⟩, A, B, C, hb, hp⟩ | ⟨y, hy, hout, hsrcf, A, B, C, hb⟩
  · have hPQ : ∀ d ∈ K.boundary.cycle,
        movePred X.toCombMap (roseJunctionCore_lobeColour X.toCombMap
          (walkKeep X.toCombMap K.boundary.cycle) rs) d = true ↔
        ∀ r ∈ rs, ¬Relation.EqvGen (CombMap.FaceClassStep X.toCombMap
          (walkKeep X.toCombMap K.boundary.cycle)) r d :=
      fun d hd => roseLobeRegion_movePred_in hc hrs hd
    have hkx : X.toCombMap.faceOf x ∈ K.faces := by
      rw [hxk]
      exact K.kept_mem
    obtain ⟨hABC, hblk⟩ := roseLobeRegion_block hPQ hb
    refine ⟨rs, Or.inl ⟨hne, hrs⟩, Or.inl fun r hr => ((hc r).mp (hrs r hr)).1, Or.inr ?_,
      A, B, C, hABC, hblk, Or.inr (roseLobeRegion_place hPQ hABC hp)⟩
    rw [← hxk]
    exact (P10Rose.FilterMove.mem_flipFaces_iff (roseJunctionCore_lobeColour_step X.toCombMap
      (walkKeep X.toCombMap K.boundary.cycle) rs) x).mpr
      ⟨fun _ => roseJunctionCore_lobeColour_eq_false _ _ hx, fun _ => hkx⟩
  · have hPQ : ∀ d ∈ K.boundary.cycle,
        movePred X.toCombMap (roseJunctionCore_lobeColour X.toCombMap
          (walkKeep X.toCombMap K.boundary.cycle) [X.toCombMap.alpha y]) d = true ↔
        ¬Relation.EqvGen (CombMap.FaceClassStep X.toCombMap
          (walkKeep X.toCombMap K.boundary.cycle)) (X.toCombMap.alpha y)
            (X.toCombMap.alpha d) :=
      fun d hd => roseLobeRegion_movePred_out hc hy hd
    have hyo : X.toCombMap.faceOf (X.toCombMap.alpha y) ∉ K.faces := ((hc y).mp hy).2
    obtain ⟨hABC, hblk⟩ := roseLobeRegion_block hPQ hb
    refine ⟨[X.toCombMap.alpha y],
      Or.inr ⟨X.toCombMap.alpha y, rfl, hout, y, hy, Or.inr (Relation.EqvGen.refl _)⟩,
      Or.inr ?_, Or.inl ⟨X.toCombMap.alpha y, rfl, hyo⟩, A, B, C, hABC, hblk,
      Or.inl ⟨X.toCombMap.alpha y, rfl, hyo⟩⟩
    refine P10Rose.FilterMove.not_mem_flipFaces (roseJunctionCore_lobeColour_step X.toCombMap
      (walkKeep X.toCombMap K.boundary.cycle) [X.toCombMap.alpha y]) K.source_not_mem ?_
    intro x hx
    apply roseJunctionCore_lobeColour_eq_false
    intro r hr
    rw [List.mem_singleton] at hr
    rw [hr]
    exact hsrcf x hx

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeRegion_core_of

/-- **The no-bubble statement from the region choice.** -/
theorem roseLobeRegion_noBub_of (h : roseLobeRegion_Statement.{u, w, v}) :
    roseLobeNoBub_Statement.{u, w, v} :=
  roseLobeCore_noBub_of (roseLobeRegion_core_of h)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeRegion_noBub_of

/-- **The lobe removal from the region choice.** -/
theorem roseLobeRegion_lobeRm_of (h : roseLobeRegion_Statement.{u, w, v}) :
    roseJunctionCore_LobeRemovalStatement.{u, w, v} :=
  roseLobeCore_lobeRm_of (roseLobeRegion_core_of h)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeRegion_lobeRm_of

/-- **The Greendlinger leaf from the region choice.** -/
theorem roseLobeRegion_green_of
    (hoff : P07InnerPocket.PocketFourPieceOffStatement.{u, w, v})
    (h : roseLobeRegion_Statement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  roseLobeCore_green_of hoff (roseLobeRegion_core_of h)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeRegion_green_of

/-- **The outer-pinch step from the region choice.** -/
theorem roseLobeRegion_pinch_of (h : roseLobeRegion_Statement.{u, w, v}) :
    PocketOuterPinchStepSectionStatement.{u, w, v} :=
  roseLobeCore_pinch_of (roseLobeRegion_core_of h)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeRegion_pinch_of

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe
