import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.MultiStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.TripleExcl
import GroupApproximation.Meta.AxiomGuard

/-!
# The region choice outside the one- to five-dart cases

Lane gl-p10-69.  Notation as in `MultiStatement`: `M = X.toCombMap`, `c = K.boundary.cycle`,
`R = EqvGen (FaceClassStep M (walkKeep M c))`, `I = invDarts X K.sourceArc.darts`,
`T = K.targetArc.darts`.

## Route

On the residual of `roseLobeMulti_Statement` (no region of the one- and two-dart kinds) the
truth check finds every surviving region witnessed by one of six fixed-size shapes, and each is
proved as a case lemma with an explicitly named witness (`TripleLake`, `TripleLobe`):

* (lake triple: consecutive, wrapping after the first dart, wrapping after the second) the
  class of `α a1` meets `α c` in `α a1`, `α a2`, `α a3` only, three cyclically consecutive darts
  of `c`, and misses the outer face and the source cell: the lake at `a1`;
* (inside triple / quadruple / quintuple) three, four or five consecutive darts `B` of `c` are
  closed under the classes they meet (one, two or more classes: one case), none of which is the
  kept class, suitably placed: the lobe `rs = B` with `B` removed.

No contiguity hypothesis (the darts are given with their positions), no general run lemma over
an arbitrary block (each shape is a separate lemma on an explicit literal).  Strict descent to
the two-dart cases is not available: the size of the trace of a region on `c` is intrinsic to
the region, and no concrete measure on the configuration decreases along a move that keeps the
hypotheses of `roseLobeMulti_Statement` (the truth check sees three- to five-dart witnesses with
no one- or two-dart witness at all), so the residual is NOT closed.

## LOUD: strength of the residual

`roseLobeTriple_Statement` is `roseLobeMulti_Statement` with six more hypotheses, the negations
of the six cases (`roseLobeTriple_NoLakeRun`, `_NoLakeWrapL`, `_NoLakeWrapR`, `_NoLobeRun`,
`_NoLobeQuad`, `_NoLobeQuint`).  So it is implied by `roseLobeMulti_Statement`, and
`roseLobeTriple_multi_of` proves the converse: as closed propositions the two (and
`roseLobeChoice_Statement`, `roseLobeRegion_Statement`) are **EQUIVALENT**; it is **NOT strictly
weaker in logical strength**, and not stronger.  It is **strictly smaller in proof content**:
every configuration with a region of the six shapes is now discharged, and on the `maxeps 2`
random configurations the residual drops from `29` (resp. `173`) to `0`.

## LOUD: model failures of the conclusion at `maxeps 10`

On seed `5`, `N = 30`, `maxeps 10` the truth-check model finds `1260` distinct configurations
satisfying every MODELLED hypothesis of `roseLobeMulti_Statement` (planarity, `hiff`, `hcov`,
`hside`, `hI`, `hT`, `ClosedWalk`, `¬FirstTurns`, `¬Unpinched`, `AllNonFirstTurnsCrossed`, the
arc-length bounds and all exclusions) and having NO lobe and NO lake: the conclusion of
`roseLobeMulti_Statement` (hence of this statement, of `roseLobeChoice_Statement` and of
`roseLobeRegion_Statement`) FAILS in the combinatorial model there.  They have
`sourceArc = targetArc = []` up to one dart, the two sides (length `≤ 7 ≤ eps`) covering the
whole walk, and interleaving inside and outside classes (a rose); all carry a letter labelling.
NOT modelled: `X.LeastArea`.  So these statements can only be true through `LeastArea` (or a
defect of the model); the earlier "failures 0" (gl-p10-63, -67) covered `maxeps 2` and seed `0`
at `maxeps 10` only.  This residual is therefore OPEN and possibly FALSE as stated without a use
of `LeastArea`.

## Remaining gap

Planar existence of a region when every region meets `c` in at least three darts in a shape not
covered here or in badly placed one to five darts; on the model, exactly the `1260` failures
above, which have no region at all.

## Truth check (Python, not formalised)

`scratchpad/gl-p10-69/c3.py` (with `c1.py`, on gl-p10-67 `b1.py` / `b4.py`).  Per configuration
of the gl-p10-67 residual it builds exactly the Lean witness of each case here that applies and
asserts `roseLobeRegion_Block` / `_Place` on it (`0` assertion failures).

* Seeds `0`-`7`, `N = 60`, `maxeps 2` (`104954` configurations): gl-p10-67 residual `29`, new
  residual `0`.  Cases (overlapping): lake triple `14`, lake wrap `14`, inside quadruple `1`.
* Seeds `0`-`7`, `N = 300`, `maxeps 2` (`494752` configurations): residual `173`, new residual
  `0`.  Lake triple `80`, lake wrap `92`, inside triple `10`, inside quadruple `3`.
* Seeds `10`-`13`, `N = 1000`, `maxeps 2`: residual `517`, new residual `0`.  Lake triple
  `253`, lake wrap `261`, inside triple `31`, inside quadruple `3`.
* Seeds `0`-`7`, `N = 30`, `maxeps 10`: residual `10283` (seeds `0`, `1`, `2`, `5`, `6`: `48`,
  `573`, `648`, `5742`, `3272`), new residual `1260`, all on seed `5` and all model failures of
  the conclusion (above).  The inside quintuple is needed on seed `1` (`143`).

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10RoseExtremalTrim

/-- **The region choice outside the one- to five-dart cases** (OPEN; LOUD: the combinatorial
model REFUTES the conclusion on `1260` configurations at `maxeps 10`, see the module docstring;
LOUD: EQUIVALENT to `roseLobeMulti_Statement`, `roseLobeChoice_Statement` and
`roseLobeRegion_Statement` as a closed proposition, NOT strictly weaker, strictly smaller in
proof content).  The hypotheses of `roseLobeMulti_Statement` (including its five two-dart
exclusions) and six exclusions (no region of the six shapes of `TripleExcl`), with the same
conclusion. -/
def roseLobeTriple_Statement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    X.LeastArea →
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
      -- `hIn`: no inside singleton region, off the kept class, suitably placed
      (∀ d ∈ K.boundary.cycle,
        (∀ e ∈ K.boundary.cycle, Relation.EqvGen (CombMap.FaceClassStep X.toCombMap
          (walkKeep X.toCombMap K.boundary.cycle)) d e → e = d) →
        (∃ x, X.toCombMap.faceOf x = (cell X K.kept).face ∧ ¬Relation.EqvGen
          (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) d x) →
        (d ∉ invDarts X K.sourceArc.darts ∨ [d] <+: invDarts X K.sourceArc.darts ∨
          [d] <:+ invDarts X K.sourceArc.darts) →
        (d ∉ K.targetArc.darts ∨ [d] <:+ K.targetArc.darts) → False) →
      -- `hKept`: the kept class does not meet `c` in one dart, suitably placed
      (∀ x dk : X.toCombMap.Dart, X.toCombMap.faceOf x = (cell X K.kept).face →
        dk ∈ K.boundary.cycle →
        Relation.EqvGen (CombMap.FaceClassStep X.toCombMap
          (walkKeep X.toCombMap K.boundary.cycle)) dk x →
        (∀ e ∈ K.boundary.cycle, Relation.EqvGen (CombMap.FaceClassStep X.toCombMap
          (walkKeep X.toCombMap K.boundary.cycle)) dk e → e = dk) →
        (∃ e ∈ K.boundary.cycle, e ≠ dk) →
        (dk ∉ K.targetArc.darts ∨ [dk] <+: K.targetArc.darts) → False) →
      -- `hOut`: no outside singleton region missing the outer face and the source cell
      (∀ y ∈ K.boundary.cycle,
        (∀ e ∈ K.boundary.cycle, Relation.EqvGen (CombMap.FaceClassStep X.toCombMap
          (walkKeep X.toCombMap K.boundary.cycle)) (X.toCombMap.alpha y)
            (X.toCombMap.alpha e) → e = y) →
        (∀ x, X.toCombMap.faceOf x = X.outerFace → ¬Relation.EqvGen (CombMap.FaceClassStep
          X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) (X.toCombMap.alpha y) x) →
        (∀ x, X.toCombMap.faceOf x = (cell X K.source).face → ¬Relation.EqvGen
          (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle))
            (X.toCombMap.alpha y) x) →
        (∃ e ∈ K.boundary.cycle, e ≠ y) → False) →
      -- `hLakeA`, `hLakeW`: no two-dart lake (adjacent pair, or the two ends of `c`)
      roseLobeMulti_NoLakePair (CombMap.FaceClassStep X.toCombMap
          (walkKeep X.toCombMap K.boundary.cycle)) K.boundary.cycle ⇑X.toCombMap.alpha
        (fun x => X.toCombMap.faceOf x = X.outerFace)
        (fun x => X.toCombMap.faceOf x = (cell X K.source).face) →
      roseLobeMulti_NoLakeWrap (CombMap.FaceClassStep X.toCombMap
          (walkKeep X.toCombMap K.boundary.cycle)) K.boundary.cycle ⇑X.toCombMap.alpha
        (fun x => X.toCombMap.faceOf x = X.outerFace)
        (fun x => X.toCombMap.faceOf x = (cell X K.source).face) →
      -- `hInA`, `hInW`: no two-dart inside region off the kept class, suitably placed
      roseLobeMulti_NoLobePair (CombMap.FaceClassStep X.toCombMap
          (walkKeep X.toCombMap K.boundary.cycle)) K.boundary.cycle
        (invDarts X K.sourceArc.darts) K.targetArc.darts
        (fun x => X.toCombMap.faceOf x = (cell X K.kept).face) →
      roseLobeMulti_NoLobeWrap (CombMap.FaceClassStep X.toCombMap
          (walkKeep X.toCombMap K.boundary.cycle)) K.boundary.cycle K.targetArc.darts
        (fun x => X.toCombMap.faceOf x = (cell X K.kept).face) →
      -- `hKeptA`: the kept class does not meet `c` in two consecutive darts, suitably placed
      roseLobeMulti_NoKeptPair (CombMap.FaceClassStep X.toCombMap
          (walkKeep X.toCombMap K.boundary.cycle)) K.boundary.cycle K.targetArc.darts
        (fun x => X.toCombMap.faceOf x = (cell X K.kept).face) →
      -- `hLake3`, `hLake3L`, `hLake3R`: no three-dart lake (consecutive, or wrapping)
      roseLobeTriple_NoLakeRun (CombMap.FaceClassStep X.toCombMap
          (walkKeep X.toCombMap K.boundary.cycle)) K.boundary.cycle ⇑X.toCombMap.alpha
        (fun x => X.toCombMap.faceOf x = X.outerFace)
        (fun x => X.toCombMap.faceOf x = (cell X K.source).face) →
      roseLobeTriple_NoLakeWrapL (CombMap.FaceClassStep X.toCombMap
          (walkKeep X.toCombMap K.boundary.cycle)) K.boundary.cycle ⇑X.toCombMap.alpha
        (fun x => X.toCombMap.faceOf x = X.outerFace)
        (fun x => X.toCombMap.faceOf x = (cell X K.source).face) →
      roseLobeTriple_NoLakeWrapR (CombMap.FaceClassStep X.toCombMap
          (walkKeep X.toCombMap K.boundary.cycle)) K.boundary.cycle ⇑X.toCombMap.alpha
        (fun x => X.toCombMap.faceOf x = X.outerFace)
        (fun x => X.toCombMap.faceOf x = (cell X K.source).face) →
      -- `hIn3`, `hIn4`, `hIn5`: no closed consecutive inside block of three to five darts
      roseLobeTriple_NoLobeRun (CombMap.FaceClassStep X.toCombMap
          (walkKeep X.toCombMap K.boundary.cycle)) K.boundary.cycle
        (invDarts X K.sourceArc.darts) K.targetArc.darts
        (fun x => X.toCombMap.faceOf x = (cell X K.kept).face) →
      roseLobeTriple_NoLobeQuad (CombMap.FaceClassStep X.toCombMap
          (walkKeep X.toCombMap K.boundary.cycle)) K.boundary.cycle
        (invDarts X K.sourceArc.darts) K.targetArc.darts
        (fun x => X.toCombMap.faceOf x = (cell X K.kept).face) →
      roseLobeTriple_NoLobeQuint (CombMap.FaceClassStep X.toCombMap
          (walkKeep X.toCombMap K.boundary.cycle)) K.boundary.cycle
        (invDarts X K.sourceArc.darts) K.targetArc.darts
        (fun x => X.toCombMap.faceOf x = (cell X K.kept).face) →
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
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeTriple_Statement

/-- **The two-dart residual from the five-dart residual**: if the conclusion failed, each of the
six new exclusions would be violated by the proved case lemmas (`roseLobeTriple_lake_run`,
`_lake_wrapL`, `_lake_wrapR`, `_lobe_run`, `_lobe_quad`, `_lobe_quint`), so the residual
applies. -/
theorem roseLobeTriple_multi_of (h : roseLobeTriple_Statement.{u, w, v}) :
    roseLobeMulti_Statement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose hpl hiff hcov
    hside hI hT hIn hKept hOut hLakeA hLakeW hInA hInW hKeptA
  by_contra hne
  apply hne
  refine h D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose hpl hiff hcov hside hI hT
    hIn hKept hOut hLakeA hLakeW hInA hInW hKeptA ?_ ?_ ?_ ?_ ?_ ?_
  · intro A C a1 a2 a3 hc hAC h12 h13 hlone hO hS
    exact hne (Or.inr (roseLobeTriple_lake_run
      (f := ⇑X.toCombMap.alpha)
      (PO := fun x => X.toCombMap.faceOf x = X.outerFace)
      (PS := fun x => X.toCombMap.faceOf x = (cell X K.source).face)
      K.boundary.cycle_nodup hc hAC h12 h13 hlone hO hS))
  · intro M a1 a2 a3 hc hM h12 h13 hlone hO hS
    exact hne (Or.inr (roseLobeTriple_lake_wrapL
      (f := ⇑X.toCombMap.alpha)
      (PO := fun x => X.toCombMap.faceOf x = X.outerFace)
      (PS := fun x => X.toCombMap.faceOf x = (cell X K.source).face)
      K.boundary.cycle_nodup hc hM h12 h13 hlone hO hS))
  · intro M a1 a2 a3 hc hM h12 h13 hlone hO hS
    exact hne (Or.inr (roseLobeTriple_lake_wrapR
      (f := ⇑X.toCombMap.alpha)
      (PO := fun x => X.toCombMap.faceOf x = X.outerFace)
      (PS := fun x => X.toCombMap.faceOf x = (cell X K.source).face)
      K.boundary.cycle_nodup hc hM h12 h13 hlone hO hS))
  · intro A C a1 a2 a3 hc hlone hx hIB hTB
    obtain ⟨x, hxk, hax⟩ := hx
    exact hne (Or.inl (roseLobeTriple_lobe_run
      (kp := fun x => X.toCombMap.faceOf x = (cell X K.kept).face)
      K.boundary.cycle_nodup hc hlone hxk hax
      (roseLobeChoice_kept_on K hcov hside hxk) hIB hTB))
  · intro A C a1 a2 a3 a4 hc hlone hx hIB hTB
    obtain ⟨x, hxk, hax⟩ := hx
    exact hne (Or.inl (roseLobeTriple_lobe_quad
      (kp := fun x => X.toCombMap.faceOf x = (cell X K.kept).face)
      K.boundary.cycle_nodup hc hlone hxk hax
      (roseLobeChoice_kept_on K hcov hside hxk) hIB hTB))
  · intro A C a1 a2 a3 a4 a5 hc hlone hx hIB hTB
    obtain ⟨x, hxk, hax⟩ := hx
    exact hne (Or.inl (roseLobeTriple_lobe_quint
      (kp := fun x => X.toCombMap.faceOf x = (cell X K.kept).face)
      K.boundary.cycle_nodup hc hlone hxk hax
      (roseLobeChoice_kept_on K hcov hside hxk) hIB hTB))

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeTriple_multi_of

/-- **The singleton residual from the five-dart residual.** -/
theorem roseLobeTriple_choice_of (h : roseLobeTriple_Statement.{u, w, v}) :
    roseLobeChoice_Statement.{u, w, v} :=
  roseLobeMulti_choice_of (roseLobeTriple_multi_of h)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeTriple_choice_of

/-- **The region choice from the five-dart residual.** -/
theorem roseLobeTriple_region_of (h : roseLobeTriple_Statement.{u, w, v}) :
    roseLobeRegion_Statement.{u, w, v} :=
  roseLobeMulti_region_of (roseLobeTriple_multi_of h)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeTriple_region_of

/-- **The planar core from the five-dart residual.** -/
theorem roseLobeTriple_core_of (h : roseLobeTriple_Statement.{u, w, v}) :
    roseLobeCore_Statement.{u, w, v} :=
  roseLobeMulti_core_of (roseLobeTriple_multi_of h)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeTriple_core_of

/-- **The Greendlinger leaf from the five-dart residual.** -/
theorem roseLobeTriple_green_of
    (hoff : P07InnerPocket.PocketFourPieceOffStatement.{u, w, v})
    (h : roseLobeTriple_Statement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  roseLobeMulti_green_of hoff (roseLobeTriple_multi_of h)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeTriple_green_of

/-- **The outer-pinch step from the five-dart residual.** -/
theorem roseLobeTriple_pinch_of (h : roseLobeTriple_Statement.{u, w, v}) :
    PocketOuterPinchStepSectionStatement.{u, w, v} :=
  roseLobeMulti_pinch_of (roseLobeTriple_multi_of h)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeTriple_pinch_of

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe
