import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.ChoiceStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.MultiExcl
import GroupApproximation.Meta.AxiomGuard

/-!
# The region choice outside the one- and two-dart cases

Lane gl-p10-67.  Notation as in `ChoiceStatement`: `M = X.toCombMap`, `c = K.boundary.cycle`,
`R = EqvGen (FaceClassStep M (walkKeep M c))`, `I = invDarts X K.sourceArc.darts`,
`T = K.targetArc.darts`.

## Classification of the gl-p10-63 residual (Step 1)

On the residual of `roseLobeChoice_Statement` (no singleton region of the three proved kinds) the
witnessing region almost always meets `c` in exactly TWO darts that are cyclically adjacent on
`c`.  Five uniform two-dart case lemmas, each with an explicitly named witness, are proved
(`MultiLake`, `MultiLobe`):

* (lake pair / lake wrap) the class of `α a` meets `α c` in `α a`, `α b` only, for `a`, `b`
  consecutive on `c` (`c = A ++ [a, b] ++ C`) or the two ends of `c` (`c = [a] ++ M ++ [b]`), and
  misses the outer face and the source cell: the lake at `a`;
* (inside pair / inside wrap) the class of `a` meets `c` in `a`, `b` only (same two shapes), is
  not the kept class, and is suitably placed relative to `I` and `T`: the lobe `rs = [a]`;
* (kept pair) the kept class meets `c` in two consecutive darts `a`, `b`, suitably placed: the
  lobe `rs = A ++ C`.

No contiguity is assumed: the two darts are given with their positions.  A general "run" lemma
(a class meeting `c` in any contiguous run) would be the contiguous-interval route, so we stop
at two darts.

## LOUD: strength of the residual

`roseLobeMulti_Statement` is `roseLobeChoice_Statement` with five more hypotheses, the negations
of the five two-dart cases (`roseLobeMulti_NoLakePair`, `_NoLakeWrap`, `_NoLobePair`,
`_NoLobeWrap`, `_NoKeptPair`).  So it is implied by `roseLobeChoice_Statement`, and
`roseLobeMulti_choice_of` proves the converse: as closed propositions the two (and
`roseLobeRegion_Statement`) are **EQUIVALENT**; it is **NOT strictly weaker in logical strength**,
not stronger, and not false as far as the truth check sees.  It is **strictly smaller in proof
content**: every configuration with a two-dart region of the five kinds is now discharged, and on
the random configurations the residual shrinks from `5634` to `29` (below).

## Remaining gap

Planar existence of a region when every region meets `c` in at least three darts or in badly
placed one or two darts.  In the truth check the surviving configurations are witnessed only by
lakes whose class meets `c` in THREE cyclically consecutive darts (infix or wrapping) and, once,
by a lobe of two classes meeting `c` in four consecutive darts; at `maxeps 10` also by one-class
lobes meeting `c` in four consecutive darts.  Not proved.

## Truth check (Python, not formalised)

`scratchpad/gl-p10-67/b5.py` (with `b4.py`) on the gl-p10-63 `choice.py` / gl-p10-62 `region.py`
generator.  Per configuration it applies the gl-p10-63 singleton cases, then builds exactly the
Lean witness of each two-dart case that applies and asserts `roseLobeRegion_Block` / `_Place` on
it (`0` assertion failures), counts the residual and checks the region conclusion on it.

* Models: `315` configurations, gl-p10-63 residual already `0`.
* Random seeds `0`-`7`, `N = 60`, `maxeps 2` (the gl-p10-63 run): `104954` configurations,
  gl-p10-63 residual `5634`, new residual `29` (`0.028%`; seeds `0`, `1`, `5`: `12`, `2`, `15`),
  region conclusion failures `0`.  Applicable cases (overlapping): lake pair `4234`, lake wrap
  `1240`, inside pair `342`, inside wrap `35`, kept pair `160`.
* Seed `0`, `N = 30`, `maxeps 10`: `53834` configurations, gl-p10-63 residual `3780`, new
  residual `48`, failures `0`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10RoseExtremalTrim

/-- **The region choice outside the one- and two-dart cases** (OPEN, PLAUSIBLE; truth-checked,
see the module docstring; LOUD: EQUIVALENT to `roseLobeChoice_Statement` and to
`roseLobeRegion_Statement` as a closed proposition, NOT strictly weaker, strictly smaller in proof
content).  The hypotheses of `roseLobeChoice_Statement` (including `hIn`, `hKept`, `hOut`) and
five exclusions (no two-dart region of the five proved kinds), with the same conclusion. -/
def roseLobeMulti_Statement : Prop :=
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
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeMulti_Statement

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe
