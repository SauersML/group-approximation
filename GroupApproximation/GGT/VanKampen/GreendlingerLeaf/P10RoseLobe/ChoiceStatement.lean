import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.RegionStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.ChoiceCases

/-!
# The region choice outside the singleton cases

Lane gl-p10-63.  Notation as in `RegionStatement`: `M = X.toCombMap`, `c = K.boundary.cycle`,
`R = EqvGen (FaceClassStep M (walkKeep M c))`, `I = invDarts X K.sourceArc.darts`,
`T = K.targetArc.darts`, `c = P ++ T` (`K.decomposition`).

## Decision criterion (proved cases)

`roseLobeRegion_Statement` holds, with a witness named explicitly, in each of three cases in which
some region meets `c` in ONE dart (checked by `choice.py`):

* (in) a dart `d ∈ c` alone on `c` in its class, not in the kept class, not an inner dart of `I`,
  and ending `T` if on `T`: lobe `rs = [d]`, `B = [d]` (`roseLobeChoice_lobe_in`; the kept face
  is reached from `c` by `roseLobeChoice_kept_on`, from `hcov` and `hside`);
* (kept) the kept class meets `c` in one dart `dk`, which starts `T` if on `T`, and `c` has
  another dart: lobe `rs = A ++ C`, `B = [dk]` (`roseLobeChoice_lobe_kept`);
* (out) a dart `y ∈ c` such that no other `α e` (`e ∈ c`) is in the class of `α y`, that class
  missing the outer face and the source cell, and `c` has another dart: lake with `B = [y]`
  (`roseLobeChoice_lake_out`).

No contiguity is assumed: in each case the block is a single dart, so it is contiguous for free.

## LOUD: strength of the residual

`roseLobeChoice_Statement` is `roseLobeRegion_Statement` with three more hypotheses, the negations
of the three cases.  So it is implied by `roseLobeRegion_Statement`, and
`roseLobeChoice_region_of` proves the converse: as closed propositions the two are **EQUIVALENT**
(and pointwise too, since each case is proved); it is **NOT strictly weaker in logical strength**,
not stronger, and not false as far as the truth check sees.  It is **strictly smaller in proof
content**: every configuration with a singleton region of the three kinds is discharged here, and
the residual is vacuous on them, which in the truth check is every model configuration and about
`94.6%` of the random ones.

## Remaining gap

Planar existence of a region (lobe or lake) when every region meets `c` in at least two darts, or
only in badly placed single darts (inner darts of `I`, or non-final darts of `T` for the inside
case).  Here a genuinely contiguous multi-dart block must be produced from planarity.  Not proved.

## Truth check (Python, not formalised)

`scratchpad/gl-p10-63/choice.py` on the gl-p10-62 `region.py` / gl-p10-60 `core.py` generator.
Per configuration it reruns the planar checks of `core.py`, builds exactly the Lean witness of
each case that applies and asserts `roseLobeRegion_Block` / `_Place` on it (0 assertion
failures), and counts the residual configurations (no case applies) and checks the region
conclusion on them.  Models: `315` configurations, residual `0`.  Random seeds `0`-`7` (`300`
each, `maxeps 2`): `104954` configurations, residual `5634` (`5.4%`), region conclusion failures
`0` (residual included).  One `maxeps 10` run: `58120` configurations, residual `4300`, failures
`0`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10RoseExtremalTrim

/-- **The kept face is reached from the walk**: under the cover and side hypotheses, every dart of
the kept cell is `R`-joined to a dart of `c` (a cover dart `y` with `α y ∈ c` lies outside
`K.faces`, but the class of the kept cell is inside). -/
theorem roseLobeChoice_kept_on {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda} {eps : ℕ}
    {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ} (K : PocketFaceSet D eps X lo hi)
    (hcov : ∀ x : X.toCombMap.Dart, ∃ y, walkKeep X.toCombMap K.boundary.cycle y ∧
      Relation.EqvGen (CombMap.FaceClassStep X.toCombMap
        (walkKeep X.toCombMap K.boundary.cycle)) x y)
    (hside : ∀ x y : X.toCombMap.Dart, Relation.EqvGen (CombMap.FaceClassStep X.toCombMap
        (walkKeep X.toCombMap K.boundary.cycle)) x y →
      (X.toCombMap.faceOf x ∈ K.faces ↔ X.toCombMap.faceOf y ∈ K.faces))
    {x : X.toCombMap.Dart} (hx : X.toCombMap.faceOf x = (cell X K.kept).face) :
    ∃ y ∈ K.boundary.cycle, Relation.EqvGen (CombMap.FaceClassStep X.toCombMap
      (walkKeep X.toCombMap K.boundary.cycle)) y x := by
  obtain ⟨y, hy, hxy⟩ := hcov x
  have hyf : X.toCombMap.faceOf y ∈ K.faces := by
    refine (hside x y hxy).mp ?_
    rw [hx]
    exact K.kept_mem
  unfold walkKeep at hy
  rcases hy with hy | hy
  · exact ⟨y, hy, Relation.EqvGen.symm x y hxy⟩
  · exfalso
    have h2 := ((K.boundary.cycle_mem_iff _).mp hy).2
    rw [X.toCombMap.alpha_involutive y] at h2
    exact h2 hyf

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeChoice_kept_on

/-- **The region choice outside the singleton cases** (OPEN, PLAUSIBLE; truth-checked, see the
module docstring; LOUD: EQUIVALENT to `roseLobeRegion_Statement` as a closed proposition, NOT
strictly weaker, strictly smaller in proof content).  The hypotheses of `roseLobeRegion_Statement`
and three exclusions (`hIn`, `hKept`, `hOut`: no singleton region of the three proved kinds), with
the same conclusion. -/
def roseLobeChoice_Statement : Prop :=
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
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeChoice_Statement

/-- **The region choice from its non-singleton residual**: if the conclusion failed, each of the
three exclusions would be violated by the proved case lemmas (`roseLobeChoice_lobe_in`,
`_lobe_kept`, `_lake_out`), so the residual applies. -/
theorem roseLobeChoice_region_of (h : roseLobeChoice_Statement.{u, w, v}) :
    roseLobeRegion_Statement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose hpl hiff hcov
    hside hI hT
  by_contra hne
  apply hne
  refine h D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose hpl hiff hcov hside hI hT
    ?_ ?_ ?_
  · rintro d hd hlone ⟨x, hxk, hdx⟩ hdI hdT
    exact hne (Or.inl (roseLobeChoice_lobe_in
      (kp := fun x => X.toCombMap.faceOf x = (cell X K.kept).face)
      K.decomposition K.boundary.cycle_nodup hd hlone hxk hdx
      (roseLobeChoice_kept_on K hcov hside hxk) hdI hdT))
  · rintro x dk hxk hdk hdkx hlone hoth hdT
    exact hne (Or.inl (roseLobeChoice_lobe_kept
      (kp := fun x => X.toCombMap.faceOf x = (cell X K.kept).face)
      (I := invDarts X K.sourceArc.darts)
      K.decomposition K.boundary.cycle_nodup hxk hdk hdkx hlone hoth hdT))
  · rintro y hy hlone hO hS hoth
    exact hne (Or.inr (roseLobeChoice_lake_out
      (f := X.toCombMap.alpha)
      (PO := fun x => X.toCombMap.faceOf x = X.outerFace)
      (PS := fun x => X.toCombMap.faceOf x = (cell X K.source).face)
      K.boundary.cycle_nodup hy hlone hO hS hoth))

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeChoice_region_of

/-- **The planar core from the non-singleton residual.** -/
theorem roseLobeChoice_core_of (h : roseLobeChoice_Statement.{u, w, v}) :
    roseLobeCore_Statement.{u, w, v} :=
  roseLobeRegion_core_of (roseLobeChoice_region_of h)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeChoice_core_of

/-- **The Greendlinger leaf from the non-singleton residual.** -/
theorem roseLobeChoice_green_of
    (hoff : P07InnerPocket.PocketFourPieceOffStatement.{u, w, v})
    (h : roseLobeChoice_Statement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  roseLobeRegion_green_of hoff (roseLobeChoice_region_of h)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeChoice_green_of

/-- **The outer-pinch step from the non-singleton residual.** -/
theorem roseLobeChoice_pinch_of (h : roseLobeChoice_Statement.{u, w, v}) :
    PocketOuterPinchStepSectionStatement.{u, w, v} :=
  roseLobeRegion_pinch_of (roseLobeChoice_region_of h)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeChoice_pinch_of

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe
