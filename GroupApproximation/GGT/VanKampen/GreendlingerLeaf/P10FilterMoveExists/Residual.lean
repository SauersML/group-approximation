import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10FilterMoveExists.Colour
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.Predicate
import GroupApproximation.Meta.AxiomGuard

/-!
# The quadrant move on a pinched boundary cycle (the residual of gl-p10-91)

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-91.

`p10FM_QuadrantMoveStatement` is a statement about a planar combinatorial map `M`, a face set
`F` and its boundary cycle `c` only: it does not mention `PocketFaceSet`, `DiscDiagram`,
labels or least area.  Its hypotheses are the pocket-free shadow of the hypotheses of
`P10Rose.RoseRegionMoveSubArcStatement`:

* `c` is a closed dart walk listing each boundary dart of `F` once, `F` is pinched, `c` is not
  in first-turn order, and every non-first turn of `c` is crossed (`p10FM_FirstTurns`,
  `p10FM_AllCrossed`: the definitions of `PocketFaceSet.FirstTurns` and
  `P10ChordLift.AllNonFirstTurnsCrossed`, verbatim for a list `c`);
* two faces `o ≠ s` off `F` (the outer face, the source cell) with face boundaries `bo`, `bs`,
  a face `k ∈ F` (the kept cell), a proper cyclic arc `a` of `bs` and a proper cyclic arc `b` of
  the reversed outer darts, with `c = s₁ ++ a⁻¹ ++ s₂ ++ b`.

Its conclusion asks for a **quadrant move**: a list `B ⊆ c` and Booleans `p q` such that the
quadrant colouring `z = p10FM_z M F B p q` (module `Colour`) leaves `o`, `s`, `k` off the
quadrant, removes some dart of `c`, keeps an infix of `a⁻¹` and a prefix of `b`, and keeps a
closed dart walk `c.filter (movePred M z)`.

## Intended proof of the target from the residual (module `Endpoint`, PROVED)

Instantiate with `M = X.toCombMap`, `F = K.faces`, `c = K.boundary`, `o = X.outerFace`,
`s`, `k` the faces of `K.source`, `K.kept`, `a = K.sourceArc`, `b = K.targetArc`.  For the
resulting `z`: region constancy and independence are `p10FM_z_step`, `p10FM_z_indep`; the outer
face and the source cell stay out, and the kept cell stays in, by `p10FM_not_mem_flip`,
`p10FM_mem_flip`; the kept infix of `a⁻¹` is `t₁⁻¹` for an arc `t₁` of the source cell
(`P10RoseLobe.roseLobeFL_exists_arc_invDarts_of_infix`); the kept prefix of `b` is an arc `t₂`
inside the old window (`P10RoseLobe.roseLobeFL_exists_arc_of_prefix_drop` with `k = 0`).  This
is `P10RegionSubArc.subArc_FilterMove K z`, which proves the goal
(`P10RegionSubArc.subArc_goal_of_filterMove`).

## Intended proof of the residual (OPEN)

Take `B` a simple closed sub-walk of `c` (a cyclically contiguous block of `c` visiting no vertex
twice, which exists because `F` is pinched) and one of the four quadrants of its side and of `F`.
Every tested configuration has such a choice (see the truth check); the combinatorial argument
choosing it (from the crossing hypothesis and the contiguity of the two arcs) is not formalised.

## LOUD: strength of the residual

The residual is **not** logically weaker than the target.  It drops `LeastArea`, the labels and
the side-length bounds of the pocket, allows arbitrary faces `o, s, k` and arbitrary face
boundaries, and restricts the witness colourings to quadrant colourings; so it is at least as
strong as the target in generality (a strictly weaker statement with a proved reduction to the
target would be equivalent to it).  It is the form asked for by the lane: a purely combinatorial
planar statement about closed walks on a `CombMap`, not mentioning `PocketFaceSet`.  What it
removes from the target is **proof content**: all colour clauses, the flipped-face clauses and
both arc constructions are discharged in modules `Colour` and `Endpoint`.

## Truth check (not formalised)

`scratchpad/gl-p10-91/loose2.py` (with `CONTIG = 1`): random planar maps with at most 8 edges,
every face set `F` of at most 4 faces with a pinched boundary, every closed walk `c` through the
boundary darts satisfying the gl-p10-46 premises (not in first-turn order, every non-first turn
crossed), every choice of faces `o ≠ s` off `F`, `k ∈ F`, every rotation of `c` and every
split `c = s₁ ++ a⁻¹ ++ s₂ ++ b` with `a`, `b` proper cyclic arcs of the boundaries of `s` and of
the reversed boundary of `o`.  Witness search: `B` a cyclically contiguous simple loop of `c`,
four quadrants.  Seeds 1–5: `128730 + 623530 + 171224 + 104172 + 389074` configurations,
**0 failures**.  The hypotheses are needed: without the rose premises (`nopre.py`) `48832` of
`416554` configurations fail, with only `¬FirstTurns` (`nftonly.py`) `48662` of `335710` fail,
and without arc contiguity (`CONTIG = 0`) `80` fail.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10FilterMoveExists

universe v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove

open scoped Classical

section Turns

variable (M : CombMap.{v})

/-- **First-turn order** of a list of darts: `PocketFaceSet.FirstTurns` for the list `c`. -/
def p10FM_FirstTurns (c : List M.Dart) (hc : c ≠ []) : Prop :=
  c.IsChain (fun d e => FirstTurn M (c.reverse.map M.alpha) (M.alpha e) (M.alpha d)) ∧
    FirstTurn M (c.reverse.map M.alpha) (M.alpha (c.head hc)) (M.alpha (c.getLast hc))

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10FilterMoveExists.p10FM_FirstTurns

/-- **A non-first turn** of `c`: `P10ChordLift.NonFirstTurn` for the list `c`. -/
def p10FM_NonFirstTurn (c : List M.Dart) (d₀ : M.Dart) (hd₀ : d₀ ∈ c) : Prop :=
  ¬ FirstTurn M (c.reverse.map M.alpha) (M.alpha (c.next d₀ hd₀)) (M.alpha d₀)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10FilterMoveExists.p10FM_NonFirstTurn

/-- **A crossed turn** of `c`: `P10ChordLift.TurnCrossed` for the list `c`. -/
def p10FM_TurnCrossed (c : List M.Dart) (d₀ : M.Dart) (hd₀ : d₀ ∈ c) : Prop :=
  ∃ (d : M.Dart) (hd : d ∈ c), d ≠ d₀ ∧ M.sigma.SameCycle (M.alpha d₀) (M.alpha d) ∧
    ¬ (RotationBetween M (M.alpha d₀) (c.next d₀ hd₀) (M.alpha d) ↔
      RotationBetween M (M.alpha d₀) (c.next d₀ hd₀) (c.next d hd))

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10FilterMoveExists.p10FM_TurnCrossed

/-- **The rose configuration** of `c`: `P10ChordLift.AllNonFirstTurnsCrossed` for `c`. -/
def p10FM_AllCrossed (c : List M.Dart) : Prop :=
  ∀ (d₀ : M.Dart) (hd₀ : d₀ ∈ c), p10FM_NonFirstTurn M c d₀ hd₀ → p10FM_TurnCrossed M c d₀ hd₀

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10FilterMoveExists.p10FM_AllCrossed

end Turns

/-- **The quadrant move** (OPEN; the residual of gl-p10-91, see the module docstring).  On a
planar map, a pinched boundary cycle `c` of a face set `F` in rose configuration, split as
`s₁ ++ a⁻¹ ++ s₂ ++ b` along proper arcs of two faces `s ≠ o` off `F`, has a quadrant colouring
leaving `o`, `s` and a given `k ∈ F` unflipped, removing some dart of `c`, keeping an infix of
`a⁻¹` and a prefix of `b`, and keeping a closed dart walk. -/
def p10FM_QuadrantMoveStatement : Prop :=
  ∀ (M : CombMap.{v}) (F : Finset M.Face) (c : BoundaryCycle M F) (o s k : M.Face)
    (bs : FaceBoundary M s) (bo : FaceBoundary M o) (a : CyclicArc bs.darts)
    (b : CyclicArc (bo.darts.reverse.map M.alpha)) (s₁ s₂ : List M.Dart),
    M.IsPlanar → IsClosedDartWalk M c.cycle → ¬Unpinched M F →
    ¬p10FM_FirstTurns M c.cycle c.cycle_nonempty → p10FM_AllCrossed M c.cycle →
    o ∉ F → s ∉ F → s ≠ o → k ∈ F →
    a.length < bs.darts.length → b.length < (bo.darts.reverse.map M.alpha).length →
    c.cycle = s₁ ++ a.darts.reverse.map M.alpha ++ s₂ ++ b.darts →
    ∃ (B : List M.Dart) (p q : Bool), (∀ d ∈ B, d ∈ c.cycle) ∧
      ¬p10FM_InZ M F B p q o ∧ ¬p10FM_InZ M F B p q s ∧ ¬p10FM_InZ M F B p q k ∧
      (∃ y ∈ c.cycle, movePred M (p10FM_z M F B p q) y = false) ∧
      (a.darts.reverse.map M.alpha).filter (movePred M (p10FM_z M F B p q)) <:+:
        a.darts.reverse.map M.alpha ∧
      b.darts.filter (movePred M (p10FM_z M F B p q)) <+: b.darts ∧
      IsClosedDartWalk M (c.cycle.filter (movePred M (p10FM_z M F B p q)))

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10FilterMoveExists.p10FM_QuadrantMoveStatement

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10FilterMoveExists
