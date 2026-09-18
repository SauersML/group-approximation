import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.OsinPointLobe
import GroupApproximation.Meta.AxiomGuard

/-!
# The lobe removal when the lobe is the whole reversed source arc

Lane gl-p10-86.  Leaf: `P10RoseExtremalTrim.roseJunctionCore_LobeRemovalStatement`
(`P10RoseExtremalTrim/JunctionCore.lean`), route (a) of the rose step: LobeRemoval to
`P10Rose.RoseRegionMoveSubArcStatement` to the in-place step.

## The case discharged here: the source-arc lobe

Write `c = s₁ ++ t₁⁻¹ ++ s₂ ++ t₂` for the boundary cycle of the pocket `K`, with
`I = t₁⁻¹ = invDarts X K.sourceArc.darts`, and take the roots `rs = I`.  Let
`z = roseJunctionCore_lobeColour M (walkKeep M c) I` be the colouring of the union of their walk
classes.  `lobeRm86_SrcLobe K` is the case in which

1. `I ≠ []`;
2. `z` colours no dart of `s₁ ++ (s₂ ++ t₂)` (the classes of `t₁⁻¹` meet `c` only in `t₁⁻¹`);
3. some dart of the kept cell is uncoloured;
4. `s₁ ++ (s₂ ++ t₂) ≠ []`.

Then the conclusion `roseLobeOsin_BlkAt K` of `P10RoseLobe.roseLobeBlk_BlockStatement` holds at
`K` with `A = s₁`, `B = I`, `C = s₂ ++ t₂` (`lobeRm86_blkAt_of_src`):

* the roots lie on `c` (they are the darts of `t₁⁻¹`);
* the source cell is outside the face set, so it stays outside
  (`roseJunctionCore_not_mem_flipFaces`); the kept cell keeps its uncoloured dart, so it stays
  inside (`roseJunctionCore_mem_flipFaces`);
* every root is removed (`roseJunctionCore_movePred_root`), so `I.filter P = []`, an infix
  of `I`;
* a dart of `A ++ C` is uncoloured by (2) and has uncoloured outer side, since the roots are on
  `c` (`roseJunctionCore_lobeColour_alpha_eq_false`); so `P` keeps all of `A ++ C`, and in
  particular all of `t₂`, a prefix of `t₂.drop 0`.

The pointwise chain `roseLobeOsin_filterAt_of`, `roseLobeOsin_lobeAt_of` then gives the
LobeRemoval conclusion at `K` (`lobeRm86_lobeAt_of_src`).  This step uses no planarity: closing
up the removed block is the vertex-balance argument of `P10RoseLobe/BlkBlock.lean`.

## The residual

`lobeRm86_ResidualStatement` is `roseJunctionCore_LobeRemovalStatement` with the extra
hypothesis `¬ lobeRm86_SrcLobe K`.  The reduction `lobeRm86_lobeRemoval_of` splits on the case.

## LOUD: strength of the residual

As closed propositions the residual and LobeRemoval are only EQUIVALENT (LobeRemoval implies the
residual by dropping a hypothesis, and the converse is `lobeRm86_lobeRemoval_of`).  Pointwise the
residual is strictly weaker: at every pocket in the source-arc lobe case it asks for nothing.
The proof content removed is exactly that case.  It is not an equivalent restatement of any other
Statement in `P10RoseLobe`: those are all stronger than LobeRemoval (Blk, FL, Place, Core,
Region all imply it).

## Truth check (Python, `scratchpad/gl-p10-86/`, not formalised)

`lobe_exact.py` evaluates the LobeRemoval conclusion exactly (every lobe, every single outside
region, every kept and source cell, every pair of arcs and every split of the sides).  It finds
`22` witnesses on the 16-dart model `Full.GL05c.Model.pocketK` and `20` on the 24-dart model
`roseJunctionRefute_pK`, so LobeRemoval is NOT refuted by either.  `srclobe.py` checks that both
models are in the source-arc lobe case: the classes of `t₁⁻¹ = [8,12,10]` (GL05c) and
`t₁⁻¹ = [2,16,4,6,18]` (pK) meet the cycle exactly in `t₁⁻¹`, the kept cell (face `0` in both)
is uncoloured, and `s₁ ++ s₂ ++ t₂ ≠ []`.  So the residual is vacuous on both models.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LobeRemoval

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10RoseExtremalTrim P10RoseLobe

section Lists

/-- The move of a lobe colouring removes all of its roots. -/
theorem lobeRm86_filter_roots_eq_nil {M : CombMap.{v}} (keep : M.Dart → Prop)
    (rs : List M.Dart) :
    rs.filter (movePred M (roseJunctionCore_lobeColour M keep rs)) = [] :=
  List.filter_eq_nil_iff.mpr fun _ hd => by
    rw [roseJunctionCore_movePred_root M keep hd]
    exact Bool.false_ne_true

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LobeRemoval.lobeRm86_filter_roots_eq_nil

/-- For roots on the walk `c`, the move keeps every uncoloured dart of `c`. -/
theorem lobeRm86_filter_eq_self {M : CombMap.{v}} {faces : Finset M.Face} {c : List M.Dart}
    (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M faces d)
    {rs : List M.Dart} (hrs : ∀ r ∈ rs, r ∈ c) {l : List M.Dart} (hl : ∀ d ∈ l, d ∈ c)
    (hz : ∀ d ∈ l, roseJunctionCore_lobeColour M (walkKeep M c) rs d = false) :
    l.filter (movePred M (roseJunctionCore_lobeColour M (walkKeep M c) rs)) = l :=
  List.filter_eq_self.mpr fun d hd => (movePred_eq_true_iff _ _ _).mpr
    ⟨hz d hd, roseJunctionCore_lobeColour_alpha_eq_false hc hrs (hl d hd)⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LobeRemoval.lobeRm86_filter_eq_self

end Lists
