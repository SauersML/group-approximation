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

section Case

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **The source-arc lobe case** at the pocket `K`: the lobe rooted at every dart of the reversed
source arc `t₁⁻¹` colours no other dart of the boundary cycle, leaves a dart of the kept cell
uncoloured, and `s₁ ++ (s₂ ++ t₂)` is nonempty. -/
abbrev lobeRm86_SrcLobe (K : PocketFaceSet D eps X lo hi) : Prop :=
  invDarts X K.sourceArc.darts ≠ [] ∧
    (∀ d ∈ K.firstSide ++ (K.secondSide ++ K.targetArc.darts),
      roseJunctionCore_lobeColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)
        (invDarts X K.sourceArc.darts) d = false) ∧
    (∃ x, X.toCombMap.faceOf x = (cell X K.kept).face ∧
      roseJunctionCore_lobeColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)
        (invDarts X K.sourceArc.darts) x = false) ∧
    K.firstSide ++ (K.secondSide ++ K.targetArc.darts) ≠ []

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LobeRemoval.lobeRm86_SrcLobe

/-- **The source-arc lobe is a contiguous removed block**: in the source-arc lobe case the
conclusion of `roseLobeBlk_BlockStatement` holds at `K`, with `A = s₁`, `B = t₁⁻¹` and
`C = s₂ ++ t₂`. -/
theorem lobeRm86_blkAt_of_src (K : PocketFaceSet D eps X lo hi) (h : lobeRm86_SrcLobe K) :
    roseLobeOsin_BlkAt K := by
  obtain ⟨hne, hrest, ⟨x, hx, hzx⟩, hACne⟩ := h
  have hrs : ∀ r ∈ invDarts X K.sourceArc.darts, r ∈ K.boundary.cycle := by
    intro r hr
    rw [K.decomposition]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hr))
  have hmem : ∀ d ∈ K.firstSide ++ (K.secondSide ++ K.targetArc.darts),
      d ∈ K.boundary.cycle := by
    intro d hd
    rw [K.decomposition]
    rcases List.mem_append.mp hd with hd | hd
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hd))
    · rcases List.mem_append.mp hd with hd | hd
      · exact List.mem_append_left _ (List.mem_append_right _ hd)
      · exact List.mem_append_right _ hd
  have hkx : X.toCombMap.faceOf x ∈ K.faces := by
    rw [hx]
    exact K.kept_mem
  have hkept := roseJunctionCore_mem_flipFaces (c := K.boundary.cycle)
    (invDarts X K.sourceArc.darts) hkx hzx
  rw [hx] at hkept
  have htgtf := lobeRm86_filter_eq_self K.boundary.cycle_mem_iff hrs (l := K.targetArc.darts)
    (fun d hd => hmem d (List.mem_append_right _ (List.mem_append_right _ hd)))
    (fun d hd => hrest d (List.mem_append_right _ (List.mem_append_right _ hd)))
  refine ⟨invDarts X K.sourceArc.darts, Or.inl ⟨hne, hrs⟩,
    roseJunctionCore_not_mem_flipFaces K.boundary.cycle_mem_iff hrs K.source_not_mem, hkept,
    ?_, ⟨0, ?_, ?_⟩, K.firstSide, invDarts X K.sourceArc.darts,
    K.secondSide ++ K.targetArc.darts, ?_,
    Or.inl ⟨lobeRm86_filter_roots_eq_nil _ _, ?_, hACne⟩⟩
  · rw [lobeRm86_filter_roots_eq_nil]
    exact List.nil_infix
  · have hlt := K.targetArc.start.2
    omega
  · exact ⟨[], by rw [htgtf, List.drop_zero, List.append_nil]⟩
  · rw [K.decomposition]
    simp only [List.append_assoc]
  · exact lobeRm86_filter_eq_self K.boundary.cycle_mem_iff hrs hmem hrest

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LobeRemoval.lobeRm86_blkAt_of_src

/-- **The lobe removal in the source-arc lobe case**, at one pocket: `lobeRm86_blkAt_of_src`
followed by the proved pointwise chain Blk to the filtered listing to the lobe removal. -/
theorem lobeRm86_lobeAt_of_src (K : PocketFaceSet D eps X lo hi) (hK : K.ClosedWalk)
    (hsrc : K.sourceArc.length < (cellDarts X K.source).length)
    (htgt : K.targetArc.length < (outerDarts X).length) (h : lobeRm86_SrcLobe K) :
    roseLobeOsin_LobeAt K :=
  roseLobeOsin_lobeAt_of K hsrc htgt (roseLobeOsin_filterAt_of K hK (lobeRm86_blkAt_of_src K h))

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LobeRemoval.lobeRm86_lobeAt_of_src

end Case

/-- **The lobe removal off the source-arc lobe case** (OPEN, PLAUSIBLE; vacuous on both known
models, see the module docstring; LOUD: only EQUIVALENT to
`roseJunctionCore_LobeRemovalStatement` as a closed proposition, pointwise strictly weaker).
As `roseJunctionCore_LobeRemovalStatement`, with the extra hypothesis that the pocket is not in
the source-arc lobe case `lobeRm86_SrcLobe`. -/
def lobeRm86_ResidualStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ), X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
      ¬ lobeRm86_SrcLobe K →
        roseLobeOsin_LobeAt K

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LobeRemoval.lobeRm86_ResidualStatement

/-- **The lobe removal from the residual**: split on the source-arc lobe case. -/
theorem lobeRm86_lobeRemoval_of (h : lobeRm86_ResidualStatement.{u, w, v}) :
    roseJunctionCore_LobeRemovalStatement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  by_cases hcase : lobeRm86_SrcLobe K
  · exact lobeRm86_lobeAt_of_src K hK hsrc htgt hcase
  · exact h D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose hcase

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LobeRemoval.lobeRm86_lobeRemoval_of

/-- **The sub-arc region move from the residual** (route (a) of the rose step). -/
theorem lobeRm86_regionMoveSubArc_of (h : lobeRm86_ResidualStatement.{u, w, v}) :
    P10Rose.RoseRegionMoveSubArcStatement.{u, w, v} :=
  roseJunctionCore_regionMoveSubArc_of_lobeRemoval (lobeRm86_lobeRemoval_of h)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LobeRemoval.lobeRm86_regionMoveSubArc_of

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LobeRemoval
