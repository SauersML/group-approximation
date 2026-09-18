import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.GFaceWindSevenStep
import GroupApproximation.Meta.AxiomGuard

/-!
# Winding choice of `F'`: the residual of `PosStep` after sign-forced steps

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-64.

Route.  `gfaceWindSix_PosStep` is reduced to its residual `gfaceWindSeven_Statement`: the
same claim at states that, in addition, have
1. no inner simple lobe `A` whose side contains the base face `o`,
2. no wrapping simple lobe `q ++ p` whose side contains `o`,
3. no two-lobe split `c = p ++ A ++ q` with both `A` and `q ++ p` simple.
States with 1 or 2 have a sign-keeping step by `gfaceWindSeven_inner_neg` /
`gfaceWindSeven_wrap_neg`, states with 3 by `gfaceWindSeven_two` (`gfaceWindSevenStep`).

* `gfaceWindSeven_Statement` (hypothesis, see the truth check).
* `gfaceWindSeven_posStep` (proved): `Statement → gfaceWindSix_PosStep`.
* `gfaceWindSeven_of_posStep` (proved): `gfaceWindSix_PosStep → Statement`.

**LOUD: as propositions the residual is EQUIVALENT to `PosStep`** (both directions are
proved), since every residual state is a `PosStep` state.  It is strictly smaller in proof
content: in the models, 86-90% of the `PosStep` states (negative lobes, two-lobe splits) are
discharged here, and only states all of whose lobes have `o` off their side and which have no
two-lobe split remain.  There one needs a lobe `W` with `g ≥ 1` on the side of `W`.

**LOUD: this does not give `gfaceWindSix_Statement`.**  `PosStep` only feeds
`gfaceWindSix_pocket`, whose conclusion holds without it (`gfaceWindSeven_pocket`) and is too
weak for the face-set clauses; the terminal-state strategy is FALSE as a complete strategy.

## Truth check

Scratchpad `gl-p10-64/seven.py` (models of `gl-p10-49/gface.py`, integer reach of
`gl-p10-55/wind.py`): residual states 136855 (random seed 1), 114681 (seed 3), 155489
(witness seed 2), each with a sign-keeping step: 0 failures.  `gl-p10-64/probe.py` on residual
states (177375 seed 1, 177063 witness): excising a lobe of inclusion-minimal side keeps
`g ≥ 0` in all of them (hint only, not formalised).  Not modelled: least area, labels.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

universe v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10ExtremalWrap GFaceChoose
open scoped Classical

/-- **The residual of `PosStep`** (hypothesis; true in all models, see the module docstring).
At a reached state with `g ≥ 0` and a repeated vertex, having no negative lobe and no
two-lobe split, some excision step keeps `g ≥ 0`. -/
def gfaceWindSeven_Statement : Prop :=
  ∀ (M : CombMap.{v}), M.IsPlanar → ∀ (C : List M.Dart) (F : Finset M.Face) (o : M.Face),
    C.Nodup → (∀ d, Surgery.MapCollapse.IsBoundaryDart M F d ↔ d ∈ C) →
    C.IsChain (fun d e => M.vertexOf (M.alpha d) = M.vertexOf e) → gfaceWindSix_Bal M C →
    o ∉ F → ∀ (c : List M.Dart) (g : M.Face → ℤ),
      Relation.ReflTransGen (gfaceWind_Step M o) (C, gfaceWind_ind F) (c, g) →
      (∀ f, 0 ≤ g f) → ¬ (c.map M.vertexOf).Nodup →
      (¬ ∃ p A q : List M.Dart, c = p ++ A ++ q ∧ IsSimpleClosedWalk M A ∧
        o ∈ SimpleClosedWalkSides.sideFaces M A) →
      (¬ ∃ p A q : List M.Dart, c = p ++ A ++ q ∧ IsSimpleClosedWalk M (q ++ p) ∧
        o ∈ SimpleClosedWalkSides.sideFaces M (q ++ p)) →
      (¬ ∃ p A q : List M.Dart, c = p ++ A ++ q ∧ IsSimpleClosedWalk M A ∧
        IsSimpleClosedWalk M (q ++ p)) →
        ∃ t : List M.Dart × (M.Face → ℤ), gfaceWind_Step M o (c, g) t ∧ ∀ f, 0 ≤ t.2 f

/-- **`PosStep` from its residual**: negative lobes and two-lobe splits are discharged by
`gfaceWindSeven_inner_neg`, `gfaceWindSeven_wrap_neg` and `gfaceWindSeven_two`. -/
theorem gfaceWindSeven_posStep (h : gfaceWindSeven_Statement.{v}) :
    gfaceWindSix_PosStep.{v} := by
  intro M hM C F o hC hS hch hbal ho c g hr hpos hnd
  by_cases h1 : ∃ p A q : List M.Dart, c = p ++ A ++ q ∧ IsSimpleClosedWalk M A ∧
      o ∈ SimpleClosedWalkSides.sideFaces M A
  · obtain ⟨p, A, q, hseg, hA, hoA⟩ := h1
    exact gfaceWindSeven_inner_neg hpos hseg hA hoA
  by_cases h2 : ∃ p A q : List M.Dart, c = p ++ A ++ q ∧ IsSimpleClosedWalk M (q ++ p) ∧
      o ∈ SimpleClosedWalkSides.sideFaces M (q ++ p)
  · obtain ⟨p, A, q, hseg, hB, hoB⟩ := h2
    exact gfaceWindSeven_wrap_neg hpos hseg hB hoB
  by_cases h3 : ∃ p A q : List M.Dart, c = p ++ A ++ q ∧ IsSimpleClosedWalk M A ∧
      IsSimpleClosedWalk M (q ++ p)
  · obtain ⟨p, A, q, hseg, hA, hB⟩ := h3
    have hinv : gfaceWind_Inv M C o c g :=
      gfaceWindSix_inv_rt (s := (C, gfaceWind_ind F)) (t := (c, g)) hM hC hr
        (gfaceWind_inv_start hS hch ho)
    exact gfaceWindSeven_two hM hC hinv hpos hseg hA hB
  exact h M hM C F o hC hS hch hbal ho c g hr hpos hnd h1 h2 h3

/-- **The residual from `PosStep`** (so the two are equivalent as propositions). -/
theorem gfaceWindSeven_of_posStep (h : gfaceWindSix_PosStep.{v}) :
    gfaceWindSeven_Statement.{v} := by
  intro M hM C F o hC hS hch hbal ho c g hr hpos hnd _ _ _
  exact h M hM C F o hC hS hch hbal ho c g hr hpos hnd

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSeven_Statement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSeven_posStep
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSeven_of_posStep
