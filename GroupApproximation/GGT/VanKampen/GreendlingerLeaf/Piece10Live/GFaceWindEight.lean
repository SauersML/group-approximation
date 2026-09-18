import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.GFaceWindEightClean
import GroupApproximation.Meta.AxiomGuard

/-!
# Winding choice of `F'`: the residual of `PosStep` is a clean-lobe existence statement

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-65.

Route.  `gfaceWindSeven_Statement` (the residual of `gfaceWindSix_PosStep`) asks for a
sign-keeping excision step at reached states with `g ≥ 0`, a repeated vertex, no negative lobe
and no two-lobe split.  By `gfaceWindEight_step` (`Piece10Live/GFaceWindEightClean`) it is
enough to find a **clean** simple lobe there: its side avoids the edges of the rest of the walk,
so `g ≥ 1` on its side and excising it keeps `g ≥ 0`.

* `gfaceWindEight_Statement` (hypothesis, see the truth check): at such a state some simple
  lobe (inner `A` with rest `p ++ q`, or wrapping `q ++ p` with rest `A`) is clean.
* `gfaceWindEight_seven` (proved): `Statement → gfaceWindSeven_Statement`.
* `gfaceWindEight_posStep` (proved): `Statement → gfaceWindSix_PosStep`.
* `gfaceWindEight_lobe`, `gfaceWindEight_descent` (proved): a reached state with a repeated
  vertex has a lobe, and if every non-clean lobe has a lobe of strictly smaller side, a clean
  lobe exists.  So the Statement follows from that descent at residual states.

**LOUD: logical strength.**  The Statement is NOT weaker than `gfaceWindSeven_Statement`: it
implies it (`gfaceWindEight_seven`), and the converse is not proved (a sign-keeping step need
not excise a clean lobe).  It is strictly smaller in proof content: its conclusion is free of
`g`, a statement about the walk and the map only, and all sign bookkeeping (constancy of `g` on
face classes, `g ≥ 1` on the side, the base face off the side) is discharged here.

**LOUD: the residual hypotheses are needed.**  On all reached pinched states with `g ≥ 0` a
clean lobe exists only in about 71% of them (see below), so the Statement is false without the
"no negative lobe / no two-lobe split" hypotheses.

**LOUD: this does not give `gfaceWindSix_Statement`** (see `Piece10Live/GFaceWindSeven`).

Remaining gap (why it is not closed here): a non-clean lobe `W` has its side meet an edge of
the rest `R`; one needs a lobe of `c` nested inside the side of `W` (a strictly smaller side).
That is a Jordan-type nesting of sides of stretches of one walk, not available in the corpus.

## Truth check

Scratchpad `gl-p10-65/eight.py` (models of `gl-p10-49/gface.py`, integer reach of
`gl-p10-55/wind.py`, lobes of `gl-p10-64/seven.py`).  Residual states / with a clean lobe:
random seed 1: 132113 / 132113; seed 3: 108461 / 108461; witness seed 2: 283093 / 283093.
In all of them every inclusion-minimal and every card-minimal lobe is clean.  Reached pinched
states with `g ≥ 0` (not residual) with a clean lobe: 772596 of 1088420 (seed 1), 748581 of
1042430 (seed 3), 1457162 of 2010429 (witness).  Not modelled: least area, labels.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

universe v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10ExtremalWrap GFaceChoose
open scoped Classical

/-- **Residual states have a clean lobe** (hypothesis; true in all models, see the module
docstring).  At a reached state with `g ≥ 0` and a repeated vertex, having no negative lobe and
no two-lobe split, some simple lobe is clean. -/
def gfaceWindEight_Statement : Prop :=
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
        ∃ p A q : List M.Dart, c = p ++ A ++ q ∧
          ((IsSimpleClosedWalk M A ∧ gfaceWindEight_Clean M A (p ++ q)) ∨
            (IsSimpleClosedWalk M (q ++ p) ∧ gfaceWindEight_Clean M (q ++ p) A))

/-- **The residual of `PosStep` from clean lobes**: excise the clean lobe
(`gfaceWindEight_step`). -/
theorem gfaceWindEight_seven (h : gfaceWindEight_Statement.{v}) :
    gfaceWindSeven_Statement.{v} := by
  intro M hM C F o hC hS hch hbal ho c g hr hpos hnd h1 h2 h3
  obtain ⟨p, A, q, hseg, hcl⟩ := h M hM C F o hC hS hch hbal ho c g hr hpos hnd h1 h2 h3
  have hinv : gfaceWind_Inv M C o c g :=
    gfaceWindSix_inv_rt (s := (C, gfaceWind_ind F)) (t := (c, g)) hM hC hr
      (gfaceWind_inv_start hS hch ho)
  exact gfaceWindEight_step hS hinv hpos hseg hcl

/-- **`PosStep` from clean lobes**, through `gfaceWindSeven_posStep`. -/
theorem gfaceWindEight_posStep (h : gfaceWindEight_Statement.{v}) :
    gfaceWindSix_PosStep.{v} :=
  gfaceWindSeven_posStep (gfaceWindEight_seven h)

/-- **A lobe** `W` of `c` with rest `R`: an inner simple stretch `A` of `c = p ++ A ++ q` with
rest `p ++ q`, or a wrapping simple stretch `q ++ p` with rest `A`. -/
def gfaceWindEight_Lobe (M : CombMap.{v}) (c W R : List M.Dart) : Prop :=
  ∃ p A q : List M.Dart, c = p ++ A ++ q ∧
    ((IsSimpleClosedWalk M A ∧ W = A ∧ R = p ++ q) ∨
      (IsSimpleClosedWalk M (q ++ p) ∧ W = q ++ p ∧ R = A))

/-- **A reached state with a repeated vertex has a lobe** (`gfaceWindFive_lobe`). -/
theorem gfaceWindEight_lobe {M : CombMap.{v}} (hM : M.IsPlanar) {C : List M.Dart}
    {F : Finset M.Face} {o : M.Face} (hC : C.Nodup)
    (hS : ∀ d, Surgery.MapCollapse.IsBoundaryDart M F d ↔ d ∈ C)
    (hch : C.IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e) (ho : o ∉ F)
    {c : List M.Dart} {g : M.Face → ℤ}
    (hr : Relation.ReflTransGen (gfaceWind_Step M o) (C, gfaceWind_ind F) (c, g))
    (hnd : ¬ (c.map M.vertexOf).Nodup) :
    ∃ W R : List M.Dart, gfaceWindEight_Lobe M c W R := by
  have hinv : gfaceWind_Inv M C o c g :=
    gfaceWindSix_inv_rt (s := (C, gfaceWind_ind F)) (t := (c, g)) hM hC hr
      (gfaceWind_inv_start hS hch ho)
  obtain ⟨hfil, hchc, -, -⟩ := hinv
  have hsub : ∀ x ∈ c, x ∈ C := by
    intro x hx
    have hx' : x ∈ C.filter (gfaceWind_mem c) := by
      rw [hfil]
      exact hx
    exact (List.mem_filter.mp hx').1
  have hal : ∀ x ∈ c, M.alpha x ∉ c := fun x hx hax =>
    ((hS x).mpr (hsub x hx)).2 ((hS _).mpr (hsub _ hax)).1
  obtain ⟨p, A, q, hseg, hA⟩ := gfaceWindFive_lobe hchc hal hnd
  exact ⟨A, p ++ q, p, A, q, hseg, Or.inl ⟨hA, rfl, rfl⟩⟩

/-- **Descent to a clean lobe**: if every non-clean lobe of `c` has a lobe of `c` whose side has
strictly fewer faces, then from any lobe one reaches a clean lobe (strong induction on the
number of side faces). -/
theorem gfaceWindEight_descent {M : CombMap.{v}} {c : List M.Dart}
    (hdesc : ∀ W R : List M.Dart, gfaceWindEight_Lobe M c W R →
      ¬ gfaceWindEight_Clean M W R → ∃ W' R' : List M.Dart, gfaceWindEight_Lobe M c W' R' ∧
        (SimpleClosedWalkSides.sideFaces M W').card <
          (SimpleClosedWalkSides.sideFaces M W).card)
    {W R : List M.Dart} (h0 : gfaceWindEight_Lobe M c W R) :
    ∃ p A q : List M.Dart, c = p ++ A ++ q ∧
      ((IsSimpleClosedWalk M A ∧ gfaceWindEight_Clean M A (p ++ q)) ∨
        (IsSimpleClosedWalk M (q ++ p) ∧ gfaceWindEight_Clean M (q ++ p) A)) := by
  suffices key : ∀ n : ℕ, ∀ W₁ R₁ : List M.Dart,
      (SimpleClosedWalkSides.sideFaces M W₁).card = n → gfaceWindEight_Lobe M c W₁ R₁ →
        ∃ W' R' : List M.Dart, gfaceWindEight_Lobe M c W' R' ∧ gfaceWindEight_Clean M W' R' by
    obtain ⟨W', R', ⟨p, A, q, hseg, hl⟩, hc⟩ := key _ W R rfl h0
    refine ⟨p, A, q, hseg, ?_⟩
    rcases hl with ⟨hA, rfl, rfl⟩ | ⟨hB, rfl, rfl⟩
    · exact Or.inl ⟨hA, hc⟩
    · exact Or.inr ⟨hB, hc⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro W₁ R₁ hn hl
    by_cases hc : gfaceWindEight_Clean M W₁ R₁
    · exact ⟨W₁, R₁, hl, hc⟩
    · obtain ⟨W', R', hl', hlt⟩ := hdesc W₁ R₁ hl hc
      exact ih _ (hlt.trans_eq hn) W' R' rfl hl'

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindEight_Statement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindEight_seven
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindEight_posStep
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindEight_Lobe
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindEight_lobe
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindEight_descent
