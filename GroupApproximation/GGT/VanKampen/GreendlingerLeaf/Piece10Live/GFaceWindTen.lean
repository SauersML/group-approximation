import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.GFaceWindTenNest
import GroupApproximation.Meta.AxiomGuard

/-!
# Winding choice of `F'`: clean lobes from inner lobes

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-68.

`gfaceWindEight_Statement` asks for a clean lobe at every residual state. `gfaceWindEight_descent`
gives one if each non-clean lobe `W` has a lobe whose side has fewer faces. This file isolates
`gfaceWindTen_Statement`: each non-clean lobe `W` has a lobe `W'` with
* every dart's face on the side of `W`, and
* a dart off `W`.

It proves `gfaceWindTen_eight : gfaceWindTen_Statement → gfaceWindEight_Statement`. The strict
drop in side size comes from planar side nesting (`gfaceWindTen_card_lt`). Its base face `o` is
off the side of every lobe at a residual state (`gfaceWindTen_lobe_base`).

## Strength (LOUD)

`gfaceWindTen_Statement` is **logically STRONGER** than `gfaceWindEight_Statement`: it implies it
(`gfaceWindTen_eight`), and it is not implied formally, because it quantifies over *every*
non-clean lobe.

It is **strictly smaller in proof content**. The planar side comparison, that side inclusion is
strict and the side card drops, is discharged here (`gfaceWindTen_nest`, `gfaceWindTen_card_lt`).
Proving `gfaceWindEight_Statement` from side-minimal lobes needs that comparison plus exactly this
statement.

## Remaining gap

The gap is producing an inner lobe for a non-clean lobe `W`. Non-clean means an edge of the rest
`R` lies in the closed disc `D` bounded by `W`. The hard case is a simple chord of `R` inside `D`,
between distinct vertices of `W`. The closed stretch that it cuts off `c` must be shown to be a
simple closed lobe with its darts' faces in `D`. That is a Jordan-type chord statement, and the
corpus has no lemma for it.

The inner lobe cannot always be taken disjoint from `W`: the `T2` counts below miss 902 cases.

## Truth check

The check is scratchpad `gl-p10-68/ten.py`, reusing the enumerators of `gl-p10-65/eight.py`. It
ran three 240 s runs: `rand` seed 1, `wit` seed 2 and `rand` seed 3. They covered 1275976
residual states with 680087 non-clean lobes.

| Check | Holds | Out of |
| --- | --- | --- |
| `T1` (this statement) | 680087 | 680087 non-clean lobes |
| `T2` (inner lobe disjoint from `W`) | 679185 | 680087 non-clean lobes |
| Nesting lemma, as used here | 4748538 | 4748538 lobe pairs |

The residual states are those of `gfaceWindEight_Statement`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

universe v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10ExtremalWrap GFaceChoose
open scoped Classical

/-- **A lobe is a simple closed walk.** -/
theorem gfaceWindTen_lobe_simple {M : CombMap.{v}} {c W R : List M.Dart}
    (hl : gfaceWindEight_Lobe M c W R) : IsSimpleClosedWalk M W := by
  obtain ⟨p, A, q, -, ⟨hA, rfl, -⟩ | ⟨hB, rfl, -⟩⟩ := hl
  · exact hA
  · exact hB

/-- **The base face is off the side of every lobe** at a residual state. -/
theorem gfaceWindTen_lobe_base {M : CombMap.{v}} {c W R : List M.Dart} {o : M.Face}
    (h1 : ¬ ∃ p A q : List M.Dart, c = p ++ A ++ q ∧ IsSimpleClosedWalk M A ∧
      o ∈ SimpleClosedWalkSides.sideFaces M A)
    (h2 : ¬ ∃ p A q : List M.Dart, c = p ++ A ++ q ∧ IsSimpleClosedWalk M (q ++ p) ∧
      o ∈ SimpleClosedWalkSides.sideFaces M (q ++ p))
    (hl : gfaceWindEight_Lobe M c W R) : o ∉ SimpleClosedWalkSides.sideFaces M W := by
  intro hoW
  obtain ⟨p, A, q, hseg, ⟨hA, rfl, -⟩ | ⟨hB, rfl, -⟩⟩ := hl
  · exact h1 ⟨p, A, q, hseg, hA, hoW⟩
  · exact h2 ⟨p, A, q, hseg, hB, hoW⟩

/-- **Inner lobes of non-clean lobes at residual states**: the hypotheses of
`gfaceWindEight_Statement`, and each non-clean lobe `W` has a lobe `W'` whose darts have their
faces on the side of `W`, with a dart off `W`. -/
def gfaceWindTen_Statement : Prop :=
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
        ∀ W R : List M.Dart, gfaceWindEight_Lobe M c W R → ¬ gfaceWindEight_Clean M W R →
          ∃ W' R' : List M.Dart, gfaceWindEight_Lobe M c W' R' ∧
            (∀ x ∈ W', M.faceOf x ∈ SimpleClosedWalkSides.sideFaces M W) ∧
              ∃ x ∈ W', x ∉ W

/-- **Clean lobes from inner lobes**: planar side nesting turns inner lobes into the strict
descent of `gfaceWindEight_descent`. -/
theorem gfaceWindTen_eight (h : gfaceWindTen_Statement.{v}) :
    gfaceWindEight_Statement.{v} := by
  intro M hM C F o hC hS hch hbal ho c g hr hpos hnd h1 h2 h3
  obtain ⟨W, R, hl⟩ := gfaceWindEight_lobe hM hC hS hch ho hr hnd
  refine gfaceWindEight_descent ?_ hl
  intro W₁ R₁ hl₁ hnc
  obtain ⟨W', R', hl', hin, x, hxW', hxW₁⟩ :=
    h M hM C F o hC hS hch hbal ho c g hr hpos hnd h1 h2 h3 W₁ R₁ hl₁ hnc
  exact ⟨W', R', hl', gfaceWindTen_card_lt hM (gfaceWindTen_lobe_simple hl₁)
    (gfaceWindTen_lobe_simple hl') hin (gfaceWindTen_lobe_base h1 h2 hl₁)
    (gfaceWindTen_lobe_base h1 h2 hl') hxW' hxW₁⟩

/-- **`PosStep` from inner lobes**, through `gfaceWindEight_posStep`. -/
theorem gfaceWindTen_posStep (h : gfaceWindTen_Statement.{v}) : gfaceWindSix_PosStep.{v} :=
  gfaceWindEight_posStep (gfaceWindTen_eight h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindTen_lobe_simple
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindTen_lobe_base
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindTen_Statement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindTen_eight
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindTen_posStep
