import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.GFaceWindChordEight
import GroupApproximation.Meta.AxiomGuard

/-!
# Winding choice of `F'`: positive (not clean) lobes from the minimal side

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-77.

## LOUD: `gfaceWindEight_Statement` is FALSE (hence so is `gfaceWindChord_Statement`)

Counterexample (scratchpad `gl-p10-77/verify.py`, an independent literal re-implementation of
`IsSimpleClosedWalk`, `walkKeep`, `FaceClassStep`/`EqvGen`, `sideFaces`, `gfaceWind_Step`,
`IsBoundaryDart`, `gfaceWindSix_Bal`, `gfaceWindEight_Clean`; found by `spiral.py`).
Darts `0..17`, `alpha d = d xor 1`, and
`sigma = [3,4,1,16,12,8,11,17,14,0,15,10,13,5,7,9,6,2]` (so `facePerm d = sigma (alpha d)`).
It is planar: connected, with 2 vertices, 9 edges and 9 faces. The faces, as dart sets, are
`f0 {0,4,8}`, `f1 {1,3}`, `f2 {2,16}`, `f3 {5,12}`, `f4 {6,17}`, `f5 {7,11,15}`, `f6 {9,14}`,
`f7 {10}`, `f8 {13}`.
Take `C = [1,3,5,14,6,12,17,9]`, `F = {f1,f3,f4,f6}` and `o = f8`. Then `C` is nodup, a
chain, balanced, and exactly the boundary of `F`, with `o ∉ F`.
Two steps follow, each excising a negative lobe (there is no sign restriction):
* excise `[5]`, a loop whose side contains `o`;
* excise `[3,14]`.

They reach `c = [1,6,12,17,9]` with `g = (1,2,2,1,3,2,2,2,0)`. There `g ≥ 0`, `c` repeats a
vertex, and `h1`, `h2`, `h3` all hold. The lobes are `[1,6]`, `[17,9]`, the wrap `[9,1]` and
the loop `[12]`, and **none of them is clean**. So no selection rule can return a clean lobe,
and rules 1-4 of the lane (inclusion-minimal side, lexicographic minimum of (side card, `|W|`),
innermost, side disjoint from other lobes) all fail there.
The pure planar-walk version is false as well (`sel.py walk`: 6, 11, 27 and 20 failing states
across seeds).

`gfaceWindSeven_Statement` (`PosStep`) survives. At the counterexample every lobe has
`g ≥ 1` on its side.

## Route (the corrected residual)

`gfaceWindSel_Statement` keeps Chord's hypotheses:
* the Eight hypotheses;
* **no** lobe of `c` is clean;
* `W` is a lobe with the fewest side faces;
* the chord configuration of `W`.

It concludes `g ≥ 1` on `sideFaces M W` (**positivity, not cleanness**).
`gfaceWindSel_seven` proves `gfaceWindSeven_Statement` from it:
* (a) if some lobe is clean, `gfaceWindEight_step` applies. Otherwise `Nat.find` picks a lobe
  `W` with the fewest side faces, as in `gfaceWindChord_eight`.
* (b) `gfaceWindChord_split` is applied to `W`.
* (c) The inner-lobe branch contradicts minimality (`gfaceWindTen_card_lt`). The chord branch
  gets positivity from the residual, and `gfaceWindSel_step` excises `W` keeping `g ≥ 0`,
  since `o ∉ sideFaces M W` (`gfaceWindTen_lobe_base`).

## Truth check

Scratchpad `gl-p10-77/sel2.py`, rule `R9_mincard`: every lobe whose side has the minimum number
of faces has `g ≥ 1` on its side. `POSALLFAIL = 0` in every run:

| run | residual states | states with no clean lobe |
|---|---|---|
| reached, random seeds 9 and 16 | 61374 and 138051 | — |
| reached, witness seed 15 | 142084 | — |
| reached, refined counterexample maps, seeds 7 8 13 14 | 55990, 80428, 306820, 120292 | 4, 9 |
| pure walks with `g ≥ 0`, seeds 5, 11, 12 | 89454, 204453, 204620 | 11, 27, 20 |
| the two maps of gl-p10-75 | — | — |

`SEVENFAIL = 0` throughout. At every state with no clean lobe, `gfaceWindSel_Statement` is
non-vacuous. Lexicographic minimum of (side card, `|W|`) and minimum `mu` also pass. The
inclusion-minimal side rule fails: `POSALLFAIL` is 10 and 29.

## Strength (LOUD)

* `gfaceWindEight_Statement → gfaceWindSel_Statement` (`gfaceWindSel_of_eight`, vacuously,
  since Eight gives a clean lobe). The converse fails: Eight is false while Sel holds in every
  model above. So Sel is **STRICTLY WEAKER** than Eight, and it is not an equivalent
  restatement.
* `gfaceWindSel_Statement → gfaceWindSeven_Statement` (`gfaceWindSel_seven`). Sel is stronger
  in content than Seven: it names which lobe is positive.
* **No `gfaceWindSel_eight_of_chord`**. Eight is false, so no chord lemma can prove it.
  `gfaceWindSel_ChordStatement` is not introduced: the remaining chord fact concerns `g`, not
  pure walk geometry.

## Remaining gap

`gfaceWindSel_Statement` itself. Take a side-card-minimal lobe `W` in chord configuration
`W ++ T`. The claim is that `g ≥ 1` on every face of its side, even though edges of `T` enter
that side.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

universe v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10ExtremalWrap GFaceChoose
open scoped Classical

/-- **Excising a positive lobe keeps `g ≥ 0`**: if the base face is off the side of a lobe `W`,
and `g ≥ 1` on that side, then removing `W` is a sign-keeping step. -/
theorem gfaceWindSel_step {M : CombMap.{v}} {o : M.Face} {c W R : List M.Dart}
    {g : M.Face → ℤ} (hl : gfaceWindEight_Lobe M c W R)
    (hoW : o ∉ SimpleClosedWalkSides.sideFaces M W) (hpos : ∀ f, 0 ≤ g f)
    (hside : ∀ f ∈ SimpleClosedWalkSides.sideFaces M W, 1 ≤ g f) :
    ∃ t : List M.Dart × (M.Face → ℤ), gfaceWind_Step M o (c, g) t ∧ ∀ f, 0 ≤ t.2 f := by
  have key : ∀ f, 0 ≤ g f - gfaceWind_wind M o W f := by
    intro f
    have h0 : gfaceWind_ind (SimpleClosedWalkSides.sideFaces M W) o = 0 :=
      gfaceWind_ind_neg hoW
    have h3 : gfaceWind_wind M o W f = gfaceWind_ind (SimpleClosedWalkSides.sideFaces M W) f -
        gfaceWind_ind (SimpleClosedWalkSides.sideFaces M W) o := rfl
    by_cases hf : f ∈ SimpleClosedWalkSides.sideFaces M W
    · linarith [gfaceWind_ind_pos hf, hside f hf]
    · linarith [gfaceWind_ind_neg hf, hpos f]
  obtain ⟨p, A, q, hseg, ⟨hA, hW, -⟩ | ⟨hB, hW, -⟩⟩ := hl
  · rw [hW] at key
    exact ⟨(p ++ q, fun f => g f - gfaceWind_wind M o A f),
      ⟨p, A, q, hseg, Or.inl ⟨hA, rfl, rfl⟩⟩, key⟩
  · rw [hW] at key
    exact ⟨(A, fun f => g f - gfaceWind_wind M o (q ++ p) f),
      ⟨p, A, q, hseg, Or.inr ⟨hB, rfl, rfl⟩⟩, key⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSel_step

/-- **Positivity at the minimal inside chord** (hypothesis; true in all models, see the module
docstring). It takes the hypotheses of `gfaceWindEight_Statement`, no clean lobe, a lobe `W`
with the fewest side faces, and a rotation `W ++ T` of `c` in chord configuration, and
concludes `g ≥ 1` on the side of `W`. -/
def gfaceWindSel_Statement : Prop :=
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
      (∀ W R : List M.Dart, gfaceWindEight_Lobe M c W R → ¬ gfaceWindEight_Clean M W R) →
      ∀ W R : List M.Dart, gfaceWindEight_Lobe M c W R →
      (∀ W' R' : List M.Dart, gfaceWindEight_Lobe M c W' R' →
        (SimpleClosedWalkSides.sideFaces M W).card ≤
          (SimpleClosedWalkSides.sideFaces M W').card) →
      ∀ X₁ X₂ T : List M.Dart, c = X₁ ++ X₂ → X₂ ++ X₁ = W ++ T → (∀ x, x ∈ R ↔ x ∈ T) →
        gfaceWindChord_Config M W T → ∀ f ∈ SimpleClosedWalkSides.sideFaces M W, 1 ≤ g f

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSel_Statement

/-- **The residual of `PosStep` from positivity at the minimal inside chord**. If some lobe is
clean, `gfaceWindEight_step` applies. Otherwise take a lobe `W` with the fewest side faces:
an inner lobe of `W` would have fewer (`gfaceWindTen_card_lt`), so `gfaceWindChord_split`
leaves the chord configuration, where the residual makes `W` positive (`gfaceWindSel_step`). -/
theorem gfaceWindSel_seven (h : gfaceWindSel_Statement.{v}) :
    gfaceWindSeven_Statement.{v} := by
  intro M hM C F o hC hS hch hbal ho c g hr hpos hnd h1 h2 h3
  have hinv : gfaceWind_Inv M C o c g :=
    gfaceWindSix_inv_rt (s := (C, gfaceWind_ind F)) (t := (c, g)) hM hC hr
      (gfaceWind_inv_start hS hch ho)
  by_cases hcl : ∃ p A q : List M.Dart, c = p ++ A ++ q ∧
      ((IsSimpleClosedWalk M A ∧ gfaceWindEight_Clean M A (p ++ q)) ∨
        (IsSimpleClosedWalk M (q ++ p) ∧ gfaceWindEight_Clean M (q ++ p) A))
  · obtain ⟨p, A, q, hseg, hcl'⟩ := hcl
    exact gfaceWindEight_step hS hinv hpos hseg hcl'
  have hall : ∀ W R : List M.Dart, gfaceWindEight_Lobe M c W R →
      ¬ gfaceWindEight_Clean M W R := by
    rintro W R ⟨p, A, q, hseg, ⟨hA, hW, hR⟩ | ⟨hB, hW, hR⟩⟩ hWR
    · rw [hW, hR] at hWR
      exact hcl ⟨p, A, q, hseg, Or.inl ⟨hA, hWR⟩⟩
    · rw [hW, hR] at hWR
      exact hcl ⟨p, A, q, hseg, Or.inr ⟨hB, hWR⟩⟩
  have hex : ∃ n : ℕ, ∃ W R : List M.Dart, gfaceWindEight_Lobe M c W R ∧
      (SimpleClosedWalkSides.sideFaces M W).card = n := by
    obtain ⟨W, R, hl⟩ := gfaceWindEight_lobe hM hC hS hch ho hr hnd
    exact ⟨_, W, R, hl, rfl⟩
  obtain ⟨W, R, hl, hn⟩ := Nat.find_spec hex
  have hmin : ∀ W' R' : List M.Dart, gfaceWindEight_Lobe M c W' R' →
      (SimpleClosedWalkSides.sideFaces M W).card ≤
        (SimpleClosedWalkSides.sideFaces M W').card := by
    intro W' R' hl'
    rw [hn]
    exact Nat.find_min' hex ⟨W', R', hl', rfl⟩
  have hoW : o ∉ SimpleClosedWalkSides.sideFaces M W := gfaceWindTen_lobe_base h1 h2 hl
  rcases gfaceWindChord_split hM hC hS hch hbal ho hr hl (hall W R hl) with
    ⟨W', R', hl', hin, x, hxW', hxW⟩ | ⟨X₁, X₂, T, hc, hZ, hRT, hcfg⟩
  · exact absurd (hmin W' R' hl') (not_le.mpr (gfaceWindTen_card_lt hM
      (gfaceWindTen_lobe_simple hl) (gfaceWindTen_lobe_simple hl') hin
      hoW (gfaceWindTen_lobe_base h1 h2 hl') hxW' hxW))
  · exact gfaceWindSel_step hl hoW hpos
      (h M hM C F o hC hS hch hbal ho c g hr hpos hnd h1 h2 h3 hall W R hl hmin
        X₁ X₂ T hc hZ hRT hcfg)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSel_seven

/-- **Eight implies the residual** (vacuously: Eight gives a clean lobe, against the
no-clean-lobe hypothesis). Eight is false (module docstring), so this only records that Sel
is weaker than Eight. -/
theorem gfaceWindSel_of_eight (h : gfaceWindEight_Statement.{v}) :
    gfaceWindSel_Statement.{v} := by
  intro M hM C F o hC hS hch hbal ho c g hr hpos hnd h1 h2 h3 hall _ _ _ _ _ _ _ _ _ _ _
  obtain ⟨p, A, q, hseg, ⟨hA, hcl⟩ | ⟨hB, hcl⟩⟩ :=
    h M hM C F o hC hS hch hbal ho c g hr hpos hnd h1 h2 h3
  · exact absurd hcl (hall A (p ++ q) ⟨p, A, q, hseg, Or.inl ⟨hA, rfl, rfl⟩⟩)
  · exact absurd hcl (hall (q ++ p) A ⟨p, A, q, hseg, Or.inr ⟨hB, rfl, rfl⟩⟩)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSel_of_eight

/-- **`PosStep` from positivity at the minimal inside chord**, through
`gfaceWindSeven_posStep`. -/
theorem gfaceWindSel_posStep (h : gfaceWindSel_Statement.{v}) :
    gfaceWindSix_PosStep.{v} :=
  gfaceWindSeven_posStep (gfaceWindSel_seven h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSel_posStep

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind
