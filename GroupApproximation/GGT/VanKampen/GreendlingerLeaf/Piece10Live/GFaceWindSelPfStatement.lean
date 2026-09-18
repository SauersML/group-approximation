import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.GFaceWindSelPf
import GroupApproximation.Meta.AxiomGuard

/-!
# Winding choice of `F'`: the minimal inside chord has no sink region

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-80.

## Target and route

The target is `gfaceWindSel_Statement` (`Piece10Live/GFaceWindSel`). At a reached state
`(c, g)`, with no clean lobe, take a lobe `W` with the fewest side faces, in chord
configuration `c ~ W ++ T`. The claim is `g ≥ 1` on `S = sideFaces M W`.

`GFaceWindSelPf.lean` removes `g` from the claim:
* `g ≥ 1` on the face of every dart of `c`, in particular just inside `W`;
* the zero set of `g` on `S` is a **sink region** `gfaceWindSelPf_Sink M S c K`. That is a
  face set `K ⊆ S`, with no dart of `c` on it, such that every boundary dart `e` of `K` has
  `alpha e ∈ c`.

So the only step that needs new content is the purely planar walk fact
`gfaceWindSelPf_Statement`: under Sel's hypotheses, **every sink region of `c` in `S` is
empty**. Proved here:
* `gfaceWindSelPf_sel_of_statement`: it implies Sel;
* `gfaceWindSelPf_seven_of_statement` and `gfaceWindSelPf_posStep_of_statement`: it implies
  `gfaceWindSeven_Statement` and `gfaceWindSix_PosStep`.

`gfaceWindSelPf_sink_empty_of_reach` gives a constructive way to discharge it. It suffices
that every face of `S` is reachable from the face of a dart of `c`, by steps across darts
`e` from `faceOf (alpha e)` to `faceOf e` with `alpha e ∉ c`.

## Strength (LOUD)

`gfaceWindSelPf_Statement` is **NOT logically weaker** than `gfaceWindSel_Statement`: it
implies it. As a statement about an arbitrary `g`, it is stronger. A sink region `K` forces
`g` to be constant on each piece of `K` and to drop by `1` into `K`. It does not force
`g = 0` there, so Sel alone does not exclude a sink region with `g ≥ 1`.

It is **strictly smaller in proof content**. The coboundary bookkeeping, the positivity just
inside `W`, and the use of `g ≥ 0` are all discharged. What is left makes no mention of `g`,
`o`, or the winding function; it is about the walk `c`, the lobe `W`, and faces of the side of
`W` only. Earlier lanes (gl-p10-77) recorded that the remaining chord fact "concerns `g`, not
pure walk geometry". This file shows that it reduces to pure walk geometry.

It is **not an equivalent restatement**: Sel is exactly "the zero set is empty", while this
statement excludes every sink region.

## Truth check

Scratchpad `gl-p10-80/res.py` reuses the gl-p10-77 harness (`sel.py`, `spiral.py`) and tests
every lobe of minimum side card at every residual state (g ≥ 0, pinched, h1, h2, h3). This is
a superset of Sel's hypotheses, since clean lobes and the chord configuration are not filtered.
It tests:
* `R2`: every face of `S` is reachable from a face just inside `W` by the monotone steps
  above. `R2` implies the reach hypothesis of `gfaceWindSelPf_sink_empty_of_reach`, and so
  implies this statement.
* `R1`: the same with steps only across edges off `c`, which is stronger.
* Sel itself.

See the table below; the failure counts are all zero.

| run (mode, seed, secs) | residual states | min lobes | no-clean lobes | Sel/R1/R2 fail |
|---|---|---|---|---|
| walk 5 60 | 191457 | 337985 | 43 | 0 / 0 / 0 |
| reach rand 9 60 | 121887 | 278022 | 0 | 0 / 0 / 0 |
| walk 11 250 | 179897 | 316964 | 29 | 0 / 0 / 0 |
| walk 12 250 | 182143 | 322473 | 31 | 0 / 0 / 0 |
| reach wit 15 250 | 121467 | 230429 | 0 | 0 / 0 / 0 |
| reach rand 16 250 | 125854 | 267792 | 0 | 0 / 0 / 0 |
| spiral 0 7 250 (k ≤ 6) | 110099 | 233440 | 0 | 0 / 0 / 0 |
| spiral 0 13 250 (k ≤ 6) | 122325 | 235738 | 0 | 0 / 0 / 0 |
| spiral 1 8 250 (k ≤ 4) | 80428 | 139011 | 4 | 0 / 0 / 0 |
| spiral 1 14 250 (k ≤ 4) | 120292 | 196038 | 13 | 0 / 0 / 0 |

Total: 1355849 residual states and 2557892 minimal lobes, 120 of them in the exact no-clean
regime; no failures. Caveat: only 120 lobes satisfy the exact `hall` hypothesis. The chord
configuration is not filtered, so the positive evidence in the precise regime is thin.

## Remaining gap

`gfaceWindSelPf_Statement`. It is a Jordan-type fact. Suppose `T` enters the disc `S` of a
side-minimal lobe only through chords, as in `gfaceWindChord_Config`. Then `T` cannot enclose
a region of `S` clockwise, with `c` running around it on its right and never entering it.
Such a region would be bounded by pieces of several chords of `T` that meet at interior
vertices. The expected proof extracts from those pieces a lobe of `c` with a smaller side,
against `gfaceWindTen_card_lt`, or a clean lobe. The corpus has no lemma that turns a family
of chords meeting inside `S` into a contiguous lobe of `c`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

universe v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10ExtremalWrap GFaceChoose
open scoped Classical

/-- **A monotone face step for `c`**: cross a dart `e` from `faceOf (alpha e)` to `faceOf e`,
where `alpha e ∉ c`. A face function cobounded by `c` does not decrease along it. -/
def gfaceWindSelPf_Up (M : CombMap.{v}) (c : List M.Dart) (a b : M.Face) : Prop :=
  ∃ e : M.Dart, M.faceOf (M.alpha e) = a ∧ M.faceOf e = b ∧ M.alpha e ∉ c

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSelPf_Up

/-- **Monotone steps never enter a sink region.** -/
theorem gfaceWindSelPf_not_mem_of_reach {M : CombMap.{v}} {S K : Finset M.Face}
    {c : List M.Dart} (hK : gfaceWindSelPf_Sink M S c K) {a b : M.Face}
    (hab : Relation.ReflTransGen (gfaceWindSelPf_Up M c) a b) (ha : a ∉ K) : b ∉ K := by
  induction hab with
  | refl => exact ha
  | tail _ hst ih =>
      obtain ⟨e, he1, he2, he3⟩ := hst
      intro hb
      rw [← he2] at hb
      exact he3 (hK.2.2 e hb (by rw [he1]; exact ih))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSelPf_not_mem_of_reach

/-- **No sink region from monotone reachability**: if every face of `S` is reachable by
monotone steps from the face of a dart of `c`, then every sink region of `c` in `S` is empty. -/
theorem gfaceWindSelPf_sink_empty_of_reach {M : CombMap.{v}} {S K : Finset M.Face}
    {c : List M.Dart}
    (hr : ∀ f ∈ S, ∃ d ∈ c, Relation.ReflTransGen (gfaceWindSelPf_Up M c) (M.faceOf d) f)
    (hK : gfaceWindSelPf_Sink M S c K) : K = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun f hf => ?_
  obtain ⟨d, hd, hdf⟩ := hr f (hK.1 hf)
  exact gfaceWindSelPf_not_mem_of_reach hK hdf (fun h => hK.2.1 d h hd) hf

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSelPf_sink_empty_of_reach

/-- **The residual: no sink region at the minimal inside chord**. The hypotheses are those of
`gfaceWindSel_Statement` verbatim. The conclusion says every sink region of `c` in the side of
`W` is empty; it does not mention `g`. -/
def gfaceWindSelPf_Statement : Prop :=
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
        gfaceWindChord_Config M W T →
        ∀ K : Finset M.Face, gfaceWindSelPf_Sink M (SimpleClosedWalkSides.sideFaces M W) c K →
          K = ∅

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSelPf_Statement

/-- **The residual implies Sel**. The boundary darts of `S = sideFaces M W` are the darts of
`W`, which lie on `c`. So the zero set of `g` on `S` is a sink region
(`gfaceWindSelPf_zero_sink`), and it is empty by the residual. -/
theorem gfaceWindSelPf_sel_of_statement (h : gfaceWindSelPf_Statement.{v}) :
    gfaceWindSel_Statement.{v} := by
  intro M hM C F o hC hS hch hbal ho c g hr hpos hnd h1 h2 h3 hall W R hl hmin X₁ X₂ T hc hZ
    hRT hcfg
  have hinv : gfaceWind_Inv M C o c g :=
    gfaceWindSix_inv_rt (s := (C, gfaceWind_ind F)) (t := (c, g)) hM hC hr
      (gfaceWind_inv_start hS hch ho)
  have hsub : ∀ x ∈ c, x ∈ C := by
    intro x hx
    have hx' : x ∈ C.filter (gfaceWind_mem c) := by
      rw [hinv.1]
      exact hx
    exact (List.mem_filter.mp hx').1
  have hal : ∀ x ∈ c, M.alpha x ∉ c := fun x hx hax =>
    ((hS x).mpr (hsub x hx)).2 ((hS _).mpr (hsub _ hax)).1
  have hW : IsSimpleClosedWalk M W := gfaceWindTen_lobe_simple hl
  have hWc : ∀ x ∈ W, x ∈ c := by
    intro x hx
    have hx' : x ∈ X₂ ++ X₁ := by
      rw [hZ]
      exact List.mem_append.mpr (Or.inl hx)
    rw [hc]
    exact List.mem_append.mpr (List.mem_append.mp hx').symm
  have hbd : ∀ e : M.Dart, M.faceOf e ∈ SimpleClosedWalkSides.sideFaces M W →
      M.faceOf (M.alpha e) ∉ SimpleClosedWalkSides.sideFaces M W → e ∈ c :=
    fun e he hae => hWc e ((hW.isBoundaryDart_sideFaces_iff hM e).mp (And.intro he hae))
  exact gfaceWindSelPf_pos_of_sink hinv.2.2.1 hal hpos hbd
    (h M hM C F o hC hS hch hbal ho c g hr hpos hnd h1 h2 h3 hall W R hl hmin X₁ X₂ T hc hZ
      hRT hcfg)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSelPf_sel_of_statement

/-- **The residual implies `gfaceWindSeven_Statement`** (through `gfaceWindSel_seven`). -/
theorem gfaceWindSelPf_seven_of_statement (h : gfaceWindSelPf_Statement.{v}) :
    gfaceWindSeven_Statement.{v} :=
  gfaceWindSel_seven (gfaceWindSelPf_sel_of_statement h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSelPf_seven_of_statement

/-- **The residual implies `gfaceWindSix_PosStep`** (through `gfaceWindSel_posStep`). -/
theorem gfaceWindSelPf_posStep_of_statement (h : gfaceWindSelPf_Statement.{v}) :
    gfaceWindSix_PosStep.{v} :=
  gfaceWindSel_posStep (gfaceWindSelPf_sel_of_statement h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSelPf_posStep_of_statement

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind
