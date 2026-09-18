import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.GFaceWindChord
import GroupApproximation.Meta.AxiomGuard

/-!
# Winding choice of `F'`: clean lobes from the minimal inside chord

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-75.

`gfaceWindEleven_Statement` and `gfaceWindTen_Statement` are false (`GFaceWindChord.lean`), so
`gfaceWindEleven_ten` and `gfaceWindTen_eight` reduce `gfaceWindEight_Statement` to false
statements. This file replaces them with a reduction through a true residual.

`gfaceWindChord_Statement` assumes the hypotheses of `gfaceWindEight_Statement`, and also
that **no** lobe of `c` is clean. From a lobe `W` whose side has the fewest faces among all
lobes, together with the chord configuration of `W`, it derives `False`.

`gfaceWindChord_eight` proves Eight from it:
* `Nat.find` picks a lobe `W` with the fewest side faces;
* `gfaceWindChord_split` either gives an inner lobe `W'` of `W` or the chord configuration;
* an inner lobe has strictly fewer side faces (`gfaceWindTen_card_lt`), against minimality.

## Strength (LOUD)

* **As a proposition, `gfaceWindChord_Statement` is EQUIVALENT to `gfaceWindEight_Statement`**
  (`gfaceWindChord_eight`, `gfaceWindChord_of_eight`). This is unavoidable here: Ten and Eleven,
  the stronger residuals, are false, and Chord's own hypotheses force a clean lobe to be absent.
* It is **strictly smaller in proof content** than Eight. Three things are discharged here:
  lobe existence, the inner-lobe cases of `gfaceWindChord_split`, and the planar side-card
  drop. Only the chord case at a minimal lobe with all lobes non-clean remains.
* It is **logically weaker than the false `gfaceWindEleven_Statement`**. There is no `_of_`
  reduction to Eleven, because Eleven is false. Chord is not stronger than Eight, and it
  cannot be false while Eight is true.

## Remaining gap

Suppose every lobe is non-clean, `W` is side-card-minimal, and `c` rotates to `W ++ T` with a
simple inside chord of `T` between distinct vertices of `W`. The chord splits the disc of `W`.
A contradiction must come from the walk's shape. The two arcs of `T` around the chord leave and
re-enter `W`, and they must contain a lobe that is clean or has a smaller side. The
counterexamples in `GFaceWindChord.lean` show both ways this can happen, through the loops `L`
and `L'` on `X` and `Y`: in the base run those lobes are clean with a smaller side, and in the
`big` run they are clean with a larger side. The statement needs a lemma finding a lobe on the
arcs `X`/`Y` whose face class avoids its rest. This is a global Jordan-type property, and the
corpus does not have it.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

universe v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10ExtremalWrap GFaceChoose
open scoped Classical

/-- **No inside chord at a side-minimal lobe when every lobe is non-clean.** It takes the
hypotheses of `gfaceWindEight_Statement`, no clean lobe, a lobe `W` with the fewest side faces,
and a rotation `W ++ T` of `c` in chord configuration, and concludes `False`. -/
def gfaceWindChord_Statement : Prop :=
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
        gfaceWindChord_Config M W T → False

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindChord_Statement

/-- **Clean lobes from the minimal inside chord**: take a lobe with the fewest side faces. An
inner lobe of it would have fewer (`gfaceWindTen_card_lt`), so `gfaceWindChord_split` leaves
the chord configuration. -/
theorem gfaceWindChord_eight (h : gfaceWindChord_Statement.{v}) :
    gfaceWindEight_Statement.{v} := by
  intro M hM C F o hC hS hch hbal ho c g hr hpos hnd h1 h2 h3
  by_contra hno
  have hall : ∀ W R : List M.Dart, gfaceWindEight_Lobe M c W R →
      ¬ gfaceWindEight_Clean M W R := by
    rintro W R ⟨p, A, q, hseg, ⟨hA, hW, hR⟩ | ⟨hB, hW, hR⟩⟩ hcl
    · rw [hW, hR] at hcl
      exact hno ⟨p, A, q, hseg, Or.inl ⟨hA, hcl⟩⟩
    · rw [hW, hR] at hcl
      exact hno ⟨p, A, q, hseg, Or.inr ⟨hB, hcl⟩⟩
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
  rcases gfaceWindChord_split hM hC hS hch hbal ho hr hl (hall W R hl) with
    ⟨W', R', hl', hin, x, hxW', hxW⟩ | ⟨X₁, X₂, T, hc, hZ, hRT, hcfg⟩
  · exact absurd (hmin W' R' hl') (not_le.mpr (gfaceWindTen_card_lt hM
      (gfaceWindTen_lobe_simple hl) (gfaceWindTen_lobe_simple hl') hin
      (gfaceWindTen_lobe_base h1 h2 hl) (gfaceWindTen_lobe_base h1 h2 hl') hxW' hxW))
  · exact h M hM C F o hC hS hch hbal ho c g hr hpos hnd h1 h2 h3 hall W R hl hmin
      X₁ X₂ T hc hZ hRT hcfg

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindChord_eight

/-- **The residual follows from `gfaceWindEight_Statement`**: a clean lobe contradicts the
no-clean-lobe hypothesis. With `gfaceWindChord_eight` the two are equivalent as propositions. -/
theorem gfaceWindChord_of_eight (h : gfaceWindEight_Statement.{v}) :
    gfaceWindChord_Statement.{v} := by
  intro M hM C F o hC hS hch hbal ho c g hr hpos hnd h1 h2 h3 hall _ _ _ _ _ _ _ _ _ _ _
  obtain ⟨p, A, q, hseg, ⟨hA, hcl⟩ | ⟨hB, hcl⟩⟩ :=
    h M hM C F o hC hS hch hbal ho c g hr hpos hnd h1 h2 h3
  · exact hall A (p ++ q) ⟨p, A, q, hseg, Or.inl ⟨hA, rfl, rfl⟩⟩ hcl
  · exact hall (q ++ p) A ⟨p, A, q, hseg, Or.inr ⟨hB, rfl, rfl⟩⟩ hcl

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindChord_of_eight

/-- **The positive step from the minimal inside chord**, through `gfaceWindEight_posStep`. -/
theorem gfaceWindChord_posStep (h : gfaceWindChord_Statement.{v}) :
    gfaceWindSix_PosStep.{v} :=
  gfaceWindEight_posStep (gfaceWindChord_eight h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindChord_posStep

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind
