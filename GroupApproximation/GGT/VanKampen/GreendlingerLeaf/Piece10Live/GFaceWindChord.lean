import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.GFaceWindEleven
import GroupApproximation.Meta.AxiomGuard

/-!
# Winding choice of `F'`: the inside-chord configuration of a lobe

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-75.

## `gfaceWindEleven_Statement` and `gfaceWindTen_Statement` are FALSE (LOUD)

Scratchpad `gl-p10-75/chord.py` builds a straight-line planar map with 10 faces (Euler
characteristic 2, connected) and a reached state `(c, g)` that violates both statements.

* `W` is the hexagon `v0 a w1 b w2 e`.
* The rest is `T = X ++ [w1 → w2] ++ Y`, where the single chord `w1 → w2` runs inside `W`.
* `X = v0 P1 P2 [P2 L1 L2 P2] P3 w1` carries a small loop `L` outside `W`.
* `Y = w2 Y1 Y2 [Y2 M1 M2 Y2] Y3 v0` carries a small loop `L'` outside `W`.
* The start walk is `C = W ++ N ++ T`, the boundary of `F`, where `F` is the faces with
  `g + wind_N = 1`. One `gfaceWind_Step` excises the negatively wound lobe
  `N = v0 n1 n2 w2 n3 w1 n4 n5 v0`, which gives `c = W ++ T` with `g ∈ {0, 1, 2}`.

The script checks every hypothesis literally:
* `C` is nodup, chained, closed and balanced, and it is exactly the boundary of `F`;
* `g ≥ 0`, and `c` is pinched;
* `h1`/`h2` (no lobe with `o` on its side) and `h3` (no two-lobe split) hold;
* the lobes of `c` are exactly `W`, `L` and `L'`, and `W` is not clean;
* all five extra hypotheses of Eleven hold.

The conclusion fails, because `L` and `L'` have their faces off the side of `W`. The
cyclically contiguous lobes of `c` are only `W`, `L` and `L'`. The chord closes up with an
arc of `W` only as the walk `chord ++ W-arc`, which is **not cyclically contiguous** in `c`, so
it is not a `gfaceWindEight_Lobe`. The preferred route `W' := chord ++ W-arc` therefore does
not meet the Lean lobe definition.

The `big` variant replaces `L` and `L'` by 4-cycles with hubs (16 faces). There `W` has 3
side faces while `L` and `L'` have 4 each. That also refutes the descent hypothesis of
`gfaceWindEight_descent`, and the claim that a side-card-minimal lobe is clean.
`gfaceWindEight_Statement` still holds in both runs, since `L` is clean. The earlier
`RESID = 0` (`gl-p10-70`) came from the small enumerated models.

## This file

`gfaceWindChord_split` runs the case analysis of `gfaceWindEleven_ten` without the false
residual. At a reached state, for a non-clean lobe `W` it gives one of two outcomes:
* an inner lobe `W'` (the conclusion of Ten); or
* the chord configuration `gfaceWindChord_Config`: a rotation `W ++ T` of `c` satisfying the
  five extra hypotheses of Eleven.
`GFaceWindChordEight.lean` uses it on a side-card-minimal lobe.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

universe v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10ExtremalWrap GFaceChoose
open scoped Classical

/-- **The inside-chord configuration** of `W` with rotation rest `T`: the five extra hypotheses
of `gfaceWindEleven_Statement`. These are an inside dart, and no inside stretch that repeats a
vertex, closes, or is an adjacent prefix or suffix. -/
def gfaceWindChord_Config (M : CombMap.{v}) (W T : List M.Dart) : Prop :=
  (∃ r ∈ T, M.faceOf r ∈ SimpleClosedWalkSides.sideFaces M W) ∧
  (∀ X Q Y : List M.Dart, T = X ++ Q ++ Y →
    (∀ x ∈ Q, M.faceOf x ∈ SimpleClosedWalkSides.sideFaces M W) →
    (Q.map M.vertexOf).Nodup) ∧
  (∀ (X Q Y : List M.Dart) (hQ : Q ≠ []), T = X ++ Q ++ Y →
    (∀ x ∈ Q, M.faceOf x ∈ SimpleClosedWalkSides.sideFaces M W) →
    M.vertexOf (M.alpha (Q.getLast hQ)) ≠ M.vertexOf (Q.head hQ)) ∧
  (∀ (Q Y : List M.Dart) (hQ : Q ≠ []), T = Q ++ Y →
    (∀ x ∈ Q, M.faceOf x ∈ SimpleClosedWalkSides.sideFaces M W) →
    (∀ x ∈ Q.tail, M.vertexOf x ∉ W.map M.vertexOf) →
    M.vertexOf (M.alpha (Q.getLast hQ)) ∉ W.map M.vertexOf) ∧
  (∀ (X Q : List M.Dart) (hQ : Q ≠ []), T = X ++ Q →
    (∀ x ∈ Q, M.faceOf x ∈ SimpleClosedWalkSides.sideFaces M W) →
    (∀ x ∈ Q.tail, M.vertexOf x ∉ W.map M.vertexOf) →
    M.vertexOf (Q.head hQ) ∉ W.map M.vertexOf)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindChord_Config

/-- **Inner lobe or inside chord**: at a reached state, a non-clean lobe `W` either has an inner
lobe `W'`, or `c` rotates to `W ++ T` with `T` carrying the rest and in chord configuration. -/
theorem gfaceWindChord_split {M : CombMap.{v}} (hM : M.IsPlanar) {C : List M.Dart}
    {F : Finset M.Face} {o : M.Face} (hC : C.Nodup)
    (hS : ∀ d, Surgery.MapCollapse.IsBoundaryDart M F d ↔ d ∈ C)
    (hch : C.IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e)
    (hbal : gfaceWindSix_Bal M C) (ho : o ∉ F) {c : List M.Dart} {g : M.Face → ℤ}
    (hr : Relation.ReflTransGen (gfaceWind_Step M o) (C, gfaceWind_ind F) (c, g))
    {W R : List M.Dart} (hl : gfaceWindEight_Lobe M c W R)
    (hnc : ¬ gfaceWindEight_Clean M W R) :
    (∃ W' R' : List M.Dart, gfaceWindEight_Lobe M c W' R' ∧
      (∀ x ∈ W', M.faceOf x ∈ SimpleClosedWalkSides.sideFaces M W) ∧ ∃ x ∈ W', x ∉ W) ∨
    ∃ X₁ X₂ T : List M.Dart, c = X₁ ++ X₂ ∧ X₂ ++ X₁ = W ++ T ∧ (∀ x, x ∈ R ↔ x ∈ T) ∧
      gfaceWindChord_Config M W T := by
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
  have hbc : gfaceWindSix_Bal M c :=
    gfaceWindSix_bal_reach (s := (C, gfaceWind_ind F)) (t := (c, g)) hr hbal
  have hcnd : c.Nodup := by
    have h0 := List.Nodup.filter (gfaceWind_mem c) hC
    rw [hinv.1] at h0
    exact h0
  obtain ⟨X₁, X₂, T, hc, hZ, hRT⟩ := gfaceWindEleven_rest hl
  have hperm : c.Perm (W ++ T) := by
    rw [hc, ← hZ]
    exact List.perm_append_comm
  have hZnd : (W ++ T).Nodup := hperm.nodup_iff.mp hcnd
  have halZ : ∀ x ∈ W ++ T, M.alpha x ∉ W ++ T := fun x hx hax =>
    hal x (hperm.mem_iff.mpr hx) (hperm.mem_iff.mpr hax)
  have hdis : ∀ x ∈ T, x ∉ W := fun x hxT hxW =>
    (List.nodup_append.mp hZnd).2.2 x hxW x hxT rfl
  have hW : IsSimpleClosedWalk M W := gfaceWindTen_lobe_simple hl
  have hchZ : (W ++ T).IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e := by
    rw [← hZ]
    exact gfaceWindEleven_cycChain (by rw [← hc]; exact hinv.2.1) (by rw [← hc]; exact hbc)
  obtain ⟨Y₁, Y₂, hY, hY2⟩ := gfaceWindEleven_rotate hZ
  have hc' : c = Y₁ ++ Y₂ := hc.trans hY
  have hchZ' : (T ++ W).IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e := by
    rw [← hY2]
    exact gfaceWindEleven_cycChain (by rw [← hc']; exact hinv.2.1) (by rw [← hc']; exact hbc)
  have hlobe : ∀ P L S : List M.Dart, W ++ T = P ++ L ++ S → IsSimpleClosedWalk M L →
      ∃ R : List M.Dart, gfaceWindEight_Lobe M c L R := fun P L S hs hL =>
    gfaceWindEleven_segLobe hc (hZ.trans hs) hL
  have hlobe' : ∀ P L S : List M.Dart, T ++ W = P ++ L ++ S → IsSimpleClosedWalk M L →
      ∃ R : List M.Dart, gfaceWindEight_Lobe M c L R := fun P L S hs hL =>
    gfaceWindEleven_segLobe hc' (hY2.trans hs) hL
  have hWR : ∀ x ∈ W, M.alpha x ∉ R := fun x hx hax =>
    halZ x (List.mem_append_left T hx) (List.mem_append_right W ((hRT _).mp hax))
  have hin : ∃ r ∈ T, M.faceOf r ∈ SimpleClosedWalkSides.sideFaces M W := by
    obtain ⟨r, hrR, hrf⟩ := gfaceWindEleven_inside hM hW hWR hnc
    exact ⟨r, (hRT r).mp hrR, hrf⟩
  by_cases hgoal : ∃ W' R' : List M.Dart, gfaceWindEight_Lobe M c W' R' ∧
      (∀ x ∈ W', M.faceOf x ∈ SimpleClosedWalkSides.sideFaces M W) ∧ ∃ x ∈ W', x ∉ W
  · exact Or.inl hgoal
  have hE1 : ∀ X Q Y : List M.Dart, T = X ++ Q ++ Y →
      (∀ x ∈ Q, M.faceOf x ∈ SimpleClosedWalkSides.sideFaces M W) →
      (Q.map M.vertexOf).Nodup := by
    intro X Q Y hT hQ
    by_contra hrep
    exact hgoal (gfaceWindEleven_e1 hchZ halZ hdis hlobe hT hQ hrep)
  have hE2 : ∀ (X Q Y : List M.Dart) (hQ : Q ≠ []), T = X ++ Q ++ Y →
      (∀ x ∈ Q, M.faceOf x ∈ SimpleClosedWalkSides.sideFaces M W) →
      M.vertexOf (M.alpha (Q.getLast hQ)) ≠ M.vertexOf (Q.head hQ) := by
    intro X Q Y hQ0 hT hQ hcl
    exact hgoal (gfaceWindEleven_e2 hchZ halZ hdis hlobe hT hQ0 hQ (hE1 X Q Y hT hQ) hcl)
  have hST : ∀ (Q Y : List M.Dart) (hQ : Q ≠ []), T = Q ++ Y →
      (∀ x ∈ Q, M.faceOf x ∈ SimpleClosedWalkSides.sideFaces M W) →
      (∀ x ∈ Q.tail, M.vertexOf x ∉ W.map M.vertexOf) →
      M.vertexOf (M.alpha (Q.getLast hQ)) ∉ W.map M.vertexOf := by
    intro Q Y hQ0 hT hQ hint hend
    have hT' : T = [] ++ Q ++ Y := by rw [hT, List.nil_append]
    exact hgoal (gfaceWindEleven_adjStart hW hchZ halZ hdis hlobe hT hQ0 hQ
      (hE1 [] Q Y hT' hQ) (hE2 [] Q Y hQ0 hT' hQ) hint hend)
  have hEN : ∀ (X Q : List M.Dart) (hQ : Q ≠ []), T = X ++ Q →
      (∀ x ∈ Q, M.faceOf x ∈ SimpleClosedWalkSides.sideFaces M W) →
      (∀ x ∈ Q.tail, M.vertexOf x ∉ W.map M.vertexOf) →
      M.vertexOf (Q.head hQ) ∉ W.map M.vertexOf := by
    intro X Q hQ0 hT hQ hint hst
    have hT' : T = X ++ Q ++ [] := by rw [hT, List.append_nil]
    exact hgoal (gfaceWindEleven_adjEnd hW hchZ' halZ hdis hlobe' hT hQ0 hQ
      (hE1 X Q [] hT' hQ) (hE2 X Q [] hQ0 hT' hQ) hint hst)
  exact Or.inr ⟨X₁, X₂, T, hc, hZ, hRT, hin, hE1, hE2, hST, hEN⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindChord_split

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind
