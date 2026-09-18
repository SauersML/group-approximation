import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.GFaceWindEight
import GroupApproximation.GGT.VanKampen.SimpleClosedWalkSideFaces
import GroupApproximation.GGT.VanKampen.SimpleClosedWalkSidesDisjoint
import GroupApproximation.Meta.AxiomGuard

/-!
# Winding choice of `F'`: side nesting of simple closed walks in a planar map

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-68.

Let `W` and `L` be simple closed walks in a planar map, with a base face `o` off both sides.
If every dart of `L` has its face on the side of `W`, then the side of `L` lies in the side of
`W` (`gfaceWindTen_nest`), strictly if some dart of `L` is not on `W` (`gfaceWindTen_card_lt`).

Proof.
* `gfaceWindTen_class_step`, `gfaceWindTen_class_head`: the darts of a simple closed walk lie in
  one face class (cut along its edges): from `a` to the next dart `b` the vertex rotation from
  `alpha a` returns to the walk first at `b` (`walkMap_sigma_alpha`), and the darts it passes are
  crossed off the walk (`faceClass_run`).
* `gfaceWindTen_outside`: the side of the reversed walk `W' = W.reverse.map alpha` is the
  complement of the side of `W` (`sideFaces_boundaryCycle_eq` for `outerCycle`).
* `gfaceWindTen_transfer`: a face-class chain of `W'` inside the side of `W'` never crosses an
  edge of `L`, since both faces of an edge of `L` crossed there would be off the side of `W`, but
  each dart of `L` has its face on the side of `W`.
* `gfaceWindTen_nest`: a face `F` on the side of `L` but off the side of `W` is on the side of
  `W'`, as is `o`; one face class of `W'` joins them, and it is a face-class chain of `L`, so `o`
  is on the side of `L`: contradiction.
* `gfaceWindTen_card_lt`: equal sides have equal boundary darts
  (`isBoundaryDart_sideFaces_iff`), i.e. equal dart sets.

## Truth check

Scratchpad `gl-p10-68/ten.py`: at every residual state of `gfaceWindEight_Statement`, for all
pairs of lobes `W`, `L` with the faces of `L` on the side of `W`, the side of `L` lay in the side
of `W`, strictly when the dart sets differ (`NESTFAIL` and `NESTFAIL2` both 0).

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

universe v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides
open scoped Classical

/-- **Consecutive darts of a simple closed walk lie in one face class** of the map cut along the
walk. -/
theorem gfaceWindTen_class_step {M : CombMap.{v}} {w : List M.Dart}
    (hw : IsSimpleClosedWalk M w) {a b : M.Dart} (ha : a ∈ w) (hb : b ∈ w)
    (hab : M.vertexOf (M.alpha a) = M.vertexOf b) :
    Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M w)) a b := by
  obtain ⟨m, hm, hpm, havoid⟩ :=
    (walkMap_isRestriction M w).sigma_firstReturn ⟨M.alpha a, hw.alpha_keep ha⟩
  have hpm' : (M.sigma ^ m) (M.alpha a) = b :=
    hpm.trans (congrArg Subtype.val (hw.walkMap_sigma_alpha ha hb hab (hw.alpha_keep ha)))
  rw [← hpm']
  exact faceClass_run M (walkKeep M w) a m
    (fun k hk0 hkm hkeep => havoid k hk0 hkm ⟨⟨_, hkeep⟩, rfl⟩) m hm le_rfl

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindTen_class_step

/-- **All darts of a simple closed walk lie in the face class of its first dart.** -/
theorem gfaceWindTen_class_head {M : CombMap.{v}} {w : List M.Dart}
    (hw : IsSimpleClosedWalk M w) :
    ∀ x ∈ w, Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M w)) (w.head hw.ne_nil) x := by
  refine List.IsChain.induction
    (fun x => Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M w)) (w.head hw.ne_nil) x)
    w (List.IsChain.iff_mem.mp hw.chain) ?_ ?_
  · rintro x y ⟨hxw, hyw, hxy⟩ h
    exact .trans _ _ _ h (gfaceWindTen_class_step hw hxw hyw hxy)
  · intro _
    exact .refl _

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindTen_class_head

/-- **The side of the reversed walk is the other side.** -/
theorem gfaceWindTen_outside {M : CombMap.{v}} (hM : M.IsPlanar) {w : List M.Dart}
    (hw : IsSimpleClosedWalk M w) :
    sideFaces M (w.reverse.map M.alpha) = sideOutside M w := by
  have hf : M.faceOf (w.head hw.ne_nil) ∉ sideOutside M w := by
    rw [mem_sideOutside_iff, Classical.not_not]
    exact (mem_sideFaces_iff M w _).mpr ⟨_, List.head_mem hw.ne_nil, .refl _⟩
  exact sideFaces_boundaryCycle_eq (M.connected_of_planar hM) (hw.outerCycle hM) hf

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindTen_outside

/-- **A face-class chain on the side of `w` crosses no edge of `L`** when every dart of `L` has
its face off the side of `w`. -/
theorem gfaceWindTen_transfer {M : CombMap.{v}} {w L : List M.Dart}
    (hL : ∀ d ∈ L, M.faceOf d ∉ sideFaces M w) {x z : M.Dart}
    (h : Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M w)) x z) :
    M.faceOf x ∈ sideFaces M w →
      Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M L)) x z := by
  induction h with
  | rel x₁ x₂ hstep =>
      intro hx
      rcases hstep with hface | ⟨hk, rfl⟩
      · exact .rel _ _ (Or.inl hface)
      · have hα : M.faceOf (M.alpha x₁) ∈ sideFaces M w :=
          (mem_sideFaces_iff_of_eqvGen w (.rel _ _ (Or.inr ⟨hk, rfl⟩))).mp hx
        refine .rel _ _ (Or.inr ⟨?_, rfl⟩)
        rintro (hmem | hmem)
        · exact hL x₁ hmem hx
        · exact hL _ hmem hα
  | refl x₁ =>
      intro _
      exact .refl _
  | symm x₁ x₂ hrel ih =>
      intro hx
      exact .symm _ _ (ih ((mem_sideFaces_iff_of_eqvGen w hrel).mpr hx))
  | trans x₁ x₂ x₃ h₁₂ _ ih₁ ih₂ =>
      intro hx
      exact .trans _ _ _ (ih₁ hx) (ih₂ ((mem_sideFaces_iff_of_eqvGen w h₁₂).mp hx))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindTen_transfer

/-- **Side nesting.**  In a planar map, if every dart of `L` has its face on the side of the simple
closed walk `W`, and the face `o` is off both sides, then the side of `L` lies in the side of
`W`. -/
theorem gfaceWindTen_nest {M : CombMap.{v}} (hM : M.IsPlanar) {W L : List M.Dart}
    (hW : IsSimpleClosedWalk M W) (hLW : ∀ d ∈ L, M.faceOf d ∈ sideFaces M W)
    {o : M.Face} (hoW : o ∉ sideFaces M W) (hoL : o ∉ sideFaces M L) :
    sideFaces M L ⊆ sideFaces M W := by
  intro F hF
  obtain ⟨z, hz⟩ := Quotient.exists_rep F
  have hz' : M.faceOf z = F := hz
  subst hz'
  obtain ⟨zo, hzo⟩ := Quotient.exists_rep o
  have hzo' : M.faceOf zo = o := hzo
  subst hzo'
  by_contra hFW
  have hW' := hW.reverseAlpha
  have hside := gfaceWindTen_outside hM hW
  have hzW' : M.faceOf z ∈ sideFaces M (W.reverse.map M.alpha) := by
    rw [hside, mem_sideOutside_iff]
    exact hFW
  have hoW' : M.faceOf zo ∈ sideFaces M (W.reverse.map M.alpha) := by
    rw [hside, mem_sideOutside_iff]
    exact hoW
  obtain ⟨d1, hd1, h1⟩ := (mem_sideFaces_iff M _ z).mp hzW'
  obtain ⟨d2, hd2, h2⟩ := (mem_sideFaces_iff M _ zo).mp hoW'
  have hzzo : Relation.EqvGen
      (CombMap.FaceClassStep M (walkKeep M (W.reverse.map M.alpha))) z zo :=
    .trans _ _ _ (.symm _ _ h1) (.trans _ _ _ (.symm _ _ (gfaceWindTen_class_head hW' d1 hd1))
      (.trans _ _ _ (gfaceWindTen_class_head hW' d2 hd2) h2))
  have hLW' : ∀ d ∈ L, M.faceOf d ∉ sideFaces M (W.reverse.map M.alpha) := by
    intro d hd h
    rw [hside, mem_sideOutside_iff] at h
    exact h (hLW d hd)
  have hzzoL := gfaceWindTen_transfer hLW' hzzo hzW'
  obtain ⟨d, hd, hdz⟩ := (mem_sideFaces_iff M L z).mp hF
  exact hoL ((mem_sideFaces_iff M L zo).mpr ⟨d, hd, .trans _ _ _ hdz hzzoL⟩)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindTen_nest

/-- **Strict side nesting.**  Under the hypotheses of `gfaceWindTen_nest`, if `L` is a simple
closed walk with a dart off `W`, its side has fewer faces than the side of `W`. -/
theorem gfaceWindTen_card_lt {M : CombMap.{v}} (hM : M.IsPlanar) {W L : List M.Dart}
    (hW : IsSimpleClosedWalk M W) (hL : IsSimpleClosedWalk M L)
    (hLW : ∀ d ∈ L, M.faceOf d ∈ sideFaces M W)
    {o : M.Face} (hoW : o ∉ sideFaces M W) (hoL : o ∉ sideFaces M L)
    {x : M.Dart} (hxL : x ∈ L) (hxW : x ∉ W) :
    (sideFaces M L).card < (sideFaces M W).card := by
  refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
    ⟨gfaceWindTen_nest hM hW hLW hoW hoL, fun heq => hxW ?_⟩)
  have hb := (hL.isBoundaryDart_sideFaces_iff hM x).mpr hxL
  rw [heq] at hb
  exact (hW.isBoundaryDart_sideFaces_iff hM x).mp hb

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindTen_card_lt

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind
