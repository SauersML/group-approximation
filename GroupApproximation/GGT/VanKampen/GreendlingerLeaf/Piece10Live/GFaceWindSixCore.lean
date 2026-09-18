import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.GFaceWindClauseCore
import GroupApproximation.Meta.AxiomGuard

/-!
# Winding choice of `F'`: face functions cobounded by a simple closed walk

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-61.

Route.  On a connected map a face function whose coboundary vanishes is constant: a vertex step
`d ↦ sigma d` stays on the face of `alpha d`, an edge step crosses a dart.  So a face function
cobounded by a simple closed walk `c` in a planar map, vanishing at a base face `o`, is the
winding function of `c` (`gfaceWindSix_eq_wind`); if it is also nonnegative then `o` lies off
the side of `c` (a first walk dart would give the value `-1` across it), so it is the indicator
of the side (`gfaceWindSix_zero_one`).  Across a walk dart a `0/1`-valued cobounded function
steps from `1` to `0` (`gfaceWindSix_walk_val`).

* `gfaceWindSix_const` (proved): constancy of coboundary-free face functions.
* `gfaceWindSix_nil`, `gfaceWindSix_eq_wind`, `gfaceWindSix_zero_one` (proved).
* `gfaceWindSix_ind01`, `gfaceWindSix_walk_val` (proved).

## Truth check

All statements here are proved (no hypothesis Props).  Consistent with scratchpad
`gl-p10-61/six.py`: every reached vertex-nodup state with `g ≥ 0` is `0/1`-valued (0 failures).

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

universe v

open scoped Classical

/-- **Coboundary-free face functions are constant** on a connected map. -/
theorem gfaceWindSix_const {M : CombMap.{v}} (hM : M.IsConnected) (φ : M.Face → ℤ)
    (hφ : ∀ d, φ (M.faceOf d) = φ (M.faceOf (M.alpha d))) (f f' : M.Face) : φ f = φ f' := by
  have key : ∀ d e, Relation.EqvGen M.Adjacent d e → φ (M.faceOf d) = φ (M.faceOf e) := by
    intro d e hde
    induction hde with
    | rel x y hxy =>
      rcases hxy with hxy | hxy
      · rw [← hxy]
        exact hφ x
      · rw [← hxy]
        have h2 : M.facePerm (M.alpha x) = M.sigma x := by
          change M.sigma (M.alpha (M.alpha x)) = M.sigma x
          rw [M.alpha_involutive x]
        rw [← h2, M.faceOf_facePerm]
        exact hφ x
    | refl _ => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  obtain ⟨d, rfl⟩ : ∃ x, M.faceOf x = f := Quotient.inductionOn' f fun x => ⟨x, rfl⟩
  obtain ⟨e, rfl⟩ : ∃ x, M.faceOf x = f' := Quotient.inductionOn' f' fun x => ⟨x, rfl⟩
  exact key d e (hM d e)

/-- **A face function cobounded by the empty walk** and vanishing at `o` is zero. -/
theorem gfaceWindSix_nil {M : CombMap.{v}} (hM : M.IsConnected) {o : M.Face}
    {g : M.Face → ℤ}
    (hcob : ∀ d, g (M.faceOf d) - g (M.faceOf (M.alpha d)) =
      gfaceWind_lind ([] : List M.Dart) d - gfaceWind_lind ([] : List M.Dart) (M.alpha d))
    (ho : g o = 0) : ∀ f, g f = 0 := by
  intro f
  have h : g f = g o := by
    refine gfaceWindSix_const hM g (fun d => ?_) f o
    have h1 := hcob d
    have h2 : gfaceWind_lind ([] : List M.Dart) d = 0 := gfaceWind_lind_neg (by simp)
    have h3 : gfaceWind_lind ([] : List M.Dart) (M.alpha d) = 0 := gfaceWind_lind_neg (by simp)
    linarith
  rw [h, ho]

/-- **A face function cobounded by a simple closed walk is its winding function.** -/
theorem gfaceWindSix_eq_wind {M : CombMap.{v}} (hM : M.IsPlanar) {c : List M.Dart}
    (hw : IsSimpleClosedWalk M c) {o : M.Face} {g : M.Face → ℤ}
    (hcob : ∀ d, g (M.faceOf d) - g (M.faceOf (M.alpha d)) =
      gfaceWind_lind c d - gfaceWind_lind c (M.alpha d))
    (ho : g o = 0) (f : M.Face) : g f = gfaceWind_wind M o c f := by
  have h : g f - gfaceWind_wind M o c f = g o - gfaceWind_wind M o c o := by
    refine gfaceWindSix_const (M.connected_of_planar hM)
      (fun f => g f - gfaceWind_wind M o c f) (fun d => ?_) f o
    have h1 := hcob d
    have h2 := gfaceWind_wind_cob hM hw o d
    show g (M.faceOf d) - gfaceWind_wind M o c (M.faceOf d) =
      g (M.faceOf (M.alpha d)) - gfaceWind_wind M o c (M.faceOf (M.alpha d))
    linarith
  have h0 : gfaceWind_wind M o c o = 0 := sub_self _
  linarith

/-- **A nonnegative face function cobounded by a simple closed walk** and vanishing at `o` is
the indicator of the side of the walk, and `o` lies off the side. -/
theorem gfaceWindSix_zero_one {M : CombMap.{v}} (hM : M.IsPlanar) {c : List M.Dart}
    (hw : IsSimpleClosedWalk M c) {o : M.Face} {g : M.Face → ℤ}
    (hcob : ∀ d, g (M.faceOf d) - g (M.faceOf (M.alpha d)) =
      gfaceWind_lind c d - gfaceWind_lind c (M.alpha d))
    (ho : g o = 0) (hpos : ∀ f, 0 ≤ g f) :
    o ∉ SimpleClosedWalkSides.sideFaces M c ∧
      ∀ f, g f = gfaceWind_ind (SimpleClosedWalkSides.sideFaces M c) f := by
  have hwind := gfaceWindSix_eq_wind hM hw hcob ho
  have hout : o ∉ SimpleClosedWalkSides.sideFaces M c := by
    intro hoS
    have hx : c.head hw.ne_nil ∈ c := List.head_mem hw.ne_nil
    have hbd := (hw.isBoundaryDart_sideFaces_iff hM _).mpr hx
    have h1 := hwind (M.faceOf (M.alpha (c.head hw.ne_nil)))
    have h2 := hpos (M.faceOf (M.alpha (c.head hw.ne_nil)))
    unfold gfaceWind_wind at h1
    rw [gfaceWind_ind_neg hbd.2, gfaceWind_ind_pos hoS] at h1
    linarith
  refine ⟨hout, fun f => ?_⟩
  rw [hwind f]
  unfold gfaceWind_wind
  rw [gfaceWind_ind_neg hout, sub_zero]

/-- **Indicators are `0/1`-valued.** -/
theorem gfaceWindSix_ind01 {M : CombMap.{v}} (F : Finset M.Face) (f : M.Face) :
    gfaceWind_ind F f = 0 ∨ gfaceWind_ind F f = 1 := by
  by_cases h : f ∈ F
  · exact Or.inr (gfaceWind_ind_pos h)
  · exact Or.inl (gfaceWind_ind_neg h)

/-- **Across a walk dart** a `0/1`-valued cobounded face function steps from `1` to `0`. -/
theorem gfaceWindSix_walk_val {M : CombMap.{v}} {c : List M.Dart} {g : M.Face → ℤ}
    (hcob : ∀ d, g (M.faceOf d) - g (M.faceOf (M.alpha d)) =
      gfaceWind_lind c d - gfaceWind_lind c (M.alpha d))
    (h01 : ∀ f, g f = 0 ∨ g f = 1) {x : M.Dart} (hx : x ∈ c) (hax : M.alpha x ∉ c) :
    g (M.faceOf x) = 1 ∧ g (M.faceOf (M.alpha x)) = 0 := by
  have h := hcob x
  rw [gfaceWind_lind_pos hx, gfaceWind_lind_neg hax] at h
  rcases h01 (M.faceOf x) with h1 | h1 <;> rcases h01 (M.faceOf (M.alpha x)) with h2 | h2 <;>
    exact ⟨by linarith, by linarith⟩

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSix_const
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSix_nil
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSix_eq_wind
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSix_zero_one
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSix_ind01
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSix_walk_val
