import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.GFaceWindList
import GroupApproximation.Meta.AxiomGuard

/-!
# Winding choice of `F'`: excision steps

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-55.

A state is a pair `(c, g)` of a sub-walk `c` of the pocket walk `C` and an integer face function
`g`.  One excision step (`gfaceWind_Step`) cuts a simple closed stretch `W` out of `c`, where
`c = p ++ A ++ q` and `W` is either `A` (inner, leaving `p ++ q`) or the wrapping stretch
`q ++ p` (leaving `A`), and subtracts the winding function of `W`.

* `gfaceWind_Inv`: `c` is the sub-list of `C` it filters, a walk, the coboundary of `g`, and
  `g` vanishes at the base face.
* `gfaceWind_inv_start`: the start `(C, indicator of the faces)`.
* `gfaceWind_cob_excise`: the coboundary part of the invariant survives an excision.

That steps keep the invariant is `Piece10Live/GFaceWindReach`.

## Truth check

See `Piece10Live/GFaceWind`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

universe v

open scoped Classical

/-- **One excision step** on states `(c, g)`: cut a simple closed stretch out of `c`, either an
inner stretch `A` of `c = p ++ A ++ q` or the wrapping stretch `q ++ p`, and subtract its
winding function (normalised at the base face `o`). -/
def gfaceWind_Step (M : CombMap.{v}) (o : M.Face) (s t : List M.Dart × (M.Face → ℤ)) : Prop :=
  ∃ p A q : List M.Dart, s.1 = p ++ A ++ q ∧
    ((IsSimpleClosedWalk M A ∧ t.1 = p ++ q ∧ t.2 = fun f => s.2 f - gfaceWind_wind M o A f) ∨
      (IsSimpleClosedWalk M (q ++ p) ∧ t.1 = A ∧
        t.2 = fun f => s.2 f - gfaceWind_wind M o (q ++ p) f))

/-- **The invariant of a state `(c, g)`** over the walk `C` and base face `o`. -/
def gfaceWind_Inv (M : CombMap.{v}) (C : List M.Dart) (o : M.Face) (c : List M.Dart)
    (g : M.Face → ℤ) : Prop :=
  C.filter (gfaceWind_mem c) = c ∧
    c.IsChain (fun d e => M.vertexOf (M.alpha d) = M.vertexOf e) ∧
    (∀ d, g (M.faceOf d) - g (M.faceOf (M.alpha d)) =
      gfaceWind_lind c d - gfaceWind_lind c (M.alpha d)) ∧ g o = 0

theorem gfaceWind_inv_start {M : CombMap.{v}} {C : List M.Dart} {F : Finset M.Face}
    {o : M.Face} (hS : ∀ d, Surgery.MapCollapse.IsBoundaryDart M F d ↔ d ∈ C)
    (hch : C.IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e) (ho : o ∉ F) :
    gfaceWind_Inv M C o C (gfaceWind_ind F) :=
  ⟨List.filter_eq_self.mpr fun _ hx => gfaceWind_mem_eq_true_iff.mpr hx, hch,
    gfaceWind_ind_cob hS, gfaceWind_ind_neg ho⟩

/-- **Excising a winding function**: the coboundary and base-face parts of the invariant pass
from `c` to `r` when `c` is the disjoint union of `r` and a simple closed walk `W`. -/
theorem gfaceWind_cob_excise {M : CombMap.{v}} (hM : M.IsPlanar) {o : M.Face}
    {c W r : List M.Dart} {g g' : M.Face → ℤ} (hw : IsSimpleClosedWalk M W)
    (hmem : ∀ x, x ∈ c ↔ x ∈ W ∨ x ∈ r) (hd : ∀ x ∈ W, x ∉ r)
    (hcob : ∀ d, g (M.faceOf d) - g (M.faceOf (M.alpha d)) =
      gfaceWind_lind c d - gfaceWind_lind c (M.alpha d)) (ho : g o = 0)
    (hg : g' = fun f => g f - gfaceWind_wind M o W f) :
    (∀ d, g' (M.faceOf d) - g' (M.faceOf (M.alpha d)) =
      gfaceWind_lind r d - gfaceWind_lind r (M.alpha d)) ∧ g' o = 0 := by
  subst hg
  refine ⟨fun d => ?_, ?_⟩
  · have h1 := hcob d
    have h2 := gfaceWind_wind_cob hM hw o d
    have h3 := gfaceWind_lind_split hmem hd d
    have h4 := gfaceWind_lind_split hmem hd (M.alpha d)
    show g (M.faceOf d) - gfaceWind_wind M o W (M.faceOf d) -
      (g (M.faceOf (M.alpha d)) - gfaceWind_wind M o W (M.faceOf (M.alpha d))) = _
    linarith
  · show g o - gfaceWind_wind M o W o = 0
    have h : gfaceWind_wind M o W o = 0 := sub_self _
    linarith

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWind_Step
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWind_Inv
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWind_inv_start
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWind_cob_excise
