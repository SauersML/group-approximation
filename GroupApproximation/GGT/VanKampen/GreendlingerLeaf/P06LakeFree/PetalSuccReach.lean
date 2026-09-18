import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketLakeAbsorption
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P06, cactus petal: a smaller boundary sees the same inside along a piece

Infrastructure for `P06LakeFree.cellPocketLakeFreePetalSucc_of_petalTurn`
(`P06LakeFree/PetalSuccStatement.lean`), lane gl-p06-17.  Osin, arXiv:math/0411039v3, §9, proof
of Lemma 9.7(b).

## Truth check and proof

Let `S`, `T` be face sets and assume every boundary dart of `S` is a boundary dart of `T`.

* *Boundary edges.*  `BoundaryEdge S x` (`x` or `α x` a boundary dart of `S`) gives
  `BoundaryEdge T x`.
* *Reaches.*  A crossing allowed off `T` is allowed off `S`: its dart is off the boundary edges of
  `T`, hence off those of `S`.  Moving around a face is always allowed.  So a reach for `T` is a
  reach for `S` (induction on the equivalence closure).
* *Membership along a piece.*  If `f` lies in the piece of `o` for `T`, a reach for `T` from a dart
  on `o` to a dart on `f` is a reach for `S`, and reaches for `S` keep membership in `S`
  (`ExteriorComponent.faceOf_mem_iff_of_eqvGen`), so `o ∈ S ↔ f ∈ S`.

With `S` the side of a walk on `∂K` and `T = K.faces`, this is the lake freeness argument: every
face off `K` is inside the side of the walk exactly when the outer face is.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121) through Osin's Lemma 9.7(b); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalSucc

universe v

open Surgery.MapCollapse Surgery.MapCollapse.ExteriorComponent

variable {M : CombMap.{v}}

/-- Boundary edges of a face set whose boundary darts are boundary darts of another are boundary
edges of the other. -/
theorem petalSucc_boundaryEdge_mono {S T : Finset M.Face}
    (h : ∀ x, IsBoundaryDart M S x → IsBoundaryDart M T x) {x : M.Dart}
    (hx : BoundaryEdge M S x) : BoundaryEdge M T x := by
  rcases hx with hx | hx
  · exact show IsBoundaryDart M T x ∨ IsBoundaryDart M T (M.alpha x) from Or.inl (h x hx)
  · exact show IsBoundaryDart M T x ∨ IsBoundaryDart M T (M.alpha x) from Or.inr (h _ hx)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalSucc.petalSucc_boundaryEdge_mono

/-- **Reaches off the larger boundary are reaches off the smaller one.** -/
theorem petalSucc_eqvGen_mono {S T : Finset M.Face}
    (h : ∀ x, IsBoundaryDart M S x → IsBoundaryDart M T x) {x y : M.Dart}
    (hxy : Relation.EqvGen (CombMap.FaceClassStep M (BoundaryEdge M T)) x y) :
    Relation.EqvGen (CombMap.FaceClassStep M (BoundaryEdge M S)) x y := by
  induction hxy with
  | rel a b hab =>
      rcases hab with hstep | ⟨hoff, hstep⟩
      · exact Relation.EqvGen.rel _ _
          (show CombMap.FaceClassStep M (BoundaryEdge M S) a b from Or.inl hstep)
      · exact Relation.EqvGen.rel _ _
          (show CombMap.FaceClassStep M (BoundaryEdge M S) a b from
            Or.inr ⟨fun hS => hoff (petalSucc_boundaryEdge_mono h hS), hstep⟩)
  | refl a => exact Relation.EqvGen.refl a
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalSucc.petalSucc_eqvGen_mono

/-- **Along a piece of the larger face set, the smaller face set holds both ends or neither.** -/
theorem petalSucc_mem_iff_of_mem_component {S T : Finset M.Face}
    (h : ∀ x, IsBoundaryDart M S x → IsBoundaryDart M T x) {o f : M.Face}
    (hf : f ∈ ExteriorComponent.component M T o) : o ∈ S ↔ f ∈ S := by
  obtain ⟨y, hy, x, hx, hxy⟩ := mem_component_iff.mp hf
  have hiff := faceOf_mem_iff_of_eqvGen (petalSucc_eqvGen_mono h hxy)
  rw [hx, hy] at hiff
  exact hiff

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalSucc.petalSucc_mem_iff_of_mem_component

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalSucc
