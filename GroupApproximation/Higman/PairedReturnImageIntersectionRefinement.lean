import GroupApproximation.Higman.PairedReturnQProfinite
import GroupApproximation.Algebra.FiniteResidual

/-!
# Finite refinements with exact paired graph-edge intersection

A finite quotient of the paired base can create accidental intersections
between the image of Higman's graph and the image of the paired edge.  The
kill-`a` coordinate removes those accidental intersections after one further
finite refinement.  This is the compatibility input required by the matched
amalgam normal-form argument.
-/

namespace GroupApproximation
namespace Higman
namespace PairedReturnImageIntersectionRefinement

open PairedReturnCutter
open Conj

abbrev P := PairedReturnGraphIntersection.P
abbrev Edge := ↑PairedReturnGraphIntersection.M
abbrev Sync := ↑Conj.K

/-- The kill-`a` coordinate of the paired base, intrinsically valued in
`Sync`. -/
def syncRet : P →* Sync :=
  PairedReturnQProfinite.retKSync.comp (MonoidHom.fst _ _)

theorem syncRet_eq_one_of_mem_graph {g : P} (hg : g ∈ Star.graphSub) :
    syncRet g = 1 := by
  apply Subtype.ext
  change ((PairedReturnQProfinite.retKSync g.1 : Sync) : F₃) = 1
  exact (DFunLike.congr_fun
    PairedReturnQProfinite.subtype_comp_retKSync g.1).trans
      (MonoidHom.mem_ker.mp
        (PairedReturnGraphIntersection.graphSub_le_retK_fst_ker hg))

@[simp] theorem syncRet_edgeToP (m : Edge) :
    syncRet (edgeToP m) = PairedReturnQProfinite.edgeFold m := by
  apply Subtype.ext
  change ((PairedReturnQProfinite.retKSync (m : P).1 : Sync) : F₃) =
    Coord.retK (m : P).1
  exact DFunLike.congr_fun PairedReturnQProfinite.subtype_comp_retKSync
    (m : P).1

theorem edgeFold_surjective :
    Function.Surjective PairedReturnQProfinite.edgeFold := by
  intro k
  refine ⟨PairedReturnGraphIntersection.muToM
    (Monoid.Coprod.inl k), ?_⟩
  simp [PairedReturnQProfinite.edgeFold_muToM]

theorem edgeFold_ker_eq_Delta :
    PairedReturnQProfinite.edgeFold.ker =
      PairedReturnGraphIntersection.Delta := by
  ext m
  change PairedReturnQProfinite.edgeFold m = 1 ↔
    m ∈ PairedReturnGraphIntersection.Delta
  rw [← PairedReturnGraphIntersection.psi_ker_eq_Delta]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

/-- The finite-index part of the edge killed by a prescribed finite
quotient. -/
def edgeKernel (Q₀ : Type) [Group Q₀]
    (q₀ : P →* Q₀) : Subgroup Edge :=
  (q₀.comp edgeToP).ker

instance edgeKernel_finiteIndex (Q₀ : Type) [Group Q₀] [Finite Q₀]
    (q₀ : P →* Q₀) : (edgeKernel Q₀ q₀).FiniteIndex := by
  exact Subgroup.finiteIndex_ker (q₀.comp edgeToP)

/-- Its image in the synchronization coordinate. -/
def syncKernelImage (Q₀ : Type) [Group Q₀]
    (q₀ : P →* Q₀) : Subgroup Sync :=
  (edgeKernel Q₀ q₀).map PairedReturnQProfinite.edgeFold

instance syncKernelImage_finiteIndex
    (Q₀ : Type) [Group Q₀] [Finite Q₀]
    (q₀ : P →* Q₀) :
    (syncKernelImage Q₀ q₀).FiniteIndex := by
  apply Subgroup.finiteIndex_iff.mpr
  exact ne_zero_of_dvd_ne_zero
    (Subgroup.FiniteIndex.index_ne_zero
      (H := edgeKernel Q₀ q₀))
    ((edgeKernel Q₀ q₀).index_map_dvd edgeFold_surjective)

/-- A normal finite-index subgroup small enough to be lifted through the
kernel of the original quotient. -/
def refinementCore (Q₀ : Type) [Group Q₀]
    (q₀ : P →* Q₀) : Subgroup Sync :=
  (syncKernelImage Q₀ q₀).normalCore

instance refinementCore_normal (Q₀ : Type) [Group Q₀]
    (q₀ : P →* Q₀) : (refinementCore Q₀ q₀).Normal :=
  by
    unfold refinementCore
    infer_instance

instance refinementCore_finiteIndex
    (Q₀ : Type) [Group Q₀] [Finite Q₀]
    (q₀ : P →* Q₀) :
    (refinementCore Q₀ q₀).FiniteIndex := by
  unfold refinementCore
  infer_instance

/-- The refined finite target. -/
abbrev Target (Q₀ : Type) [Group Q₀]
    (q₀ : P →* Q₀) :=
  Q₀ × (Sync ⧸ refinementCore Q₀ q₀)

/-- Add the finite kill-`a` quotient to the prescribed quotient. -/
def refineHom (Q₀ : Type) [Group Q₀]
    (q₀ : P →* Q₀) : P →* Target Q₀ q₀ :=
  q₀.prod ((QuotientGroup.mk' (refinementCore Q₀ q₀)).comp syncRet)

@[simp] theorem refineHom_fst (Q₀ : Type) [Group Q₀]
    (q₀ : P →* Q₀) (g : P) :
    (refineHom Q₀ q₀ g).1 = q₀ g := rfl

theorem refinementCore_le_syncKernelImage
    (Q₀ : Type) [Group Q₀]
    (q₀ : P →* Q₀) :
    refinementCore Q₀ q₀ ≤ syncKernelImage Q₀ q₀ :=
  (syncKernelImage Q₀ q₀).normalCore_le

/-- The refinement has no accidental graph-edge intersection: its two mapped
subgroups meet in precisely the mapped returning subgroup. -/
theorem map_graph_inf_map_edge_eq_map_delta
    (Q₀ : Type) [Group Q₀] [Finite Q₀]
    (q₀ : P →* Q₀) :
    Star.graphSub.map (refineHom Q₀ q₀) ⊓
        PairedReturnGraphIntersection.M.map (refineHom Q₀ q₀) =
      PairedReturnGraphIntersection.deltaSub.map (refineHom Q₀ q₀) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxGraph, hxEdge⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨g, hg, hgx⟩ := Subgroup.mem_map.mp hxGraph
    obtain ⟨m, hm, hmx⟩ := Subgroup.mem_map.mp hxEdge
    let ms : Edge := ⟨m, hm⟩
    have heq : refineHom Q₀ q₀ g = refineHom Q₀ q₀ m :=
      hgx.trans hmx.symm
    have hq₀ : q₀ g = q₀ m := congrArg Prod.fst heq
    have hgSync : syncRet g = 1 := syncRet_eq_one_of_mem_graph hg
    have hmQuot :
        QuotientGroup.mk' (refinementCore Q₀ q₀) (syncRet m) = 1 := by
      have hsnd := congrArg Prod.snd heq
      change QuotientGroup.mk' (refinementCore Q₀ q₀) (syncRet g) =
        QuotientGroup.mk' (refinementCore Q₀ q₀) (syncRet m) at hsnd
      rw [hgSync, map_one] at hsnd
      exact hsnd.symm
    have hmCore : syncRet m ∈ refinementCore Q₀ q₀ :=
      (QuotientGroup.eq_one_iff (syncRet m)).mp hmQuot
    have hmImage : syncRet m ∈ syncKernelImage Q₀ q₀ :=
      refinementCore_le_syncKernelImage Q₀ q₀ hmCore
    obtain ⟨k, hkKernel, hkSync⟩ := Subgroup.mem_map.mp hmImage
    let deltaEdge : Edge := ms * k⁻¹
    have hdeltaFold : PairedReturnQProfinite.edgeFold deltaEdge = 1 := by
      rw [map_mul, map_inv, hkSync]
      rw [show PairedReturnQProfinite.edgeFold ms = syncRet m by
        exact (syncRet_edgeToP ms).symm]
      exact mul_inv_cancel _
    have hdelta : (deltaEdge : P) ∈
        PairedReturnGraphIntersection.deltaSub := by
      change deltaEdge ∈ PairedReturnGraphIntersection.Delta
      rw [← edgeFold_ker_eq_Delta]
      exact MonoidHom.mem_ker.mpr hdeltaFold
    refine ⟨(deltaEdge : P), hdelta, ?_⟩
    rw [← hmx]
    apply Prod.ext
    · change q₀ ((ms : P) * (k : P)⁻¹) = q₀ m
      rw [map_mul, map_inv]
      have hkOne : q₀ (k : P) = 1 := MonoidHom.mem_ker.mp hkKernel
      rw [hkOne, inv_one, mul_one]
    · change QuotientGroup.mk' (refinementCore Q₀ q₀)
          (syncRet (deltaEdge : P)) =
        QuotientGroup.mk' (refinementCore Q₀ q₀) (syncRet m)
      have hsyncDelta : syncRet (deltaEdge : P) = 1 :=
        (syncRet_edgeToP deltaEdge).trans hdeltaFold
      rw [hsyncDelta]
      exact (map_one _).trans hmQuot.symm
  · intro x hx
    exact Subgroup.mem_inf.mpr ⟨
      Subgroup.map_mono PairedReturnGraphIntersection.deltaSub_le_graphSub hx,
      Subgroup.map_mono PairedReturnGraphIntersection.deltaSub_le_M hx⟩

end PairedReturnImageIntersectionRefinement
end Higman
end GroupApproximation
