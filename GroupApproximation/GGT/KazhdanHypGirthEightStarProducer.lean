import GroupApproximation.GGT.KazhdanHypGirthEightVKInterface
import GroupApproximation.GGT.KazhdanHypGirthEightLayerInjection
import GroupApproximation.GGT.VanKampen.DiscPathHomotopy

/-!
# Clean successive-star construction

This module contains the constructor after its genuine geometric inputs have
been supplied.  The rooted-path theorem produces a Cayley labelling, the
centered layer cover produces the first-face incidence injection and its
covering inequality, and `CombMapStars` proves the disjoint-layer area bound.
The remaining source is the construction of the rooted paths and centered
cover for a reduced filling; no such producer is present in the clean vk API.
-/

namespace GroupApproximation
namespace GGT
namespace KazhdanHypGirthEightStarProducer

open GroupApproximation.GGT.GirthEightVKInterface
open GroupApproximation.GGT.GirthEightPrimitives2
open GroupApproximation.KazhdanHyp
open GroupApproximation.WordMetric
open scoped BigOperators

section Table

variable {Generator TriangleIndex : Type}
  [Fintype Generator] [DecidableEq Generator]
  [Fintype TriangleIndex] [DecidableEq TriangleIndex]
  {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}

/-! ## The four stored inequalities -/

omit [Fintype Generator] [DecidableEq Generator]
    [Fintype TriangleIndex] [DecidableEq TriangleIndex] in
theorem innerStarLayers_sum_bound
    (Delta : VanKampen.DiscDiagram (triangleRelatorWords T))
    (P : BoundarySubpath T Delta) (depth : ℕ) :
    (∑ i : Fin depth,
      (innerBoundaryFaceStarLayer Delta P i).card) ≤ Delta.innerFaceCount := by
  classical
  have hpairwise :
      ((Finset.univ : Finset (Fin depth)) : Set (Fin depth)).PairwiseDisjoint
        (fun i ↦ innerBoundaryFaceStarLayer Delta P i) := by
    intro i _hi j _hj hij
    exact innerBoundaryFaceStarLayer_disjoint Delta P (by
      intro hval
      apply hij
      exact Fin.ext hval)
  rw [← Finset.card_biUnion hpairwise]
  apply Finset.card_le_card
  intro f hf
  obtain ⟨i, _hi, hfi⟩ := Finset.mem_biUnion.mp hf
  exact (Finset.mem_inter.mp hfi).2

/-! ## Rooted paths and centered covers -/

/-- The exact local certificate whose output is immediately a successive-star
record.  `centered_cover` is the first-face covering fact; its incidence
injection is constructed by the clean layer module. -/
structure StarLayerConstructionCertificate
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    (_L : TriangularDiagramLocalData T Delta) where
  rooted : RootedPathSystem Delta.toCombMap
  rooted_complete : RootedPathsFaceComplete Delta rooted
  side : BoundarySubpath T Delta
  depth : ℕ
  scale : ℕ
  loss : ℕ
  perimeter : ℕ
  centered_cover : CenteredWindowLayerCover
    Delta side depth scale loss perimeter
  boundary_bound : Delta.combinatorialBoundaryLength ≤ 6 * scale
  depth_too_large : 18 * perimeter * scale < depth * (scale - loss)

/-- Build the exact `SuccessiveStarLayers` record from the path and centered
cover certificate. -/
noncomputable def StarLayerConstructionCertificate.toSuccessiveStarLayers
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    (L : TriangularDiagramLocalData T Delta)
    (C : StarLayerConstructionCertificate Delta L) :
    SuccessiveStarLayers T := by
  let relatorOnly : RelatorOnly T Delta := { cell := L.innerFaceCell }
  let cayley := cayleyVertexLabelling_of_faceComplete Delta relatorOnly
    C.rooted C.rooted_complete
  let hcover := layerCoversWindow_of_layerCover Delta C.side C.depth
    C.scale C.loss C.perimeter C.centered_cover
  exact {
    diagram := Delta
    localData := L
    cayley := cayley
    side := C.side
    depth := C.depth
    scale := C.scale
    loss := C.loss
    perimeter := C.perimeter
    layer := fun i => (innerBoundaryFaceStarLayer Delta C.side i).card
    boundary_bound := C.boundary_bound
    layer_disjoint := innerStarLayers_sum_bound Delta C.side C.depth
    layer_covers := hcover
    depth_too_large := C.depth_too_large }

theorem starLayerConstructionCertificate_boundary_bound
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    (L : TriangularDiagramLocalData T Delta)
    (C : StarLayerConstructionCertificate Delta L) :
    (C.toSuccessiveStarLayers Delta L).diagram.combinatorialBoundaryLength ≤
      6 * (C.toSuccessiveStarLayers Delta L).scale :=
  C.boundary_bound

/-! ## The remaining source and its consumer -/

/-- The global source still needed to make the local star construction
unconditional.  Its output is the exact rooted-path/centered-cover package;
the four numerical fields are retained here so no estimate is hidden. -/
def StarLayerConstructionCertificateInput : Prop :=
  ∀ (delta : ℕ) (x y z p : TriangularHodgeLayer.Presented T),
    Hyperbolic.IsBetween
      (↑(GirthEightSlim.presentedGeneratorFinset T) :
        Set (TriangularHodgeLayer.Presented T)) x p y →
    (∀ q : TriangularHodgeLayer.Presented T,
      Hyperbolic.IsBetween
        (↑(GirthEightSlim.presentedGeneratorFinset T) :
          Set (TriangularHodgeLayer.Presented T)) x q z →
      delta < wordDist
        (↑(GirthEightSlim.presentedGeneratorFinset T) :
          Set (TriangularHodgeLayer.Presented T)) p q) →
    (∀ q : TriangularHodgeLayer.Presented T,
      Hyperbolic.IsBetween
        (↑(GirthEightSlim.presentedGeneratorFinset T) :
          Set (TriangularHodgeLayer.Presented T)) z q y →
      delta < wordDist
        (↑(GirthEightSlim.presentedGeneratorFinset T) :
          Set (TriangularHodgeLayer.Presented T)) p q) →
    ∀ (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T)),
      Delta.Reduced →
      ∃ L : TriangularDiagramLocalData T Delta,
        Nonempty (StarLayerConstructionCertificate Delta L)

/-- The source package constructs a `SuccessiveStarLayers` record for every
geodesic configuration. -/
theorem successiveStarLayers_of_certificateInput
    (hsource : StarLayerConstructionCertificateInput (T := T)) :
    ∀ (delta : ℕ) (x y z p : TriangularHodgeLayer.Presented T),
      Hyperbolic.IsBetween
        (↑(GirthEightSlim.presentedGeneratorFinset T) :
          Set (TriangularHodgeLayer.Presented T)) x p y →
      (∀ q : TriangularHodgeLayer.Presented T,
        Hyperbolic.IsBetween
          (↑(GirthEightSlim.presentedGeneratorFinset T) :
            Set (TriangularHodgeLayer.Presented T)) x q z →
        delta < wordDist
          (↑(GirthEightSlim.presentedGeneratorFinset T) :
            Set (TriangularHodgeLayer.Presented T)) p q) →
      (∀ q : TriangularHodgeLayer.Presented T,
        Hyperbolic.IsBetween
          (↑(GirthEightSlim.presentedGeneratorFinset T) :
            Set (TriangularHodgeLayer.Presented T)) z q y →
        delta < wordDist
          (↑(GirthEightSlim.presentedGeneratorFinset T) :
            Set (TriangularHodgeLayer.Presented T)) p q) →
      ∀ (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T)),
        Delta.Reduced →
        ∃ L : TriangularDiagramLocalData T Delta,
          Nonempty (SuccessiveStarLayers T) := by
  intro delta x y z p hp hfarXZ hfarZY Delta hred
  obtain ⟨L, ⟨C⟩⟩ := hsource delta x y z p hp hfarXZ hfarZY Delta hred
  exact ⟨L, ⟨C.toSuccessiveStarLayers Delta L⟩⟩

/-! ## One-triangle layer model -/

theorem oneTriangle_unit_cover_model :
    ∀ _i : Fin 1, 1 - 0 ≤ 1 *
      (VanKampen.oneTriangleCombMap.faceStarLayer
        (Finset.univ : Finset VanKampen.oneTriangleCombMap.Face) 0).card :=
  layer_covers_of_incidenceInjection oneTriangle_unitIncidenceInjection

end Table
end KazhdanHypGirthEightStarProducer
end GGT
end GroupApproximation
