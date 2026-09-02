import GroupApproximation.GGT.KazhdanHypGirthEight
import GroupApproximation.GGT.KazhdanHypGQLinkTransfer
import GroupApproximation.GGT.KazhdanHypSingerReduction
import GroupApproximation.GGT.KazhdanHypSymplecticQuadrangleStrongRegular
import GroupApproximation.GGT.KazhdanHypGQTwoTable

/-!
# Identifying the presentation link with `W(8)`

The signed link vertex `(p,true)` is a point and `(p,false)` is the line named
by the table bijection `lineMap p`.  The corner relation below is exactly the
presentation-link convention used by `TriangularHodgeLayer`: a cyclic corner
from `(x,s)` to the inverse of `(y,t)` contributes to the undirected count.

The resulting signed-vertex equivalence is fed to the existing
`KazhdanHypGQLinkTransfer` bridge.  Thus the `GeneralizedQuadrangleCounts`
instance and its rational Gram rows come from the algebraic W(8) instance;
there is no enumeration of the 1170 link vertices.  This is the finite link
input used alongside Huebschmann's least-area spherical-map obstruction and
Duda's `C(3)-T(6)` discussion (arXiv:2112.01912, `all3.tex`, circa
lines 1234--1249).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GroupApproximation
namespace KazhdanHyp

open scoped BigOperators

/-! ## The signed incidence convention -/

/-- The point/line vertex map induced by a point-to-line bijection. -/
def signedVertexEquiv {Point Line : Type} (lineMap : Point ≃ Line) :
    (Point × Bool) ≃ (Point ⊕ Line) where
  toFun u := match u.2 with
    | true => Sum.inl u.1
    | false => Sum.inr (lineMap u.1)
  invFun v := match v with
    | Sum.inl p => (p, true)
    | Sum.inr l => (lineMap.symm l, false)
  left_inv := by
    intro u
    rcases u with ⟨p, s⟩
    cases s <;> simp
  right_inv := by
    intro v
    cases v with
    | inl p => rfl
    | inr l => simp

/-- Natural-number adjacency of a bipartite incidence graph. -/
def incidenceGraphAdj {Point Line : Type}
    [Fintype Point] [DecidableEq Point] [Fintype Line] [DecidableEq Line]
    (incident : Point → Line → Prop) [DecidableRel incident] :
    (Point ⊕ Line) → (Point ⊕ Line) → ℕ
  | Sum.inl p, Sum.inr l => incidenceWeight incident p l
  | Sum.inr l, Sum.inl p => incidenceWeight incident p l
  | Sum.inl _, Sum.inl _ => 0
  | Sum.inr _, Sum.inr _ => 0

/-- The exact signed-corner statement that a table link is an incidence graph.
The two negative signs are represented by line labels through `lineMap`. -/
def CornerIncidenceTable {Point Line TriangleIndex : Type}
    [Fintype Point] [DecidableEq Point] [Fintype Line] [DecidableEq Line]
    [Fintype TriangleIndex] [DecidableEq TriangleIndex]
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Point)
    (incident : Point → Line → Prop) [DecidableRel incident]
    (lineMap : Point ≃ Line) : Prop :=
  ∀ x y s t,
    TriangularHodgeLayer.adjacencyCount T (x, s) (y, t) =
      if s then (if t then 0 else incidenceWeight incident x (lineMap y))
      else (if t then incidenceWeight incident y (lineMap x) else 0)

/-- The signed link equivalence preserves adjacency.  This is the graph
isomorphism theorem in the natural-number interface. -/
theorem presentationLink_isomorphic_to_incidence
    {Point Line TriangleIndex : Type}
    [Fintype Point] [DecidableEq Point] [Fintype Line] [DecidableEq Line]
    [Fintype TriangleIndex] [DecidableEq TriangleIndex]
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Point)
    (incident : Point → Line → Prop) [DecidableRel incident]
    (lineMap : Point ≃ Line) (h : CornerIncidenceTable T incident lineMap) :
    ∀ u v,
      TriangularHodgeLayer.adjacencyCount T u v =
        incidenceGraphAdj incident (signedVertexEquiv lineMap u)
          (signedVertexEquiv lineMap v) := by
  intro u v
  rcases u with ⟨x, s⟩
  rcases v with ⟨y, t⟩
  have hxy := h x y
  norm_num [CornerIncidenceTable] at hxy
  cases s with
  | false =>
      cases t with
      | false =>
          simpa [incidenceGraphAdj, signedVertexEquiv] using hxy.1.1
      | true =>
          simpa [incidenceGraphAdj, signedVertexEquiv] using hxy.1.2
  | true =>
      cases t with
      | false =>
          simpa [incidenceGraphAdj, signedVertexEquiv] using hxy.2.1
      | true =>
          simpa [incidenceGraphAdj, signedVertexEquiv] using hxy.2.2

/-! ## Counts and the exact order-eight certificate -/

/-- A generalized-quadrangle count package identifies the presentation link
with its incidence graph.  Taking `G` to be the certified algebraic W(8)
package gives the requested 585-point/585-line identification. -/
theorem generalizedQuadrangleCounts_identify_presentation_link
    {Point Line TriangleIndex : Type}
    [Fintype Point] [DecidableEq Point] [Fintype Line] [DecidableEq Line]
    [Fintype TriangleIndex] [DecidableEq TriangleIndex]
    (G : GeneralizedQuadrangleCounts Point Line)
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Point)
    (lineMap : Point ≃ Line)
    (h : CornerIncidenceTable T G.incident lineMap) :
    ∃ e : (Point × Bool) ≃ G.Vertex,
      ∀ u v, (TriangularHodgeLayer.adjacencyCount T u v : ℚ) =
        G.adj (e u) (e v) := by
  refine ⟨signedVertexEquiv lineMap, ?_⟩
  intro u v
  have hlink := presentationLink_isomorphic_to_incidence T G.incident lineMap h u v
  rcases u with ⟨x, s⟩
  rcases v with ⟨y, t⟩
  cases s <;> cases t <;>
    simpa [incidenceGraphAdj, GeneralizedQuadrangleCounts.adj,
      signedVertexEquiv] using congrArg (fun n : ℕ => (n : ℚ)) hlink

/-- Specializing the preceding count identification to order eight and the
exact `mu=4` construction transfers the gap-`5/9` Gram certificate.  The
proof is symbolic in `G`, so it never enumerates the link. -/
theorem girthEightSDPChecks_of_orderEight_link_identification
    {Point Line TriangleIndex : Type}
    [Fintype Point] [DecidableEq Point] [Fintype Line] [DecidableEq Line]
    [Fintype TriangleIndex] [DecidableEq TriangleIndex] [Nonempty Point]
    (G : GeneralizedQuadrangleCounts Point Line) (horder : G.order = 8)
    {T : TriangleIndex → TriangularHodgeLayer.Triangle Point}
    (hgeom : GirthEightChecks T 9)
    (lineMap : Point ≃ Line)
    (h : CornerIncidenceTable T G.incident lineMap) :
    GirthEightSDPChecks T 9 (5 / 9)
      (QuadrangleLinkData.reindex
        (G.toQuadrangleLinkDataEight horder) (signedVertexEquiv lineMap)).gramRow := by
  let Q := G.toQuadrangleLinkDataEight horder
  let I : TriangleLinkIdentification T Q := {
    vertexEquiv := signedVertexEquiv lineMap
    adjacency_eq := by
      intro u v
      have hlink := presentationLink_isomorphic_to_incidence T G.incident lineMap h u v
      rcases u with ⟨x, s⟩
      rcases v with ⟨y, t⟩
      cases s <;> cases t <;>
        simpa [incidenceGraphAdj, GeneralizedQuadrangleCounts.adj,
          signedVertexEquiv, Q,
          GeneralizedQuadrangleCounts.toQuadrangleLinkDataEight,
          GeneralizedQuadrangleCounts.toQuadrangleLinkData]
          using congrArg (fun n : ℕ => (n : ℚ)) hlink }
  have hdeg : (9 : ℚ) = Q.deg := by
    norm_num [Q, QuadrangleLinkData.deg,
      GeneralizedQuadrangleCounts.toQuadrangleLinkDataEight,
      GeneralizedQuadrangleCounts.toQuadrangleLinkData]
    rw [horder]
    norm_num
  have hc := girthEightSDPChecks_of_linkIdentification T hgeom Q I hdeg
  have hgap : Q.gapValue = 5 / 9 := by
    norm_num [Q, QuadrangleLinkData.gapValue, QuadrangleLinkData.contraction,
      QuadrangleLinkData.deg,
      GeneralizedQuadrangleCounts.toQuadrangleLinkDataEight,
      GeneralizedQuadrangleCounts.toQuadrangleLinkData]
    rw [horder]
    norm_num
  have hc' : GirthEightSDPChecks T 9 (5 / 9)
      (QuadrangleLinkData.reindex Q (signedVertexEquiv lineMap)).gramRow := by
    simpa [I, TriangleLinkIdentification.reindexed, Q,
      QuadrangleLinkData.reindex_gapValue, hgap] using hc
  exact hc'

/-! ## The concrete W(8) theorem -/

/-- The algebraic symplectic quadrangle `W(8)` supplies the exact degree-nine
link data and its `5/9` gap.  The only table-specific input is the signed
corner incidence identity; the proof consumes ko's committed
`wEightCounts`/`wEightQuadrangleLinkData` definitions and does not enumerate
the `1170` signed link vertices. -/
theorem girthEightSDPChecks_of_wEight_link_identification
    {TriangleIndex : Type}
    [Fintype TriangleIndex] [DecidableEq TriangleIndex]
    {T : TriangleIndex →
      TriangularHodgeLayer.Triangle SymplecticQuadrangle.Point}
    (hgeom : GirthEightChecks T 9)
    (lineMap : SymplecticQuadrangle.Point ≃ SymplecticQuadrangle.Line)
    (h : CornerIncidenceTable T SymplecticQuadrangle.Incident lineMap) :
    GirthEightSDPChecks T 9 (5 / 9)
      (QuadrangleLinkData.reindex
        _root_.GroupApproximation.KazhdanHyp.SymplecticQuadrangle.wEightQuadrangleLinkData
        (signedVertexEquiv lineMap)).gramRow := by
  simpa [_root_.GroupApproximation.KazhdanHyp.SymplecticQuadrangle.wEightQuadrangleLinkData] using
    (girthEightSDPChecks_of_orderEight_link_identification
      _root_.GroupApproximation.KazhdanHyp.SymplecticQuadrangle.wEightCounts
      (by rfl) hgeom lineMap h)

/-! ## Singer row reduction -/

/-- For an equivariant table, positivity of only the 27 representative rows
implies positivity of every row.  The remaining link checks are supplied by
the W(8) identification (or by the corresponding Singer pair-root theorem). -/
theorem positiveRows_of_singer_representatives
    {Generator TriangleIndex TriangleRep : Type}
    [Fintype Generator] [DecidableEq Generator]
    [Fintype TriangleIndex] [DecidableEq TriangleIndex] [Fintype TriangleRep]
    (sigma : Equiv.Perm Generator) (tau : Equiv.Perm TriangleIndex)
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (hT : TriangleEquivariant sigma tau T)
    (triangleCover : CyclicOrbitCover tau TriangleRep)
    (hrows : Fintype.card TriangleRep = 27 ∧
      ∀ r k, (T (triangleCover.root r) k).2 = true) :
    ∀ j k, (T j k).2 = true := by
  exact triangleCover.forall_of_representatives
    (P := fun j => ∀ k, (T j k).2 = true)
    (by
      intro j hj k
      rw [hT j k]
      exact hj k)
      hrows.2

/-- A Singer-equivariant W(8) table needs positivity only on its `27` stored
triangle-orbit rows.  Replacing the positivity component of `hgeom` with
those representatives and applying the concrete W(8) transfer yields the
gap-`5/9` SDP certificate outright.  The other four girth/link clauses in
`hgeom` are the geometric checks supplied by the existing girth-eight
pipeline; no `1170`-vertex link enumeration occurs here. -/
theorem girthEightSDPChecks_of_singerRows_wEight
    {TriangleIndex TriangleRep : Type}
    [Fintype TriangleIndex] [DecidableEq TriangleIndex]
    [Fintype TriangleRep]
    {T : TriangleIndex →
      TriangularHodgeLayer.Triangle SymplecticQuadrangle.Point}
    (sigma : Equiv.Perm SymplecticQuadrangle.Point)
    (tau : Equiv.Perm TriangleIndex)
    (hT : TriangleEquivariant sigma tau T)
    (triangleCover : CyclicOrbitCover tau TriangleRep)
    (hrows : Fintype.card TriangleRep = 27 ∧
      ∀ r k, (T (triangleCover.root r) k).2 = true)
    (hgeom : GirthEightChecks T 9)
    (lineMap : SymplecticQuadrangle.Point ≃ SymplecticQuadrangle.Line)
    (h : CornerIncidenceTable T SymplecticQuadrangle.Incident lineMap) :
    GirthEightSDPChecks T 9 (5 / 9)
      (QuadrangleLinkData.reindex
        _root_.GroupApproximation.KazhdanHyp.SymplecticQuadrangle.wEightQuadrangleLinkData
        (signedVertexEquiv lineMap)).gramRow := by
  have hpositive := positiveRows_of_singer_representatives
    sigma tau T hT triangleCover hrows
  rcases hgeom with ⟨_, htail⟩
  exact girthEightSDPChecks_of_wEight_link_identification
    ⟨hpositive, htail⟩ lineMap h

/-! ## A published small model -/

/-- Model test on ko's transcribed `GQ(2,2)` table.  No algebraic `W(2)`
instance is present, so this checks the abstract signed-incidence interface. -/
def gqTwoIncident : Fin 15 → Fin 15 → Prop :=
  fun x y => y = GQTwoTable.neighbor x 0 ∨
    y = GQTwoTable.neighbor x 1 ∨ y = GQTwoTable.neighbor x 2

instance gqTwoIncidentDecidable : DecidableRel gqTwoIncident := by
  intro x y
  unfold gqTwoIncident
  infer_instance

theorem gqTwo_cornerIncidence_model :
    CornerIncidenceTable GQTwoTable.triangles gqTwoIncident
      (Equiv.refl (Fin 15)) := by
  intro x y s t
  change TriangularHodgeLayer.adjacencyCount GQTwoTable.triangles (x, s) (y, t) =
    if s then (if t then 0 else GQTwoTable.incidence x y)
    else (if t then GQTwoTable.incidence y x else 0)
  exact GQTwoTable.adjacency_eq_incidence x y s t

/-- The GQ(2,2) model has the same hypothesis shape as the concrete theorem:
literal positivity together with a signed corner/incidence identification.
It is an abstract-interface model because this repository has no algebraic
`W(2)` counts package. -/
theorem gqTwo_singerRows_hypothesis_shape_model :
    (∀ j k, (GQTwoTable.triangles j k).2 = true) ∧
      CornerIncidenceTable GQTwoTable.triangles gqTwoIncident
        (Equiv.refl (Fin 15)) := by
  exact ⟨GQTwoTable.positive, gqTwo_cornerIncidence_model⟩

end KazhdanHyp
end GroupApproximation
