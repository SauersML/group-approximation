import GroupApproximation.GGT.KazhdanHypGQScheme
import GroupApproximation.GGT.KazhdanHypSingerReduction

/-!
# Transporting a generalized-quadrangle certificate to a triangle table

The rational Gram factor in `KazhdanHypQuadrangle` is indexed by the abstract
vertices of a generalized-quadrangle incidence graph.  A triangle table is
indexed by signed generators.  This module reindexes all association-scheme
data along an equivalence and proves that equality of the two adjacency
tables gives `GirthEightSDPChecks` for the literal triangle table.

For a Singer-equivariant table, adjacency agreement need only be checked on
representatives of simultaneous signed-vertex-pair orbits.  The remaining
pairs follow from table equivariance, equivariance of the link
identification, and invariance of the algebraic quadrangle adjacency table.
This is the kernel-small bridge used by a generated W(8) witness.
-/

namespace GroupApproximation
namespace KazhdanHyp

open scoped BigOperators

universe u v

namespace QuadrangleLinkData

variable {U : Type u} {V : Type v}
  [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]

/-- Reindex quadrangle link data along an equivalence of finite vertex types. -/
def reindex (Q : QuadrangleLinkData V) (e : U ≃ V) : QuadrangleLinkData U where
  adj u w := Q.adj (e u) (e w)
  col u w := Q.col (e u) (e w)
  sign u := Q.sign (e u)
  ord := Q.ord
  mu := Q.mu
  adj_symm u w := Q.adj_symm (e u) (e w)
  col_symm u w := Q.col_symm (e u) (e w)
  sign_sq u := Q.sign_sq (e u)
  sign_sum := by
    exact (Equiv.sum_comp e Q.sign).trans Q.sign_sum
  adj_col_sum u := by
    exact (Equiv.sum_comp e (fun w ↦ Q.adj w (e u))).trans
      (Q.adj_col_sum (e u))
  adj_sign u := by
    exact (Equiv.sum_comp e
      (fun w ↦ Q.adj w (e u) * Q.sign w)).trans
      (Q.adj_sign (e u))
  col_col_sum u := by
    exact (Equiv.sum_comp e (fun w ↦ Q.col w (e u))).trans
      (Q.col_col_sum (e u))
  col_sign u := by
    exact (Equiv.sum_comp e
      (fun w ↦ Q.col w (e u) * Q.sign w)).trans
      (Q.col_sign (e u))
  adj_square u w := by
    have hsum := Equiv.sum_comp e
      (fun x ↦ Q.adj x (e u) * Q.adj x (e w))
    rw [hsum, Q.adj_square]
    simp only [e.injective.eq_iff]
  col_square u w := by
    have hsum := Equiv.sum_comp e
      (fun x ↦ Q.col x (e u) * Q.col x (e w))
    rw [hsum, Q.col_square]
    simp only [e.injective.eq_iff]
  card_eq := by
    rw [Fintype.card_congr e]
    exact Q.card_eq
  ord_pos := Q.ord_pos
  mu_pos := Q.mu_pos
  mu_bound := Q.mu_bound

@[simp]
theorem reindex_adj (Q : QuadrangleLinkData V) (e : U ≃ V) (u w : U) :
    (Q.reindex e).adj u w = Q.adj (e u) (e w) :=
  rfl

/-- Reindexing transports the link gap without changing its value. -/
@[simp]
theorem reindex_gapValue (Q : QuadrangleLinkData V) (e : U ≃ V) :
    (Q.reindex e).gapValue = Q.gapValue :=
  rfl

/-- The reindexed Gram rows are definitionally the Gram rows constructed from
the transported association scheme. -/
noncomputable def reindexedGramRow (Q : QuadrangleLinkData V) (e : U ≃ V) :
    QuadRow U → U → ℚ :=
  (Q.reindex e).gramRow

end QuadrangleLinkData

section Table

variable {Generator TriangleIndex : Type}
  [Fintype Generator] [DecidableEq Generator] [Nonempty Generator]
  [Fintype TriangleIndex] [DecidableEq TriangleIndex]

/-- A literal triangle table has the same weighted link as an abstract
quadrangle incidence graph.  The equivalence is the vertex map of the link
isomorphism; `adjacency_eq` is the edge-preservation clause.  Stating the
isomorphism at the rational weight level is exactly what the certificate
consumer reads, while avoiding a second Boolean adjacency encoding. -/
structure TriangleLinkIdentification
    {V : Type} [Fintype V] [DecidableEq V]
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (Q : QuadrangleLinkData V) where
  vertexEquiv : (Generator × Bool) ≃ V
  adjacency_eq : ∀ u w,
    (TriangularHodgeLayer.adjacencyCount T u w : ℚ) =
      Q.adj (vertexEquiv u) (vertexEquiv w)

namespace TriangleLinkIdentification

variable {V : Type} [Fintype V] [DecidableEq V]
  {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}
  {Q : QuadrangleLinkData V}

/-- The identification reindexes the quadrangle link data onto signed
generators, preserving its degree, Gram row, and rational gap. -/
noncomputable def reindexed (I : TriangleLinkIdentification T Q) :
    QuadrangleLinkData (Generator × Bool) :=
  Q.reindex I.vertexEquiv

omit [Nonempty Generator] [DecidableEq TriangleIndex] in
theorem adjacency_eq_reindexed (I : TriangleLinkIdentification T Q) (u w) :
    (TriangularHodgeLayer.adjacencyCount T u w : ℚ) =
      (I.reindexed.adj u w) :=
  I.adjacency_eq u w

end TriangleLinkIdentification

/-- An adjacency-preserving identification with a quadrangle link transfers
its exact rational Gram identity to `GirthEightSDPChecks` for the table. -/
theorem girthEightSDPChecks_of_quadrangleEquiv
    {V : Type} [Fintype V] [DecidableEq V]
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    {d : ℕ} (hgeom : GirthEightChecks T d)
    (Q : QuadrangleLinkData V)
    (e : (Generator × Bool) ≃ V)
    (hdegval : (d : ℚ) = Q.deg)
    (hadj : ∀ u w,
      (TriangularHodgeLayer.adjacencyCount T u w : ℚ) =
      Q.adj (e u) (e w)) :
    GirthEightSDPChecks T d (Q.reindex e).gapValue
      (Q.reindex e).gramRow := by
  let R : QuadrangleLinkData (Generator × Bool) := Q.reindex e
  have hkgon := R.linkCertificateChecks_kgon_of_quadrangle T d hdegval
    (by
      intro u w
      exact hadj u w)
  have hlink := linkCertificateChecks_of_kgonChecks_three
    T d R.gapValue R.gramRow hgeom.regular hkgon
  exact ⟨hlink.1, hlink.2.1, hlink.2.2.2⟩

/-- A link isomorphism in the preceding sense is sufficient for the exact
certificate transfer. -/
theorem girthEightSDPChecks_of_linkIdentification
    {V : Type} [Fintype V] [DecidableEq V]
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    {d : ℕ} (hgeom : GirthEightChecks T d)
    (Q : QuadrangleLinkData V)
    (I : TriangleLinkIdentification T Q)
    (hdegval : (d : ℚ) = Q.deg) :
    GirthEightSDPChecks T d I.reindexed.gapValue I.reindexed.gramRow := by
  exact girthEightSDPChecks_of_quadrangleEquiv T hgeom Q I.vertexEquiv
    hdegval I.adjacency_eq

/-! ## Singer reduction for the link identification -/

/-- Equivariance data relating the signed-generator Singer action to an
automorphism of an algebraic link. -/
structure SingerLinkEquivariance
    {V : Type} [Fintype V] [DecidableEq V]
    (sigma : Equiv.Perm Generator)
    (Q : QuadrangleLinkData V)
    (e : (Generator × Bool) ≃ V) where
  /-- The corresponding algebraic link automorphism. -/
  rho : Equiv.Perm V
  /-- The vertex identification intertwines the two actions. -/
  intertwines : ∀ u, e (signedPerm sigma u) = rho (e u)
  /-- The quadrangle adjacency table is invariant under the automorphism. -/
  adj_invariant : ∀ x y, Q.adj (rho x) (rho y) = Q.adj x y

namespace SingerLinkEquivariance

variable {V Rep : Type} [Fintype V] [DecidableEq V]
  (sigma : Equiv.Perm Generator)
  (Q : QuadrangleLinkData V)
  (e : (Generator × Bool) ≃ V)

omit [Nonempty Generator] in
/-- Agreement on simultaneous signed-pair orbit representatives implies
agreement on every pair.  Thus the large table never needs a quadratic
kernel enumeration. -/
theorem adjacency_eq_of_pairOrbitRoots
    [Fintype Rep]
    (tau : Equiv.Perm TriangleIndex)
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (hT : TriangleEquivariant sigma tau T)
    (S : SingerLinkEquivariance sigma Q e)
    (cover : CyclicOrbitCover (signedPairPerm sigma) Rep)
    (hroot : ∀ r,
      (TriangularHodgeLayer.adjacencyCount T
        (cover.root r).1 (cover.root r).2 : ℚ) =
        Q.adj (e (cover.root r).1) (e (cover.root r).2)) :
    ∀ u w,
      (TriangularHodgeLayer.adjacencyCount T u w : ℚ) =
        Q.adj (e u) (e w) := by
  let P := fun z : (Generator × Bool) × (Generator × Bool) ↦
    (TriangularHodgeLayer.adjacencyCount T z.1 z.2 : ℚ) =
      Q.adj (e z.1) (e z.2)
  have hstep : ∀ z, P z → P (signedPairPerm sigma z) := by
    rintro ⟨u, w⟩ huw
    change (TriangularHodgeLayer.adjacencyCount T
      (signedPerm sigma u) (signedPerm sigma w) : ℚ) =
        Q.adj (e (signedPerm sigma u)) (e (signedPerm sigma w))
    rw [adjacencyCount_signedPerm hT, S.2 u,
      S.2 w, S.3, huw]
  have hall : ∀ z, P z := cover.forall_of_representatives hstep hroot
  intro u w
  exact hall (u, w)

/-- Pair-root agreement and a checked Singer-equivariant table produce the
exact rational SDP certificate with no full adjacency-table evaluation. -/
theorem girthEightSDPChecks_of_singerPairRoots
    [Fintype Rep]
    (tau : Equiv.Perm TriangleIndex)
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    {d : ℕ} (hgeom : GirthEightChecks T d)
    (hT : TriangleEquivariant sigma tau T)
    (S : SingerLinkEquivariance sigma Q e)
    (cover : CyclicOrbitCover (signedPairPerm sigma) Rep)
    (hroot : ∀ r,
      (TriangularHodgeLayer.adjacencyCount T
        (cover.root r).1 (cover.root r).2 : ℚ) =
        Q.adj (e (cover.root r).1) (e (cover.root r).2))
    (hdegval : (d : ℚ) = Q.deg) :
    GirthEightSDPChecks T d (Q.reindex e).gapValue
      (Q.reindex e).gramRow :=
  girthEightSDPChecks_of_quadrangleEquiv T hgeom Q e hdegval
    (adjacency_eq_of_pairOrbitRoots sigma Q e tau T hT S cover hroot)

end SingerLinkEquivariance

end Table
end KazhdanHyp
end GroupApproximation
