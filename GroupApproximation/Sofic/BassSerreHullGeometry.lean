import GroupApproximation.Algebra.BassSerreFreeProductAction
import GroupApproximation.Sofic.HullSuitabilityGeometry

/-!
# The Bass--Serre tree as Hull's metric action

This module equips the already-constructed Bass--Serre coset tree with its
real-valued path metric and connects left translation to
`HullGeometry.IsIsometricAction`.  A type synonym keeps this metric instance
local to the Hull-facing interface.
-/

namespace GroupApproximation
namespace BassSerreHullGeometry

open BassSerreFreeProduct

universe u

variable (G : Type u) [Group G]

/-- Bass--Serre vertices carrying the real path metric. -/
def PathVertex := BassSerreFreeProduct.Vertex G

instance pathVertexMulAction :
    MulAction (BassSerreFreeProduct.Ambient G) (PathVertex G) :=
  BassSerreFreeProduct.vertexMulAction G

/-- The graph distance, cast to `ℝ`. -/
noncomputable instance pathVertexMetricSpace :
    MetricSpace (PathVertex G) where
  dist x y := ((BassSerreFreeProduct.graph G).dist x y : ℝ)
  dist_self x := by simp
  dist_comm x y := by
    exact_mod_cast SimpleGraph.dist_comm
      (G := BassSerreFreeProduct.graph G) (u := x) (v := y)
  dist_triangle x y z := by
    exact_mod_cast (BassSerreFreeProduct.graph_connected G).dist_triangle
      (u := x) (v := y) (w := z)
  eq_of_dist_eq_zero x y hxy := by
    have hxy' : (BassSerreFreeProduct.graph G).dist x y = 0 := by
      exact_mod_cast hxy
    exact (BassSerreFreeProduct.graph_connected G).dist_eq_zero_iff.mp hxy'

@[simp] theorem pathVertex_dist (x y : PathVertex G) :
    dist x y = ((BassSerreFreeProduct.graph G).dist x y : ℝ) := rfl

/-- Left translation preserves graph distance. -/
theorem graph_dist_smul (a : BassSerreFreeProduct.Ambient G)
    (x y : BassSerreFreeProduct.Vertex G) :
    (BassSerreFreeProduct.graph G).dist (a • x) (a • y) =
      (BassSerreFreeProduct.graph G).dist x y := by
  apply Nat.le_antisymm
  · obtain ⟨p, hp⟩ :=
      (BassSerreFreeProduct.graph_connected G).exists_walk_length_eq_dist x y
    calc
      (BassSerreFreeProduct.graph G).dist (a • x) (a • y) ≤
          (p.map (BassSerreFreeProduct.actionHom G a)).length :=
        SimpleGraph.dist_le _
      _ = p.length := by simp
      _ = (BassSerreFreeProduct.graph G).dist x y := hp
  · obtain ⟨p, hp⟩ :=
      (BassSerreFreeProduct.graph_connected G).exists_walk_length_eq_dist
        (a • x) (a • y)
    have hle : (BassSerreFreeProduct.graph G).dist
        (a⁻¹ • (a • x)) (a⁻¹ • (a • y)) ≤ p.length := by
      exact SimpleGraph.dist_le
        (p.map (BassSerreFreeProduct.actionHom G a⁻¹))
    simpa only [inv_smul_smul, hp] using hle

/-- **The Bass--Serre path-metric action is isometric.** -/
theorem isIsometricAction :
    HullGeometry.IsIsometricAction
      (BassSerreFreeProduct.Ambient G) (PathVertex G) := by
  intro a x y
  exact_mod_cast graph_dist_smul G a x y

/-- The path-metric action is faithful: an element fixing every vertex fixes
both endpoints of the base edge, whose pointwise stabilizer is trivial. -/
theorem eq_one_of_smul_eq_all (a : BassSerreFreeProduct.Ambient G)
    (ha : ∀ x : PathVertex G, a • x = x) : a = 1 := by
  apply (BassSerreFreeProduct.smul_baseEdge_eq_iff G a).mp
  apply Prod.ext
  · exact ha (BassSerreFreeProduct.baseLeft G)
  · exact ha (BassSerreFreeProduct.baseRight G)

/-- Adjacent vertices have real path distance one. -/
theorem dist_eq_one_of_adj {x y : PathVertex G}
    (hxy : (BassSerreFreeProduct.graph G).Adj x y) : dist x y = 1 := by
  rw [pathVertex_dist, SimpleGraph.dist_eq_one_iff_adj.mpr hxy]
  norm_num

/-- In a tree every simple path is the geodesic between its endpoints.  This
small interface lemma is useful here because Mathlib's graph metric only
states the converse (`length = dist` implies `IsPath`) directly. -/
theorem length_eq_graph_dist_of_isPath {x y : PathVertex G}
    (p : (BassSerreFreeProduct.graph G).Walk x y) (hp : p.IsPath) :
    p.length = (BassSerreFreeProduct.graph G).dist x y := by
  obtain ⟨q, hq, hqlength⟩ :=
    (BassSerreFreeProduct.graph_connected G).exists_path_of_dist x y
  have hpq : p = q := congrArg Subtype.val
    ((BassSerreFreeProduct.graph_isAcyclic G).path_unique ⟨p, hp⟩ ⟨q, hq⟩)
  simpa [hpq] using hqlength

/-- An element fixing both endpoints of an edge is the identity.  This is the
sharp zero-error case of the long-segment rigidity argument. -/
theorem eq_one_of_fixes_adjacent {x y : PathVertex G}
    (hxy : (BassSerreFreeProduct.graph G).Adj x y)
    {a : BassSerreFreeProduct.Ambient G}
    (hx : a • x = x) (hy : a • y = y) : a = 1 := by
  have ha : a ∈ MulAction.stabilizer
      (BassSerreFreeProduct.Ambient G) (x, y) := by
    rw [MulAction.mem_stabilizer_iff]
    exact Prod.ext hx hy
  rw [BassSerreFreeProduct.adjacentPair_pointwiseStabilizer_eq_bot G hxy] at ha
  simpa using ha

/-- Fixing two distinct vertices of the Bass--Serre tree forces an element to
be the identity.  Uniqueness of the path makes the element fix its first edge,
where the algebraic edge-stabilizer computation applies. -/
theorem eq_one_of_fixes_distinct {x y : PathVertex G} (hxy : x ≠ y)
    {a : BassSerreFreeProduct.Ambient G}
    (hx : a • x = x) (hy : a • y = y) : a = 1 := by
  obtain ⟨p, hp⟩ :=
    (BassSerreFreeProduct.graph_isTree G).existsUnique_path x y
  let p' : (BassSerreFreeProduct.graph G).Walk x y :=
    (p.map (BassSerreFreeProduct.actionHom G a)).copy hx hy
  have hp' : p'.IsPath := by
    dsimp [p']
    exact (hp.map (BassSerreFreeProduct.actionHom G a)).copy
  have heq : p = p' := congrArg Subtype.val
    ((BassSerreFreeProduct.graph_isAcyclic G).path_unique ⟨p, hp⟩ ⟨p', hp'⟩)
  cases p with
  | nil => exact (hxy rfl).elim
  | @cons x z y hxz q =>
      have hs := congrArg SimpleGraph.Walk.support heq
      have htail := congrArg List.tail hs
      have hhead := congrArg List.head? htail
      have hz : a • z = z := by
        simpa [p', SimpleGraph.Walk.support_map] using hhead
      exact eq_one_of_fixes_adjacent G hxz hx hz

/-- The simultaneous exact-displacement set at the endpoints of an edge is
the singleton identity.  This packages both finiteness and the optimal count
without any local-finiteness hypothesis on the tree. -/
theorem exactEdgeDisplacement_eq_singleton {x y : PathVertex G}
    (hxy : (BassSerreFreeProduct.graph G).Adj x y) :
    {a : BassSerreFreeProduct.Ambient G | a • x = x ∧ a • y = y} = {1} := by
  ext a
  constructor
  · intro ha
    have : a = 1 := eq_one_of_fixes_adjacent G hxy ha.1 ha.2
    simpa [this]
  · intro ha
    have : a = 1 := by simpa using ha
    subst a
    simp

/-- Consequently the exact-displacement set on an edge has cardinality one. -/
theorem exactEdgeDisplacement_ncard {x y : PathVertex G}
    (hxy : (BassSerreFreeProduct.graph G).Adj x y) :
    {a : BassSerreFreeProduct.Ambient G | a • x = x ∧ a • y = y}.ncard = 1 := by
  rw [exactEdgeDisplacement_eq_singleton G hxy]
  simp

end BassSerreHullGeometry
end GroupApproximation
