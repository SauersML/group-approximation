import GroupApproximation.Algebra.BassSerreFreeProductAction
import GroupApproximation.Sofic.HullSuitabilityGeometry
import Mathlib.Data.List.NodupEquivFin

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

/-- A sufficiently central entry of a sublist of `left ++ middle ++ right`
must come from `middle`.  This is the finite-list core of the tree-overlap
argument: bypassing can delete at most the two short end pieces before it
reaches a central edge. -/
private theorem mem_middle_of_sublist {A : Type*}
    {l left middle right : List A} (hsub : l <+ left ++ middle ++ right)
    {i : ℕ} (hi : i < l.length) (hleft : left.length ≤ i)
    (hright : right.length < l.length - i) : l[i] ∈ middle := by
  obtain ⟨f, hf⟩ := List.sublist_iff_exists_orderEmbedding_getElem?_eq.mp hsub
  have hilast : i ≤ l.length - 1 := by omega
  have hlast : f (l.length - 1) < (left ++ middle ++ right).length := by
    have hlastlt : l.length - 1 < l.length := by omega
    have h := hf (l.length - 1)
    rw [List.getElem?_eq_getElem hlastlt, eq_comm,
      List.getElem?_eq_some_iff] at h
    exact h.1
  have hfLower : i ≤ f i := f.strictMono.id_le i
  have hfSpacing : (l.length - 1 - i) + f i ≤ f (l.length - 1) := by
    have h := f.strictMono.add_le_nat (l.length - 1 - i) i
    simpa [Nat.sub_add_cancel hilast] using h
  have hmiddleLower : left.length ≤ f i := hleft.trans hfLower
  have hmiddleUpper : f i < left.length + middle.length := by
    simp only [List.length_append] at hlast
    omega
  have hopt := hf i
  rw [List.getElem?_eq_getElem hi] at hopt
  have hidx : f i - left.length < middle.length := by omega
  have hmidopt : middle[f i - left.length]? = some l[i] := by
    rw [eq_comm] at hopt
    simpa [List.getElem?_append, hmiddleLower.not_lt, hidx] using hopt
  rw [List.getElem?_eq_some_iff] at hmidopt
  rw [← hmidopt.2]
  exact List.getElem_mem hidx

/-- The `i`-th undirected edge of a walk joins its `i`-th and `(i+1)`-st
vertices. -/
private theorem edges_getElem_eq_getVert {V : Type*} {H : SimpleGraph V}
    {x y : V} (p : H.Walk x y) (i : ℕ) (hi : i < p.length) :
    p.edges[i]'(by simpa only [SimpleGraph.Walk.length_edges] using hi) =
      s(p.getVert i, p.getVert (i + 1)) := by
  induction p generalizing i with
  | nil => omega
  | @cons x z y hxz q ih =>
      cases i with
      | zero => simp
      | succ i =>
          simp only [SimpleGraph.Walk.length_cons, Nat.add_lt_add_iff_right] at hi
          simpa [Nat.succ_eq_add_one, Nat.add_assoc] using ih i hi

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

/-- The canonical (choice of the unique) combinatorial geodesic. -/
noncomputable def geodesic (x y : PathVertex G) :
    (BassSerreFreeProduct.graph G).Walk x y :=
  Classical.choose
    ((BassSerreFreeProduct.graph_connected G).exists_path_of_dist x y)

theorem geodesic_isPath (x y : PathVertex G) : (geodesic G x y).IsPath :=
  (Classical.choose_spec
    ((BassSerreFreeProduct.graph_connected G).exists_path_of_dist x y)).1

@[simp] theorem geodesic_length (x y : PathVertex G) :
    (geodesic G x y).length = (BassSerreFreeProduct.graph G).dist x y :=
  (Classical.choose_spec
    ((BassSerreFreeProduct.graph_connected G).exists_path_of_dist x y)).2

/-- The vertex with index `i` on the canonical geodesic is exactly distance
`i` from its initial endpoint, as long as `i` is in range. -/
theorem graph_dist_getVert_geodesic {x y : PathVertex G} {i : ℕ}
    (hi : i ≤ (BassSerreFreeProduct.graph G).dist x y) :
    (BassSerreFreeProduct.graph G).dist x ((geodesic G x y).getVert i) = i := by
  let q := (geodesic G x y).take i
  have hq : q.IsPath := (geodesic_isPath G x y).take i
  have hlength : q.length = i := by
    dsimp [q]
    rw [SimpleGraph.Walk.take_length, geodesic_length, min_eq_left hi]
  rw [← length_eq_graph_dist_of_isPath G q hq, hlength]

/-- Consecutive in-range vertices of the canonical geodesic form an edge. -/
theorem geodesic_getVert_adj {x y : PathVertex G} {i : ℕ}
    (hi : i < (BassSerreFreeProduct.graph G).dist x y) :
    (BassSerreFreeProduct.graph G).Adj
      ((geodesic G x y).getVert i) ((geodesic G x y).getVert (i + 1)) := by
  apply SimpleGraph.Walk.adj_getVert_succ
  simpa only [geodesic_length] using hi

/-- A vertex of a tree geodesic is determined by its distance from the first
endpoint. -/
theorem eq_of_mem_geodesic_of_graph_dist_eq {x y z w : PathVertex G}
    (hz : z ∈ (geodesic G x y).support)
    (hw : w ∈ (geodesic G x y).support)
    (hd : (BassSerreFreeProduct.graph G).dist x z =
      (BassSerreFreeProduct.graph G).dist x w) : z = w := by
  rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hz hw
  obtain ⟨i, rfl, hi⟩ := hz
  obtain ⟨j, rfl, hj⟩ := hw
  have hi' : i ≤ (BassSerreFreeProduct.graph G).dist x y := by
    simpa only [geodesic_length] using hi
  have hj' : j ≤ (BassSerreFreeProduct.graph G).dist x y := by
    simpa only [geodesic_length] using hj
  rw [graph_dist_getVert_geodesic G hi', graph_dist_getVert_geodesic G hj'] at hd
  subst j
  rfl

/-- **Central-edge overlap.**  If both endpoints move by at most `k`, then the
`k`-th edge of a geodesic of length at least `2k+1` occurs on the translated
geodesic.  The proof concatenates the two short endpoint geodesics with the
translated geodesic and uses that bypassing this walk must recover the unique
original geodesic.  The list lemma above shows that a central edge cannot have
come from either short end piece. -/
theorem centralEdge_mem_mapped_geodesic {x y : PathVertex G}
    (a : BassSerreFreeProduct.Ambient G) (k : ℕ)
    (hx : (BassSerreFreeProduct.graph G).dist x (a • x) ≤ k)
    (hy : (BassSerreFreeProduct.graph G).dist y (a • y) ≤ k)
    (hxy : 2 * k + 1 ≤ (BassSerreFreeProduct.graph G).dist x y) :
    (geodesic G x y).edges[k]'(by simpa only [geodesic_length] using
      (show k < (BassSerreFreeProduct.graph G).dist x y by omega)) ∈
      ((geodesic G x y).map (BassSerreFreeProduct.actionHom G a)).edges := by
  let p := geodesic G x y
  let r := geodesic G x (a • x)
  let s := geodesic G (a • y) y
  let m := p.map (BassSerreFreeProduct.actionHom G a)
  let W : (BassSerreFreeProduct.graph G).Walk x y := r.append (m.append s)
  have hWpath : W.bypass.IsPath := W.bypass_isPath
  have hbypass : W.bypass = p := congrArg Subtype.val
    ((BassSerreFreeProduct.graph_isAcyclic G).path_unique
      ⟨W.bypass, hWpath⟩ ⟨p, geodesic_isPath G x y⟩)
  have hsub : p.edges <+ r.edges ++ m.edges ++ s.edges := by
    have := W.edges_bypass_sublist_edges
    rw [hbypass] at this
    simpa [W, SimpleGraph.Walk.edges_append] using this
  apply mem_middle_of_sublist hsub
  · simpa only [geodesic_length] using
      (show k < (BassSerreFreeProduct.graph G).dist x y by omega)
  · simpa only [SimpleGraph.Walk.length_edges, geodesic_length] using hx
  · simp only [SimpleGraph.Walk.length_edges, geodesic_length]
    omega

/-- The endpoints of the image of the central edge lie on the original
geodesic.  Apply `centralEdge_mem_mapped_geodesic` to the inverse element and
then undo the inverse action on the two endpoints. -/
theorem smul_central_getVert_mem_geodesic {x y : PathVertex G}
    (a : BassSerreFreeProduct.Ambient G) (k : ℕ)
    (hx : (BassSerreFreeProduct.graph G).dist x (a • x) ≤ k)
    (hy : (BassSerreFreeProduct.graph G).dist y (a • y) ≤ k)
    (hxy : 2 * k + 1 ≤ (BassSerreFreeProduct.graph G).dist x y) :
    a • (geodesic G x y).getVert k ∈ (geodesic G x y).support ∧
      a • (geodesic G x y).getVert (k + 1) ∈ (geodesic G x y).support := by
  let p := geodesic G x y
  have hxinv : (BassSerreFreeProduct.graph G).dist x (a⁻¹ • x) ≤ k := by
    have h := graph_dist_smul G a (a⁻¹ • x) x
    rw [smul_inv_smul] at h
    calc
      (BassSerreFreeProduct.graph G).dist x (a⁻¹ • x) =
          (BassSerreFreeProduct.graph G).dist (a⁻¹ • x) x :=
        SimpleGraph.dist_comm
      _ = (BassSerreFreeProduct.graph G).dist x (a • x) := h.symm
      _ ≤ k := hx
  have hyinv : (BassSerreFreeProduct.graph G).dist y (a⁻¹ • y) ≤ k := by
    have h := graph_dist_smul G a (a⁻¹ • y) y
    rw [smul_inv_smul] at h
    calc
      (BassSerreFreeProduct.graph G).dist y (a⁻¹ • y) =
          (BassSerreFreeProduct.graph G).dist (a⁻¹ • y) y :=
        SimpleGraph.dist_comm
      _ = (BassSerreFreeProduct.graph G).dist y (a • y) := h.symm
      _ ≤ k := hy
  have hedge := centralEdge_mem_mapped_geodesic G a⁻¹ k hxinv hyinv hxy
  have hklt : k < p.length := by
    dsimp [p]
    rw [geodesic_length]
    omega
  have hedge' : s(p.getVert k, p.getVert (k + 1)) ∈
      (p.map (BassSerreFreeProduct.actionHom G a⁻¹)).edges := by
    rw [← edges_getElem_eq_getVert p k hklt]
    exact hedge
  have hu := (p.map (BassSerreFreeProduct.actionHom G a⁻¹)).fst_mem_support_of_mem_edges hedge'
  have hv := (p.map (BassSerreFreeProduct.actionHom G a⁻¹)).snd_mem_support_of_mem_edges hedge'
  rw [SimpleGraph.Walk.support_map] at hu hv
  obtain ⟨u, hu, hua⟩ := List.mem_map.mp hu
  obtain ⟨v, hv, hva⟩ := List.mem_map.mp hv
  constructor
  · have heu : a • p.getVert k = u := by
      rw [← hua]
      exact smul_inv_smul a u
    rwa [heu]
  · have hev : a • p.getVert (k + 1) = v := by
      rw [← hva]
      exact smul_inv_smul a v
    rwa [hev]

/-- Uniform counting for integral endpoint displacement.  The code of a mover
is the pair of distances from `x` to the two endpoints of the translated
central edge.  Central overlap puts both endpoints on the original geodesic,
where distance from `x` determines a vertex.  Equal codes therefore give the
same translated edge, and exact edge rigidity gives the same group element. -/
theorem boundedGraphDisplacement_finite_count (k : ℕ) {x y : PathVertex G}
    (hxy : 2 * k + 1 ≤ (BassSerreFreeProduct.graph G).dist x y) :
    let S : Set (BassSerreFreeProduct.Ambient G) := {a |
      (BassSerreFreeProduct.graph G).dist x (a • x) ≤ k ∧
      (BassSerreFreeProduct.graph G).dist y (a • y) ≤ k}
    S.Finite ∧ S.ncard ≤ (2 * k + 1) * (2 * k + 2) := by
  let p := geodesic G x y
  let u := p.getVert k
  let v := p.getVert (k + 1)
  let S : Set (BassSerreFreeProduct.Ambient G) := {a |
    (BassSerreFreeProduct.graph G).dist x (a • x) ≤ k ∧
    (BassSerreFreeProduct.graph G).dist y (a • y) ≤ k}
  have hku : (BassSerreFreeProduct.graph G).dist x u = k := by
    dsimp [u, p]
    apply graph_dist_getVert_geodesic G
    omega
  have hkv : (BassSerreFreeProduct.graph G).dist x v = k + 1 := by
    dsimp [v, p]
    apply graph_dist_getVert_geodesic G
    omega
  have huv : (BassSerreFreeProduct.graph G).Adj u v := by
    dsimp [u, v, p]
    apply geodesic_getVert_adj G
    omega
  have hmem : ∀ a : S, a.1 • u ∈ p.support ∧ a.1 • v ∈ p.support := by
    intro a
    exact smul_central_getVert_mem_geodesic G a.1 k a.2.1 a.2.2 hxy
  have huBound : ∀ a : S,
      (BassSerreFreeProduct.graph G).dist x (a.1 • u) < 2 * k + 1 := by
    intro a
    have ht := (BassSerreFreeProduct.graph_connected G).dist_triangle
      (u := x) (v := a.1 • x) (w := a.1 • u)
    have hi := graph_dist_smul G a.1 x u
    omega
  have hvBound : ∀ a : S,
      (BassSerreFreeProduct.graph G).dist x (a.1 • v) < 2 * k + 2 := by
    intro a
    have ht := (BassSerreFreeProduct.graph_connected G).dist_triangle
      (u := x) (v := a.1 • x) (w := a.1 • v)
    have hi := graph_dist_smul G a.1 x v
    omega
  let code : S → Fin (2 * k + 1) × Fin (2 * k + 2) := fun a =>
    (⟨(BassSerreFreeProduct.graph G).dist x (a.1 • u), huBound a⟩,
      ⟨(BassSerreFreeProduct.graph G).dist x (a.1 • v), hvBound a⟩)
  have hcode : Function.Injective code := by
    intro a b hab
    have hdu : (BassSerreFreeProduct.graph G).dist x (a.1 • u) =
        (BassSerreFreeProduct.graph G).dist x (b.1 • u) := by
      exact congrArg (fun q => q.1.1) hab
    have hdv : (BassSerreFreeProduct.graph G).dist x (a.1 • v) =
        (BassSerreFreeProduct.graph G).dist x (b.1 • v) := by
      exact congrArg (fun q => q.2.1) hab
    have hau : a.1 • u = b.1 • u :=
      eq_of_mem_geodesic_of_graph_dist_eq G (hmem a).1 (hmem b).1 hdu
    have hav : a.1 • v = b.1 • v :=
      eq_of_mem_geodesic_of_graph_dist_eq G (hmem a).2 (hmem b).2 hdv
    have hfixu : (b.1⁻¹ * a.1) • u = u := by
      rw [mul_smul, hau, inv_smul_smul]
    have hfixv : (b.1⁻¹ * a.1) • v = v := by
      rw [mul_smul, hav, inv_smul_smul]
    have hone : b.1⁻¹ * a.1 = 1 := eq_one_of_fixes_adjacent G huv hfixu hfixv
    apply Subtype.ext
    exact inv_mul_eq_one.mp hone
  letI : Finite S := Finite.of_injective code hcode
  refine ⟨Set.toFinite S, ?_⟩
  rw [← Nat.card_coe_set_eq]
  exact (Nat.card_le_card_of_injective code hcode).trans_eq (by simp)

/-- **The Bass--Serre action is acylindrical.**  For a real error `ε`, choose
an integral upper bound `k`.  A segment of length `2k+1` has a central edge;
the preceding counting theorem injects all simultaneous `ε`-movers into a
set of `(2k+1)(2k+2)` distance pairs. -/
theorem isAcylindrical :
    HullGeometry.IsAcylindrical
      (BassSerreFreeProduct.Ambient G) (PathVertex G) := by
  intro ε _hε
  obtain ⟨k : ℕ, hk : ε ≤ k⟩ := exists_nat_ge ε
  refine ⟨(2 * k + 1 : ℝ), (2 * k + 1) * (2 * k + 2), ?_⟩
  intro x y hxy
  have hxyNat : 2 * k + 1 ≤ (BassSerreFreeProduct.graph G).dist x y := by
    rw [pathVertex_dist] at hxy
    exact_mod_cast hxy
  let S : Set (BassSerreFreeProduct.Ambient G) := {a |
    (BassSerreFreeProduct.graph G).dist x (a • x) ≤ k ∧
    (BassSerreFreeProduct.graph G).dist y (a • y) ≤ k}
  let T : Set (BassSerreFreeProduct.Ambient G) := {a |
    dist x (a • x) ≤ ε ∧ dist y (a • y) ≤ ε}
  obtain ⟨hSfinite, hScard⟩ := boundedGraphDisplacement_finite_count G k hxyNat
  have hTS : T ⊆ S := by
    intro a ha
    constructor
    · have hreal :
          ((BassSerreFreeProduct.graph G).dist x (a • x) : ℝ) ≤ k := by
        rw [← pathVertex_dist]
        exact ha.1.trans hk
      exact_mod_cast hreal
    · have hreal :
          ((BassSerreFreeProduct.graph G).dist y (a • y) : ℝ) ≤ k := by
        rw [← pathVertex_dist]
        exact ha.2.trans hk
      exact_mod_cast hreal
  have hTfinite : T.Finite := hSfinite.subset hTS
  change T.Finite ∧ T.ncard ≤ (2 * k + 1) * (2 * k + 2)
  exact ⟨hTfinite, (Set.ncard_le_ncard hTS hSfinite).trans hScard⟩

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
  obtain ⟨p, hp, _hunique⟩ :=
    (BassSerreFreeProduct.graph_isTree G).existsUnique_path x y
  let p' : (BassSerreFreeProduct.graph G).Walk x y :=
    (p.map (BassSerreFreeProduct.actionHom G a)).copy hx hy
  have hp' : p'.IsPath := by
    have hinj : Function.Injective (fun z : PathVertex G ↦ a • z) := by
      intro u v huv
      simpa only [inv_smul_smul] using
        congrArg (fun z : PathVertex G ↦ a⁻¹ • z) huv
    dsimp [p']
    rw [SimpleGraph.Walk.isPath_copy]
    exact hp.map hinj
  have heq : p = p' := congrArg Subtype.val
    ((BassSerreFreeProduct.graph_isAcyclic G).path_unique ⟨p, hp⟩ ⟨p', hp'⟩)
  cases p with
  | nil => exact (hxy rfl).elim
  | @cons x z y hxz q =>
      have hs := congrArg SimpleGraph.Walk.support heq
      have htail := congrArg List.tail hs
      have hhead := congrArg List.head? htail
      have hz : a • z = z := by
        simpa [p'] using hhead.symm
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

/-- Exact simultaneous displacement at any two distinct vertices has the same
optimal bound; the intervening geodesic supplies an edge fixed pointwise. -/
theorem exactDistinctDisplacement_eq_singleton {x y : PathVertex G}
    (hxy : x ≠ y) :
    {a : BassSerreFreeProduct.Ambient G | a • x = x ∧ a • y = y} = {1} := by
  ext a
  constructor
  · intro ha
    have : a = 1 := eq_one_of_fixes_distinct G hxy ha.1 ha.2
    simpa [this]
  · intro ha
    have : a = 1 := by simpa using ha
    subst a
    simp

end BassSerreHullGeometry
end GroupApproximation
