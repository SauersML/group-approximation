import GroupApproximation.Kazhdan.HalfSpaceBoundedOrbits
import GroupApproximation.GroupTheory.TreeGraphGeometry
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-!
# A group with property `(T)` acting on a tree has bounded orbits

The tree step of the Guentner--Higson--Weinberger argument used in
`non_mf_groups_exist.tex` (the remark after `prop:torsion-defect-ring`,
tex lines 1146--1150): `GL_2` over a field with a discrete valuation acts on the
Bruhat--Tits tree, and a Kazhdan subgroup must have bounded orbits there.
This module proves the tree statement for an arbitrary action of a group by
graph automorphisms on an arbitrary combinatorial tree.

The half-spaces are indexed by the darts `(u, v)` of the tree:
`H_{(u,v)} = {z : d(z, v) < d(z, u)}`.

* If `x ∈ H_{(u,v)}` and `y ∉ H_{(u,v)}`, every walk from `x` to `y` uses the
  edge `s(u,v)`: a shortest walk from `x` to `v` and a shortest walk from `y` to
  `u` both avoid it, so a walk from `x` to `y` avoiding it would give a walk from
  `u` to `v` avoiding it, and every edge of a tree is a bridge.  So only the
  darts over the edges of one walk separate `x` from `y`: finitely many.
* The darts along the geodesic from `x` to `y` all separate them, so at least
  `d(x,y)` darts separate `x` from `y`.

With `HalfSpaceSystem.exists_card_sepFinset_bound` (Delorme's theorem) the
displacement `d(x₀, g x₀)` is bounded uniformly in `g`.
-/

namespace GroupApproximation
namespace TreeAction

universe u

open SimpleGraph

variable {V : Type u} {H : SimpleGraph V}

/-- A shortest walk from `x` to `v` does not visit a vertex `u ≠ v` that is at
least as far from `x` as `v` is. -/
theorem not_mem_support_of_length_eq_dist {x v u : V} (p : H.Walk x v)
    (hp : p.length = H.dist x v) (huv : u ≠ v) (hdist : H.dist x v ≤ H.dist x u) :
    u ∉ p.support := by
  intro hu
  have hlt := Walk.length_takeUntil_lt_length hu huv
  have hle : H.dist x u ≤ (p.takeUntil u hu).length := dist_le _
  omega

theorem edge_not_mem_edges_of_length_eq_dist {x v u : V} (p : H.Walk x v)
    (hp : p.length = H.dist x v) (huv : u ≠ v) (hdist : H.dist x v ≤ H.dist x u) :
    s(u, v) ∉ p.edges := fun he ↦
  not_mem_support_of_length_eq_dist p hp huv hdist (p.fst_mem_support_of_mem_edges he)

/-- **Separated vertices force the edge.**  In a tree, if `x` is strictly
closer to `v` than to `u`, `y` is at least as close to `u` as to `v`, and `u, v`
are adjacent, then every walk from `x` to `y` uses the edge `s(u, v)`. -/
theorem edge_mem_edges_of_separated (hT : H.IsTree) {u v x y : V} (hadj : H.Adj u v)
    (hx : H.dist x v < H.dist x u) (hy : H.dist y u ≤ H.dist y v) (p : H.Walk x y) :
    s(u, v) ∈ p.edges := by
  by_contra hp
  obtain ⟨q₁, hq₁⟩ := hT.connected.exists_walk_length_eq_dist x v
  obtain ⟨q₂, hq₂⟩ := hT.connected.exists_walk_length_eq_dist y u
  have h₁ : s(u, v) ∉ q₁.edges := edge_not_mem_edges_of_length_eq_dist q₁ hq₁ hadj.ne hx.le
  have h₂ : s(u, v) ∉ q₂.edges := by
    rw [Sym2.eq_swap]
    exact edge_not_mem_edges_of_length_eq_dist q₂ hq₂ hadj.ne.symm hy
  have hbridge : H.IsBridge s(u, v) :=
    isAcyclic_iff_forall_isBridge.mp hT.isAcyclic (mem_edgeSet.mpr hadj)
  have hmem :=
    isBridge_iff_forall_walk_mem_edges.mp hbridge ((q₂.reverse.append p.reverse).append q₁)
  simp only [Walk.edges_append, Walk.edges_reverse, List.mem_append, List.mem_reverse] at hmem
  rcases hmem with (h | h) | h
  · exact h₂ h
  · exact hp h
  · exact h₁ h

/-! ## Group actions by graph automorphisms -/

section Action

variable {G : Type u} [Group G] [MulAction G V]

/-- `G` acts on the vertices of `H` by graph automorphisms. -/
def IsGraphAction (G : Type u) [Group G] [MulAction G V] (H : SimpleGraph V) : Prop :=
  ∀ (g : G) (x y : V), H.Adj (g • x) (g • y) ↔ H.Adj x y

/-- The graph homomorphism `x ↦ g • x`. -/
def smulHom (hG : IsGraphAction G H) (g : G) : H →g H where
  toFun x := g • x
  map_rel' h := (hG g _ _).mpr h

theorem dist_smul_le (hconn : H.Connected) (hG : IsGraphAction G H) (g : G) (x y : V) :
    H.dist (g • x) (g • y) ≤ H.dist x y := by
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist x y
  have h := dist_le (p.map (smulHom hG g))
  rw [Walk.length_map, hp] at h
  exact h

theorem dist_smul (hconn : H.Connected) (hG : IsGraphAction G H) (g : G) (x y : V) :
    H.dist (g • x) (g • y) = H.dist x y := by
  refine le_antisymm (dist_smul_le hconn hG g x y) ?_
  have h := dist_smul_le hconn hG g⁻¹ (g • x) (g • y)
  rwa [inv_smul_smul, inv_smul_smul] at h

/-- The induced action on darts. -/
def dartSMul (hG : IsGraphAction G H) : MulAction G H.Dart where
  smul g d := ⟨(g • d.fst, g • d.snd), (hG g _ _).mpr d.adj⟩
  one_smul d := Dart.ext _ _ (Prod.ext (one_smul G d.fst) (one_smul G d.snd))
  mul_smul g h d := Dart.ext _ _ (Prod.ext (mul_smul g h d.fst) (mul_smul g h d.snd))

/-- **The half-spaces of a tree**: `H_{(u,v)} = {z : d(z,v) < d(z,u)}`. -/
noncomputable def treeHalfSpaces (hT : H.IsTree) (hG : IsGraphAction G H) :
    @HalfSpaceSystem G _ V _ H.Dart (dartSMul hG) := by
  letI := dartSMul hG
  exact
    { half := fun d ↦ {z | H.dist z d.snd < H.dist z d.fst}
      equivariant := fun g d z ↦ by
        show H.dist (g • z) (g • d.snd) < H.dist (g • z) (g • d.fst) ↔
          H.dist z d.snd < H.dist z d.fst
        rw [dist_smul hT.connected hG, dist_smul hT.connected hG]
      finite_sep := fun x y ↦ by
        classical
        obtain ⟨p, -⟩ := hT.connected.exists_walk_length_eq_dist x y
        refine Set.Finite.subset
          (Set.Finite.preimage (f := SimpleGraph.Dart.toProd)
            (fun d₁ _ d₂ _ h ↦ Dart.ext _ _ h)
            (p.support.toFinset ×ˢ p.support.toFinset : Finset (V × V)).finite_toSet) ?_
        intro d hd
        simp only [Set.mem_setOf_eq] at hd
        have hedge : s(d.fst, d.snd) ∈ p.edges := by
          by_cases hx : H.dist x d.snd < H.dist x d.fst
          · have hy : H.dist y d.fst ≤ H.dist y d.snd := by
              by_contra hy
              exact hd ⟨fun _ ↦ not_le.mp hy, fun _ ↦ hx⟩
            exact edge_mem_edges_of_separated hT d.adj hx hy p
          · have hy : H.dist y d.snd < H.dist y d.fst := by
              by_contra hy
              exact hd ⟨fun h ↦ absurd h hx, fun h ↦ absurd h hy⟩
            have hx' : H.dist x d.fst ≤ H.dist x d.snd := le_of_not_gt hx
            have h := edge_mem_edges_of_separated hT d.adj hy hx' p.reverse
            simpa [Walk.edges_reverse] using h
        simp only [Set.mem_preimage, Finset.coe_product, Set.mem_prod, Finset.mem_coe,
          List.mem_toFinset]
        exact ⟨p.fst_mem_support_of_mem_edges hedge, p.snd_mem_support_of_mem_edges hedge⟩ }

/-- At least `d(x,y)` half-spaces separate `x` from `y`: the darts along the
geodesic. -/
theorem dist_le_card_sepFinset (hT : H.IsTree) (hG : IsGraphAction G H) (x y : V) :
    H.dist x y ≤
      (@HalfSpaceSystem.sepFinset G _ V _ H.Dart (dartSMul hG) (treeHalfSpaces hT hG) x y).card := by
  classical
  letI := dartSMul hG
  let W := treeHalfSpaces hT hG
  let p := TreeGraphGeometry.geodesic H hT x y
  have hlen : p.length = H.dist x y := TreeGraphGeometry.geodesic_length H hT x y
  have hdx : ∀ i, i ≤ p.length → H.dist x (p.getVert i) = i := fun i hi ↦
    TreeGraphGeometry.dist_getVert_geodesic H hT (hlen ▸ hi)
  have hdy : ∀ i, i ≤ p.length → H.dist y (p.getVert i) = p.length - i := by
    intro i hi
    have hsum := TreeGraphGeometry.dist_add_dist_eq_of_mem_geodesic H hT
      (p.getVert_mem_support i)
    rw [hdx i hi, dist_comm] at hsum
    omega
  let f : Fin p.length → H.Dart := fun i ↦
    ⟨(p.getVert i, p.getVert (i + 1)), p.adj_getVert_succ i.2⟩
  have hcard := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin p.length)))
    (t := W.sepFinset x y) f
    (fun i _ ↦ by
      refine (W.mem_sepFinset).mpr ?_
      show ¬ (H.dist x (p.getVert (i + 1)) < H.dist x (p.getVert i) ↔
        H.dist y (p.getVert (i + 1)) < H.dist y (p.getVert i))
      rw [hdx i i.2.le, hdx (i + 1) i.2, hdy i i.2.le, hdy (i + 1) i.2]
      omega)
    (fun i _ j _ hij ↦ by
      have hv : p.getVert i = p.getVert j := congrArg (fun d : H.Dart ↦ d.fst) hij
      have := congrArg (H.dist x) hv
      rw [hdx i i.2.le, hdx j j.2.le] at this
      exact Fin.ext this)
  rw [Finset.card_univ, Fintype.card_fin, hlen] at hcard
  exact hcard

/-- **A group with property `(T)` acting on a tree by graph automorphisms has
bounded orbits.** -/
theorem exists_dist_bound_of_hasKazhdanPropertyT (hT : H.IsTree) (hG : IsGraphAction G H)
    (hK : HasKazhdanPropertyT.{u, u} G) (x₀ : V) :
    ∃ R : ℝ, ∀ g : G, (H.dist x₀ (g • x₀) : ℝ) ≤ R := by
  letI := dartSMul hG
  obtain ⟨R, hR⟩ := (treeHalfSpaces hT hG).exists_card_sepFinset_bound hK x₀
  exact ⟨R, fun g ↦ (Nat.cast_le.mpr (dist_le_card_sepFinset hT hG x₀ (g • x₀))).trans (hR g)⟩

end Action

end TreeAction
end GroupApproximation

#audit_axioms GroupApproximation.TreeAction.exists_dist_bound_of_hasKazhdanPropertyT
