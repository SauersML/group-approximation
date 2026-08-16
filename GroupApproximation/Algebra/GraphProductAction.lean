import GroupApproximation.Algebra.GraphProduct

/-!
# The acting group on a graph product, and the group `E_𝒢` of (54.20)

Lemma 54.3 forms the semidirect product `E_𝒢 = B_𝒢 ⋊ G`, where `G` permutes the
sites and `B_𝒢` is the graph product over a `G`-invariant graph.  This file
supplies the action.

A site permutation carries the free product's relators to relators as soon as
the graph is `G`-invariant, so it descends to the graph product; the descended
maps compose the way `G` multiplies, so they assemble into
`graphActionHom : G →* MulAut (B_𝒢)` and hence into the semidirect product
`GraphWreath`.

The `G`-invariance hypothesis is exactly what makes the descent legitimate, and
it is the hypothesis Lemma 54.3 arranges by building the graph out of a union of
`G`-orbits of pairs.
-/

namespace GroupApproximation

namespace GraphProduct

universe u v w

open Monoid.CoprodI

variable {K : Type u} [Group K] {X : Type v} {adj : X → X → Prop}
variable {G : Type w} [Group G] [MulAction G X]

/-- A graph on the sites preserved by the acting group. -/
def IsInvariant (G : Type w) [Group G] [MulAction G X] (adj : X → X → Prop) : Prop :=
  ∀ (g : G) (a b : X), adj a b → adj (g • a) (g • b)

/-- A site permutation carries imposed relations to imposed relations. -/
theorem freeLampMap_mem_normalClosure (hinv : IsInvariant G adj) (g : G)
    {w : FreePrecursor.FreeLamp K X} (hw : w ∈ edgeRelators K adj) :
    FreePrecursor.freeLampMap K X g w
      ∈ Subgroup.normalClosure (edgeRelators K adj) := by
  obtain ⟨u, v, k, l, huv, rfl⟩ := hw
  rw [map_commutatorElement, FreePrecursor.freeLampMap_of,
    FreePrecursor.freeLampMap_of]
  exact Subgroup.subset_normalClosure ⟨g • u, g • v, k, l, hinv g u v huv, rfl⟩

/-- The endomorphism of the graph product induced by a site permutation. -/
def graphMap (hinv : IsInvariant G adj) (g : G) :
    GraphProd K adj →* GraphProd K adj :=
  QuotientGroup.lift _ ((mk adj).comp (FreePrecursor.freeLampMap K X g))
    (Subgroup.normalClosure_le_normal (by
      intro w hw
      rw [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply, mk,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact freeLampMap_mem_normalClosure hinv g hw))

@[simp] theorem graphMap_vertex (hinv : IsInvariant G adj) (g : G) (x : X)
    (k : K) :
    graphMap (K := K) hinv g (vertex adj x k) = vertex adj (g • x) k := by
  simp [graphMap, vertex, mk]

theorem graphMap_one (hinv : IsInvariant G adj) :
    graphMap (K := K) (G := G) hinv 1 = MonoidHom.id (GraphProd K adj) := by
  refine MonoidHom.ext fun z => ?_
  obtain ⟨w, rfl⟩ := mk_surjective adj z
  show mk adj (FreePrecursor.freeLampMap K X (1 : G) w) = mk adj w
  rw [DFunLike.congr_fun (FreePrecursor.freeLampMap_one K X (G := G)) w]
  rfl

theorem graphMap_comp (hinv : IsInvariant G adj) (g h : G) :
    (graphMap (K := K) hinv g).comp (graphMap hinv h)
      = graphMap (K := K) hinv (g * h) := by
  refine MonoidHom.ext fun z => ?_
  obtain ⟨w, rfl⟩ := mk_surjective adj z
  show mk adj (FreePrecursor.freeLampMap K X g
      (FreePrecursor.freeLampMap K X h w))
    = mk adj (FreePrecursor.freeLampMap K X (g * h) w)
  rw [← FreePrecursor.freeLampMap_comp]
  rfl

/-- The site permutation attached to `g`, as an automorphism of the graph
product. -/
def graphAut (hinv : IsInvariant G adj) (g : G) :
    MulAut (GraphProd K adj) where
  toFun := graphMap hinv g
  invFun := graphMap hinv g⁻¹
  left_inv := fun z => by
    have h := graphMap_comp (K := K) hinv g⁻¹ g
    rw [inv_mul_cancel, graphMap_one] at h
    exact DFunLike.congr_fun h z
  right_inv := fun z => by
    have h := graphMap_comp (K := K) hinv g g⁻¹
    rw [mul_inv_cancel, graphMap_one] at h
    exact DFunLike.congr_fun h z
  map_mul' := fun a b => map_mul (graphMap hinv g) a b

/-- The action of the site-permuting group on the graph product. -/
def graphActionHom (hinv : IsInvariant G adj) :
    G →* MulAut (GraphProd K adj) where
  toFun := graphAut hinv
  map_one' := by
    refine MulEquiv.ext fun z => ?_
    show graphMap (K := K) hinv (1 : G) z = z
    rw [graphMap_one]
    rfl
  map_mul' := fun g h => by
    refine MulEquiv.ext fun z => ?_
    show graphMap (K := K) hinv (g * h) z
      = graphMap hinv g (graphMap hinv h z)
    rw [← graphMap_comp]
    rfl

/-- **The group `E_𝒢` of (54.20)**: the graph product with the site-permuting
group adjoined. -/
abbrev GraphWreath (hinv : IsInvariant G adj) : Type (max u v w) :=
  GraphProd K adj ⋊[graphActionHom (K := K) hinv] G

end GraphProduct

end GroupApproximation
