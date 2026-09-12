import GroupApproximation.Algebra.FreePermutationalPrecursor

/-!
# Graph products of groups

Section 54.3 of the dossier interpolates a **graph product** between the free
product of the vertex groups and their restricted direct product: given a
simplicial graph on the site set, `B_𝒢` is the free product of one copy of `K`
per site, with two vertex groups made to commute exactly when their sites are
adjacent.  Taking the empty graph gives the free product; taking the complete
graph gives the restricted direct product.  Mathlib has no graph products, so
they are built here.

Only one nontrivial fact about them is needed, and it is the one the necessity
half of Lemma 54.3 turns on:

> at a **non**-edge `{x, y}` the cross-site commutator `⁅k_x, ℓ_y⁆` is still
> nontrivial in the graph product.

That is `vertex_commutator_ne_one`.  The proof is a retraction rather than any
normal-form theory for graph products: kill every vertex group except the two at
`x` and `y`, which is legitimate precisely because `x` and `y` are *not*
adjacent, so no imposed relation is destroyed; the result lands in the free
product `K * K`, where the commutator is a reduced word
(`boolOf_commutator_ne_one` in `Algebra/FreePermutationalPrecursor`).

The graph is required to be **simplicial**: symmetric and irreflexive.  Both are
used, and neither is decorative.  Symmetry is what lets the retraction rule out
the edge `(y, x)` as well as `(x, y)`.  Irreflexivity is what rules out a loop
at `x`, whose relation `⁅k_x, ℓ_x⁆ = 1` would make the vertex group abelian and
survive the retraction; without it the statement is simply false.
-/

namespace GroupApproximation

namespace GraphProduct

universe u v

open Monoid.CoprodI

open scoped commutatorElement

variable {K : Type u} [Group K] {X : Type v}

/-- A simplicial graph on `X`: symmetric and irreflexive. -/
structure IsSimplicial (adj : X → X → Prop) : Prop where
  symm : ∀ {x y : X}, adj x y → adj y x
  irrefl : ∀ {x : X}, ¬ adj x x

/-- The relations imposed by the graph: the cross-site commutators at adjacent
sites. -/
def edgeRelators (K : Type u) [Group K] {X : Type v} (adj : X → X → Prop) :
    Set (FreePrecursor.FreeLamp K X) :=
  {w | ∃ (x y : X) (k l : K), adj x y ∧
    w = ⁅of (M := fun _ : X => K) (i := x) k,
        of (M := fun _ : X => K) (i := y) l⁆}

/-- The **graph product** of copies of `K` over the sites `X`, for the adjacency
`adj`: the free product of the vertex groups, with adjacent vertex groups made
to commute. -/
abbrev _root_.GroupApproximation.GraphProd (K : Type u) [Group K] {X : Type v}
    (adj : X → X → Prop) : Type (max u v) :=
  FreePrecursor.FreeLamp K X ⧸ Subgroup.normalClosure (edgeRelators K adj)

variable {adj : X → X → Prop}

/-- The quotient map from the free product. -/
def mk (adj : X → X → Prop) :
    FreePrecursor.FreeLamp K X →* GraphProd K adj :=
  QuotientGroup.mk' _

theorem mk_surjective (adj : X → X → Prop) :
    Function.Surjective (mk (K := K) adj) :=
  QuotientGroup.mk'_surjective _

/-- The inclusion of the vertex group at a site. -/
def vertex (adj : X → X → Prop) (x : X) : K →* GraphProd K adj :=
  (mk adj).comp (of (M := fun _ : X => K) (i := x))

@[simp] theorem mk_of (adj : X → X → Prop) (x : X) (k : K) :
    mk adj (of (M := fun _ : X => K) (i := x) k) = vertex adj x k := rfl

/-- **Adjacent vertex groups commute.**  This is the defining relation. -/
theorem commute_vertex_of_adj {x y : X} (hxy : adj x y) (k l : K) :
    Commute (vertex adj x k) (vertex adj y l) := by
  rw [← commutatorElement_eq_one_iff_commute]
  have hmem : ⁅of (M := fun _ : X => K) (i := x) k,
      of (M := fun _ : X => K) (i := y) l⁆
      ∈ Subgroup.normalClosure (edgeRelators K adj) :=
    Subgroup.subset_normalClosure ⟨x, y, k, l, hxy, rfl⟩
  have := (QuotientGroup.eq_one_iff (N := Subgroup.normalClosure (edgeRelators K adj))
    _).mpr hmem
  simpa [vertex, mk, commutatorElement_def] using this

/-! ## The retraction at a non-edge -/

section Retract

variable [DecidableEq X]

/-- At a non-edge the two-site retraction of the free product kills every
imposed relation, so it descends to the graph product.  Every edge either misses
one of the two chosen sites -- and then one of its two letters is killed -- or is
the pair `{x, y}` itself in one of its two orders, which symmetry excludes, or is
a loop, which irreflexivity excludes. -/
theorem siteRetract_edgeRelators (hG : IsSimplicial adj) {x y : X}
    (hnadj : ¬ adj x y) :
    edgeRelators K adj ≤ (FreePrecursor.siteRetract K X x y).ker := by
  rintro _ ⟨u, v, k, l, huv, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement]
  by_cases hux : u = x
  · by_cases hvy : v = y
    · exact absurd (by rw [← hux, ← hvy]; exact huv) hnadj
    · by_cases hvu : v = u
      · rw [hvu] at huv
        exact absurd huv hG.irrefl
      · have hvx : v ≠ x := by rw [← hux]; exact hvu
        rw [FreePrecursor.siteRetract_of_other K X hvx hvy,
          commutatorElement_one_right]
  · by_cases huy : u = y
    · by_cases hvx : v = x
      · exact absurd (hG.symm (by rw [← huy, ← hvx]; exact huv)) hnadj
      · by_cases hvu : v = u
        · rw [hvu] at huv
          exact absurd huv hG.irrefl
        · have hvy : v ≠ y := by rw [← huy]; exact hvu
          rw [FreePrecursor.siteRetract_of_other K X hvx hvy,
            commutatorElement_one_right]
    · rw [FreePrecursor.siteRetract_of_other K X hux huy, commutatorElement_one_left]

/-- The retraction of the graph product onto the free product of the two vertex
groups at a non-edge. -/
def graphRetract (hG : IsSimplicial adj) {x y : X} (hnadj : ¬ adj x y) :
    GraphProd K adj →* FreePrecursor.BoolCoprod K :=
  QuotientGroup.lift _ (FreePrecursor.siteRetract K X x y)
    (Subgroup.normalClosure_le_normal (siteRetract_edgeRelators hG hnadj))

@[simp] theorem graphRetract_vertex_left (hG : IsSimplicial adj) {x y : X}
    (hnadj : ¬ adj x y) (k : K) :
    graphRetract hG hnadj (vertex adj x k) = FreePrecursor.boolOf K true k := by
  simp [graphRetract, vertex, mk]

@[simp] theorem graphRetract_vertex_right (hG : IsSimplicial adj) {x y : X}
    (hnadj : ¬ adj x y) (hyx : y ≠ x) (k : K) :
    graphRetract hG hnadj (vertex adj y k) = FreePrecursor.boolOf K false k := by
  simp [graphRetract, vertex, mk, FreePrecursor.siteRetract_of_right K X hyx]

/-- **The point of the graph product (54.22).**  At a non-edge the cross-site
commutator survives: distinct, nonadjacent vertex groups do *not* commute.  This
is what separates a graph product from the restricted direct product, and it is
the contradiction the necessity half of Lemma 54.3 runs into. -/
theorem vertex_commutator_ne_one (hG : IsSimplicial adj) {x y : X} (hxy : x ≠ y)
    (hnadj : ¬ adj x y) {k l : K} (hk : k ≠ 1) (hl : l ≠ 1) :
    ⁅vertex adj x k, vertex adj y l⁆ ≠ 1 := by
  intro hcon
  have himg := congrArg (graphRetract hG hnadj) hcon
  rw [map_commutatorElement, graphRetract_vertex_left,
    graphRetract_vertex_right hG hnadj (Ne.symm hxy), map_one] at himg
  exact FreePrecursor.boolOf_commutator_ne_one K hk hl himg

/-- Consequently the two vertex groups at a non-edge fail to commute, so the
graph product is not the restricted direct product unless the graph is
complete. -/
theorem not_commute_vertex_of_not_adj (hG : IsSimplicial adj) {x y : X}
    (hxy : x ≠ y) (hnadj : ¬ adj x y) {k l : K} (hk : k ≠ 1) (hl : l ≠ 1) :
    ¬ Commute (vertex adj x k) (vertex adj y l) := by
  rw [← commutatorElement_eq_one_iff_commute]
  exact vertex_commutator_ne_one hG hxy hnadj hk hl

/-- **The contradiction step of Lemma 54.3, abstractly.**  If in the graph
product the vertex groups at two *distinct* sites commute, then those sites are
adjacent.  Equivalently: a graph product in which all distinct vertex groups
commute is a graph product over the complete graph.

This is the whole force of the final paragraph of Lemma 54.3.  There the graph
product is identified with the wreath product `W`, in which different-site lamp
groups commute by construction; this lemma then says every pair of distinct
sites must already be an edge, so the finitely many pair-orbits collected from
the normal generators exhaust all of them. -/
theorem adj_of_commute_vertex [Nontrivial K] (hG : IsSimplicial adj) {x y : X}
    (hxy : x ≠ y)
    (hcomm : ∀ k l : K, Commute (vertex adj x k) (vertex adj y l)) : adj x y := by
  by_contra hnadj
  obtain ⟨k, hk⟩ := exists_ne (1 : K)
  exact not_commute_vertex_of_not_adj hG hxy hnadj hk hk (hcomm k k)

/-- The vertex inclusions at a non-edge are injective, since they are split by
the retraction. -/
theorem vertex_injective_left (hG : IsSimplicial adj) {x y : X}
    (hnadj : ¬ adj x y) : Function.Injective (vertex (K := K) adj x) := by
  intro k l hkl
  have h := congrArg (graphRetract hG hnadj) hkl
  rw [graphRetract_vertex_left, graphRetract_vertex_left] at h
  exact Monoid.CoprodI.of_injective (M := fun _ : Bool => K) true h

end Retract

/-! ## The two extreme graphs -/

/-- With no edges the graph product is the free product itself. -/
theorem edgeRelators_bot : edgeRelators K (fun _ _ : X => False) = ∅ := by
  ext w
  simp [edgeRelators]

end GraphProduct

end GroupApproximation
