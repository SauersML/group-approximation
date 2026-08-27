import GroupApproximation.GGT.HyperbolicTreeMetric

/-!
# Actions on a tree: isometry, displacement convexity, acylindricity

`GGT/HyperbolicTreeMetric.lean` turns a tree into a `0`-hyperbolic
`PseudoMetricSpace`.  This module makes a group acting on the tree by graph
automorphisms act on that space, and pushes the consequences as far as they go
without further tree combinatorics.

## What is proved

* `dist_smul_eq` --- a bijective action by adjacency-preserving maps is by graph
  isometries.  Only one direction of adjacency preservation is assumed; the
  other comes from applying it to `g⁻¹`.  Consequently
  `isIsometricAction_treeSpace`, in the form
  `HullGeometry.IsIsometricAction` states it.
* `dist_smul_le_max_of_between` --- **displacement is convex along geodesics**:
  if `m` lies between `x` and `y` then

  ```
      d(m, g·m) ≤ max (d(x, g·x), d(y, g·y)).
  ```

  This is usually quoted as a `CAT(0)` fact.  In a tree it is one line of the
  sharp four-point inequality: `(x|y)_m = 0` because `m` is between `x` and `y`,
  so the four-point condition at basepoint `m` applied to `x`, `g·m`, `y` forces
  `(x|g·m)_m = 0` or `(g·m|y)_m = 0`, and either branch reads off the bound
  against the corresponding endpoint.  No curvature machinery, no geodesic
  parametrisation.
* `isAcylindrical_treeSpace` --- acylindricity from a shift datum together with
  trivial pointwise stabilisers of long segments.

## Why acylindricity needs a shift, not a fixed point

The natural guess --- "`g` almost fixes both ends of a long segment, so `g`
fixes its middle pointwise" --- is **false**, and displacement convexity is
exactly as far as it goes.  A translation of the line `ℤ` moves every vertex by
one and fixes nothing, while every segment stabiliser is trivial.  What is true
is that such a `g` *shifts* the middle segment by a bounded amount: it maps the
vertex at depth `i` to the vertex at depth `i - k` for one integer `k` with
`|k| ≤ n`, independent of `i`.  The counting then runs on the shift and not on
a fixed point: two elements with the same shift differ by something fixing the
middle segment pointwise.

`HasSegmentShift` is that datum, packaged as exactly what the counting consumes:
a pair of vertices far apart and a bounded integer invariant whose level sets
are cosets of their pointwise stabiliser.  It is **not proved here** ---
`SegmentShiftStatement` names the missing theorem --- because it is several
hundred lines of `Walk` and geodesic combinatorics, and it is the one input a
Bass--Serre construction has to supply.  `TreeAcylindricityStatement` names the
general conclusion, with bounded rather than trivial stabilisers, which follows
from the shift by a coset count.

Given the shift and *trivial* segment stabilisers --- which is the case for a
Bass--Serre tree with trivial edge stabilisers, and the case
`Algebra/BassSerreFreeProductAction.baseEdge_pointwiseStabilizer_eq_bot` already
establishes for a binary free product --- no coset counting is needed at all:
the shift invariant is injective on the `ε`-stabiliser of the pair, so the
bound is the number of available shifts.  That is `isAcylindrical_treeSpace`,
and it is unconditional given its two hypotheses.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.HullGeometry
open GroupApproximation.TreeGraphGeometry

universe u v

/-! ## The action on the metric space -/

/-- A group acting on the vertices acts on the tree metric space.  Declared at
low priority so that a construction which carries its own action on its own
vertex type --- as `GGT/BassSerreHNNAction.lean` does --- keeps that one, and
lemmas stated against it continue to match syntactically. -/
instance (priority := 100) instMulActionTreeSpace {G : Type u} [Group G]
    {V : Type v} {H : SimpleGraph V} [MulAction G V] (hH : H.IsTree) :
    MulAction G (TreeSpace hH) :=
  inferInstanceAs (MulAction G V)

@[simp] theorem TreeSpace.val_smul {G : Type u} [Group G] {V : Type v}
    {H : SimpleGraph V} [MulAction G V] {hH : H.IsTree} (g : G)
    (x : TreeSpace hH) : TreeSpace.val (g • x) = g • TreeSpace.val x := rfl

/-- **An action by adjacency-preserving bijections is by graph isometries.**
Adjacency preservation is assumed in one direction only: a walk maps to a walk
of the same length, which gives one inequality, and the same statement for `g⁻¹`
gives the other. -/
theorem dist_smul_eq {G : Type u} [Group G] {V : Type v} {H : SimpleGraph V}
    [MulAction G V] (hH : H.IsTree)
    (hadj : ∀ (g : G) (u w : V), H.Adj u w → H.Adj (g • u) (g • w))
    (g : G) (u w : V) : H.dist (g • u) (g • w) = H.dist u w := by
  have key : ∀ (a : G) (p q : V), H.dist (a • p) (a • q) ≤ H.dist p q := by
    intro a p q
    have hle := SimpleGraph.dist_le ((geodesic H hH p q).map
      (⟨fun z => a • z, fun h => hadj a _ _ h⟩ : SimpleGraph.Hom H H))
    rw [SimpleGraph.Walk.length_map, geodesic_length] at hle
    exact hle
  refine le_antisymm (key g u w) ?_
  have h := key g⁻¹ (g • u) (g • w)
  rw [inv_smul_smul, inv_smul_smul] at h
  exact h

/-- The translation action on the tree metric space is by isometries. -/
theorem isIsometricAction_treeSpace {G : Type u} [Group G] {V : Type v}
    {H : SimpleGraph V} [MulAction G V] (hH : H.IsTree)
    (hadj : ∀ (g : G) (u w : V), H.Adj u w → H.Adj (g • u) (g • w)) :
    IsIsometricAction G (TreeSpace hH) := by
  intro g x y
  have h := dist_smul_eq hH hadj g (TreeSpace.val x) (TreeSpace.val y)
  show ((H.dist (TreeSpace.val (g • x)) (TreeSpace.val (g • y)) : ℕ) : ℝ)
    = ((H.dist (TreeSpace.val x) (TreeSpace.val y) : ℕ) : ℝ)
  rw [TreeSpace.val_smul, TreeSpace.val_smul, h]

/-! ## Displacement is convex along geodesics -/

/-- **Displacement convexity in a tree.**  If `m` lies between `x` and `y` then
`g` moves `m` by at most the larger of the displacements of the two endpoints.

The proof is the sharp four-point inequality and nothing else.  Betweenness says
`(x|y)_m = 0`, so the four-point condition at basepoint `m` for the triple
`x, g·m, y` forces one of `(x|g·m)_m` and `(g·m|y)_m` to vanish.  The first says
`m` is between `x` and `g·m`, and comparing with the route from `x` through
`g·x` --- which costs `d(x,g·x) + d(x,m)`, since `g` is an isometry --- bounds
`d(m, g·m)` by `d(x, g·x)`.  The second branch is the same argument at `y`. -/
theorem dist_smul_le_max_of_between {G : Type u} [Group G] {V : Type v}
    {H : SimpleGraph V} [MulAction G V] (hH : H.IsTree)
    (hiso : ∀ (a : G) (p q : V), H.dist (a • p) (a • q) = H.dist p q) (g : G)
    {x y m : V} (hm : H.dist x m + H.dist m y = H.dist x y) :
    H.dist m (g • m) ≤ max (H.dist x (g • x)) (H.dist y (g • y)) := by
  have key := graphDist_fourPoint_zero H hH m x (g • m) y
  have h1 : H.dist (g • x) (g • m) = H.dist x m := hiso g x m
  have h2 : H.dist (g • m) (g • y) = H.dist m y := hiso g m y
  have t2 := hH.connected.dist_triangle (u := x) (v := g • x) (w := g • m)
  have t3 := hH.connected.dist_triangle (u := g • m) (v := g • y) (w := y)
  have c1 : H.dist m y = H.dist y m := SimpleGraph.dist_comm
  have c2 : H.dist m (g • m) = H.dist (g • m) m := SimpleGraph.dist_comm
  have c3 : H.dist (g • y) y = H.dist y (g • y) := SimpleGraph.dist_comm
  omega

/-! ## Segment stabilisers and the shift datum -/

/-- **Trivial pointwise stabilisers of long segments**: no nonidentity element
fixes two vertices at distance at least `L`.  For a Bass--Serre tree this is the
statement that edge stabilisers are trivial, which
`Algebra/BassSerreFreeProductAction.baseEdge_pointwiseStabilizer_eq_bot` proves
for a binary free product. -/
def TrivialSegmentStabilizers (G : Type u) [Group G] {V : Type v}
    (H : SimpleGraph V) [MulAction G V] (L : ℕ) : Prop :=
  ∀ u w : V, L ≤ H.dist u w → ∀ g : G, g • u = u → g • w = w → g = 1

/-- **Bounded pointwise stabilisers of long segments**: the pointwise stabiliser
of any two vertices at distance at least `L` is finite of size at most `N`.  The
hypothesis a Bass--Serre construction with finite edge groups supplies. -/
def BoundedSegmentStabilizers (G : Type u) [Group G] {V : Type v}
    (H : SimpleGraph V) [MulAction G V] (L N : ℕ) : Prop :=
  ∀ u w : V, L ≤ H.dist u w →
    {g : G | g • u = u ∧ g • w = w}.Finite ∧
      {g : G | g • u = u ∧ g • w = w}.ncard ≤ N

/-- **The shift datum.**  Whenever two vertices are at distance at least
`L + 2n`, there are two vertices `u`, `w` at distance at least `L` --- the ends
of the middle segment --- and a bounded integer invariant `Φ` of the elements
moving both original vertices by at most `n`, such that two elements with the
same invariant agree on `u` and on `w`.

This is the honest content of "`g` almost fixes both ends of a long segment, so
it acts on the middle by a bounded shift", stated in exactly the form the
cardinality count consumes and with no reference to fixed points, which need not
exist. -/
def HasSegmentShift (G : Type u) [Group G] {V : Type v} (H : SimpleGraph V)
    [MulAction G V] (L : ℕ) : Prop :=
  ∀ (n : ℕ) (x y : V), L + 2 * n ≤ H.dist x y →
    ∃ (u w : V) (Φ : G → ℤ), L ≤ H.dist u w ∧
      ∀ g : G, H.dist x (g • x) ≤ n → H.dist y (g • y) ≤ n →
        (Φ g).natAbs ≤ n ∧
          ∀ h : G, H.dist x (h • x) ≤ n → H.dist y (h • y) ≤ n →
            Φ g = Φ h → g • u = h • u ∧ g • w = h • w

/-! ## Acylindricity -/

/-- **A tree action with a shift datum and trivial segment stabilisers is
acylindrical.**

`R = L + 2⌈ε⌉` and `N` is the number of available shifts.  Trivial stabilisers
make the shift invariant *injective* on the `ε`-stabiliser of the pair, so the
count is an injection into `{k : ℤ | |k| ≤ ⌈ε⌉}` and no coset arithmetic is
needed. -/
theorem isAcylindrical_treeSpace {G : Type u} [Group G] {V : Type v}
    {H : SimpleGraph V} [MulAction G V] (hH : H.IsTree) {L : ℕ}
    (hshift : HasSegmentShift G H L)
    (hstab : TrivialSegmentStabilizers G H L) :
    IsAcylindrical G (TreeSpace hH) := by
  classical
  intro ε _hε
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ε ≤ (n : ℝ) := ⟨⌈ε⌉₊, Nat.le_ceil ε⟩
  have hfin : {k : ℤ | k.natAbs ≤ n}.Finite := by
    refine Set.Finite.subset
      (Set.Finite.union
        (Set.finite_range (fun m : Fin (n + 1) => ((m : ℕ) : ℤ)))
        (Set.finite_range (fun m : Fin (n + 1) => -((m : ℕ) : ℤ)))) ?_
    intro k hk
    have hk' : k.natAbs ≤ n := hk
    rcases Int.natAbs_eq k with hc | hc
    · exact Or.inl ⟨⟨k.natAbs, by omega⟩, hc.symm⟩
    · exact Or.inr ⟨⟨k.natAbs, by omega⟩, hc.symm⟩
  refine ⟨((L + 2 * n : ℕ) : ℝ), {k : ℤ | k.natAbs ≤ n}.ncard, ?_⟩
  intro x y hxy
  have hxyN : L + 2 * n ≤ H.dist (TreeSpace.val x) (TreeSpace.val y) := by
    have h : ((L + 2 * n : ℕ) : ℝ)
        ≤ ((H.dist (TreeSpace.val x) (TreeSpace.val y) : ℕ) : ℝ) := hxy
    exact_mod_cast h
  obtain ⟨u, w, Φ, hL, hΦ⟩ :=
    hshift n (TreeSpace.val x) (TreeSpace.val y) hxyN
  have hmem : ∀ g : G, g ∈ {g : G | dist x (g • x) ≤ ε ∧ dist y (g • y) ≤ ε} →
      H.dist (TreeSpace.val x) (g • TreeSpace.val x) ≤ n ∧
        H.dist (TreeSpace.val y) (g • TreeSpace.val y) ≤ n := by
    rintro g ⟨h1, h2⟩
    have e1 : ((H.dist (TreeSpace.val x) (g • TreeSpace.val x) : ℕ) : ℝ)
        ≤ (n : ℝ) := le_trans h1 hn
    have e2 : ((H.dist (TreeSpace.val y) (g • TreeSpace.val y) : ℕ) : ℝ)
        ≤ (n : ℝ) := le_trans h2 hn
    exact ⟨by exact_mod_cast e1, by exact_mod_cast e2⟩
  have hinj : Set.InjOn Φ
      {g : G | dist x (g • x) ≤ ε ∧ dist y (g • y) ≤ ε} := by
    intro g₁ hg₁ g₂ hg₂ heq
    obtain ⟨ha₁, hb₁⟩ := hmem g₁ hg₁
    obtain ⟨ha₂, hb₂⟩ := hmem g₂ hg₂
    obtain ⟨-, hcoset⟩ := hΦ g₁ ha₁ hb₁
    obtain ⟨hu, hw⟩ := hcoset g₂ ha₂ hb₂ heq
    have ku : (g₂⁻¹ * g₁) • u = u := by
      rw [mul_smul, hu, inv_smul_smul]
    have kw : (g₂⁻¹ * g₁) • w = w := by
      rw [mul_smul, hw, inv_smul_smul]
    exact (inv_mul_eq_one.mp (hstab u w hL (g₂⁻¹ * g₁) ku kw)).symm
  have hmaps : ∀ g ∈ {g : G | dist x (g • x) ≤ ε ∧ dist y (g • y) ≤ ε},
      Φ g ∈ {k : ℤ | k.natAbs ≤ n} := by
    intro g hg
    exact (hΦ g (hmem g hg).1 (hmem g hg).2).1
  have himg : Φ '' {g : G | dist x (g • x) ≤ ε ∧ dist y (g • y) ≤ ε}
      ⊆ {k : ℤ | k.natAbs ≤ n} := by
    rintro k ⟨g, hg, rfl⟩
    exact hmaps g hg
  exact ⟨Set.Finite.of_finite_image (hfin.subset himg) hinj,
    Set.ncard_le_ncard_of_injOn Φ hmaps hinj hfin⟩

/-! ## What is still missing -/

/-- **The tree shift lemma**, written down as the statement this module does not
prove.

An automorphism of a tree that moves two vertices at distance at least `L + 2n`
by at most `n` each maps the middle segment of `[x,y]` onto itself by a shift of
bounded size.  The reason the statement below asserts only the *consequence*
`HasSegmentShift` is that the consequence is what the count needs: an integer
invariant of bounded size whose level sets agree on the ends of the middle
segment.

Sketch of the missing proof.  Both `m_i` for `n ≤ i ≤ d(x,y) - n` and `g·m_i`
lie on the geodesic `[g·x, g·y]`, because each is within `n` of an endpoint's
image; on a geodesic a point is determined by its distance to one end;
`d(g·x, g·m_i) = i` while `d(g·x, m_i) = i + k` with
`k = d(x,g·x) - 2 (g·x | y)_x` independent of `i`; so `g·m_i = m_{i-k}` and
`|k| ≤ n`.  Formalising it is a `Walk` and geodesic exercise, not a new idea. -/
def SegmentShiftStatement : Prop :=
  ∀ (G : Type) [Group G] (V : Type) (H : SimpleGraph V) [MulAction G V]
    (L : ℕ), H.IsTree →
      (∀ (g : G) (u w : V), H.Adj u w → H.Adj (g • u) (g • w)) →
        HasSegmentShift G H L

/-- **The general acylindricity criterion for tree actions**, with *bounded*
rather than trivial segment stabilisers, written down as the statement this
module does not prove.

It follows from `SegmentShiftStatement` by a coset count: the level sets of the
shift invariant on the `ε`-stabiliser of the pair are cosets of the pointwise
stabiliser of the middle segment, so the stabiliser has at most
`(2⌈ε⌉ + 1) · N` elements.  `isAcylindrical_treeSpace` is the case `N = 1`,
where the count degenerates to an injection and is proved outright. -/
def TreeAcylindricityStatement : Prop :=
  ∀ (G : Type) [Group G] (V : Type) (H : SimpleGraph V) [MulAction G V]
    (hH : H.IsTree) (L N : ℕ),
      (∀ (g : G) (u w : V), H.Adj u w → H.Adj (g • u) (g • w)) →
        BoundedSegmentStabilizers G H L N → IsAcylindrical G (TreeSpace hH)

end GGT
end GroupApproximation
