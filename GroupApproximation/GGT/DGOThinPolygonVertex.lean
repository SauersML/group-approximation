import GroupApproximation.Algebra.HyperbolicSlimFourPoint

/-!
# Thin triangles at the vertices, for Dahmani--Guirardel--Osin's Lemma 4.15

Their §4.2 needs a polygon to be thin *at its vertices*: the corner-offset
construction of Lemma 4.16 picks a point `u` on one side and needs a point `v`
**on another side** near it, because the cycle it builds is assembled from
segments of the sides, and the reason those segments are safe is that the
distinguished component is isolated in the polygon they came from.  A point
merely lying metrically between two corners is no use: it is not on the word,
so nothing is known about the letters around it.

## Why this is stated over `ℕ`, on `wordDist`

`Sofic/HullSuitabilityGeometry.lean` has thin triangles over `ℝ`, for sides
given as `IsGeodesicSegment f 0 L` in a `PseudoMetricSpace`.  That form cannot
be used here.  A side of a polygon in `Γ(G, X ⊔ ℋ)` is a *word*, and its vertex
set carries `wordDist`, which is not a geodesic metric --- between two vertices
at distance `n` there is no continuum of points, so no `IsGeodesicSegment` joins
them.  (The realisation `CayleyGeodesicModel.Point` does have geodesics; the
vertex model does not, and it is the vertex model the polygon lives in.)

`Algebra/HyperbolicSlimTriangles.lean` is stated in exactly the right
vocabulary: `IsBetween S b p c` is `d(b,p) + d(p,c) = d(b,c)`, which needs no
paths, and `Hyperbolic.isSlimTriangles_of_isFourPointHyperbolic` proves
`IsSlimTriangles S (4 * δ)` from the four-point condition.  What it delivers is
a point *between* two corners.  This module supplies the missing half-step: a
between-point is `2δ` from an indexed vertex of any geodesic chain with those
endpoints.

## The half-step is one four-point application

If `p` and `q` both lie between `x` and `z` and are at the same distance from
`x`, then `d(x,p) + d(z,q)` and `d(x,q) + d(z,p)` both equal `d(x,z)`, so the
four-point condition read at `(x, z, p, q)` says

    d(x,z) + d(p,q) ≤ d(x,z) + 2δ .

That is `wordDist_le_two_mul_of_isBetween`, and it is the whole content: a
between-point at parameter `t` and the chain vertex at index `t` are two points
between the same endpoints at the same distance from one of them.

## Constants

`4δ` from slimness, `2δ` from the half-step, so `6δ` for a triangle.  Nothing
here is sharp and nothing downstream needs it to be: Lemma 4.16 only asks for
*some* `θ` with quadrangle thinness, and its corner offset is `θ + 1`.

At `μ = 1`, `b = 0` a quasi-geodesic side of `OsinComponents.IsQuasiGeodesicPolygon`
is exactly an `IsGeodesicChain`, so this is the regime where Lemma 4.15 costs
no stability theorem at all.  For `b > 0` a side is a quasi-geodesic chain and
the constant is Morse's; `ElementaryMorseChord.exists_bound_chord_near_chain`
proves that, but over `ℝ` and against an `IsGeodesicSegment` chord, so it is the
realisation and not the vertex model that would have to carry it.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.WordMetric

universe u

variable {G : Type u} [Group G]

/-! ## Geodesic chains -/

/-- **A geodesic chain**: an indexed family of vertices whose word distance is
the difference of the indices.  A geodesic side of a polygon in
`Γ(G, X ⊔ ℋ)`, read through `OsinComponents.vertex`, is one of these --- the
lower bound is the `μ = 1`, `b = 0` quasi-geodesic clause and the upper bound is
automatic, consecutive vertices being one letter apart. -/
def IsGeodesicChain (S : Set G) (y : ℕ → G) (n : ℕ) : Prop :=
  ∀ i j : ℕ, i ≤ j → j ≤ n → wordDist S (y i) (y j) = j - i

/-- Every vertex of a geodesic chain lies between its endpoints. -/
theorem IsGeodesicChain.isBetween {S : Set G} {y : ℕ → G} {n : ℕ}
    (hy : IsGeodesicChain S y n) {i : ℕ} (hi : i ≤ n) :
    Hyperbolic.IsBetween S (y 0) (y i) (y n) := by
  have h1 : wordDist S (y 0) (y i) = i := by
    simpa using hy 0 i (Nat.zero_le i) hi
  have h2 : wordDist S (y i) (y n) = n - i := hy i n hi le_rfl
  have h3 : wordDist S (y 0) (y n) = n := by
    simpa using hy 0 n (Nat.zero_le n) le_rfl
  show wordDist S (y 0) (y i) + wordDist S (y i) (y n) = wordDist S (y 0) (y n)
  omega

/-! ## The half-step: from a between-point to a vertex -/

/-- **Two between-points at the same distance from an endpoint are `2δ` apart.**
One application of the four-point condition at `(x, z, p, q)`: both of the
competing pairings equal `d(x,z)`, so the maximum is `d(x,z)` and `d(p,q)` is
what the slack `2δ` has to cover. -/
theorem wordDist_le_two_mul_of_isBetween {S : Set G} {δ : ℕ}
    (hS : IsSymmetricGeneratingSet S)
    (hδ : Hyperbolic.IsFourPointHyperbolic S δ) {x z p q : G}
    (hp : Hyperbolic.IsBetween S x p z) (hq : Hyperbolic.IsBetween S x q z)
    (heq : wordDist S x p = wordDist S x q) :
    wordDist S p q ≤ 2 * δ := by
  have h := hδ x z p q
  have h1 : wordDist S x p + wordDist S p z = wordDist S x z := hp
  have h2 : wordDist S x q + wordDist S q z = wordDist S x z := hq
  have hzp : wordDist S z p = wordDist S p z := wordDist_comm hS z p
  have hzq : wordDist S z q = wordDist S q z := wordDist_comm hS z q
  omega

/-- **A between-point is `2δ` from an indexed vertex of the chain.**  The index
is the distance from the initial vertex, which is what makes the two points
comparable by `wordDist_le_two_mul_of_isBetween`. -/
theorem exists_index_wordDist_le_of_isBetween {S : Set G} {δ : ℕ}
    (hS : IsSymmetricGeneratingSet S)
    (hδ : Hyperbolic.IsFourPointHyperbolic S δ)
    {y : ℕ → G} {n : ℕ} (hy : IsGeodesicChain S y n) {q : G}
    (hq : Hyperbolic.IsBetween S (y 0) q (y n)) :
    ∃ j : ℕ, j ≤ n ∧ wordDist S q (y j) ≤ 2 * δ := by
  have hxz : wordDist S (y 0) (y n) = n := by
    simpa using hy 0 n (Nat.zero_le n) le_rfl
  have hq' : wordDist S (y 0) q + wordDist S q (y n) = wordDist S (y 0) (y n) := hq
  refine ⟨wordDist S (y 0) q, by omega, ?_⟩
  have hjn : wordDist S (y 0) q ≤ n := by omega
  have h1 : wordDist S (y 0) (y (wordDist S (y 0) q)) = wordDist S (y 0) q := by
    simpa using hy 0 (wordDist S (y 0) q) (Nat.zero_le _) hjn
  exact wordDist_le_two_mul_of_isBetween hS hδ hq (hy.isBetween hjn) h1.symm

/-! ## Thin triangles at the vertices -/

/-- **Dahmani--Guirardel--Osin's Lemma 4.15 for a triangle, at the vertices and
at `μ = 1`, `b = 0`.**  Three geodesic chains closing up into a triangle: every
vertex of the first is within `6δ` of a vertex of one of the other two.

The corners are `a 0 = b 0`, `a na = c nc` and `b nb = c 0`. -/
theorem exists_index_wordDist_le_of_triangle {S : Set G} {δ : ℕ}
    (hS : IsSymmetricGeneratingSet S)
    (hδ : Hyperbolic.IsFourPointHyperbolic S δ)
    {a b c : ℕ → G} {na nb nc : ℕ}
    (ha : IsGeodesicChain S a na) (hb : IsGeodesicChain S b nb)
    (hc : IsGeodesicChain S c nc)
    (hab : b 0 = a 0) (hbc : c 0 = b nb) (hca : c nc = a na)
    {i : ℕ} (hi : i ≤ na) :
    (∃ j : ℕ, j ≤ nb ∧ wordDist S (a i) (b j) ≤ 6 * δ) ∨
      (∃ j : ℕ, j ≤ nc ∧ wordDist S (a i) (c j) ≤ 6 * δ) := by
  have hslim := Hyperbolic.isSlimTriangles_of_isFourPointHyperbolic hS hδ
  rcases hslim (a 0) (a na) (b nb) (a i) (ha.isBetween hi) with
    ⟨q, hq, hd⟩ | ⟨q, hq, hd⟩
  · refine Or.inl ?_
    have hq' : Hyperbolic.IsBetween S (b 0) q (b nb) := by
      rw [hab]
      exact hq
    obtain ⟨j, hjn, hj⟩ := exists_index_wordDist_le_of_isBetween hS hδ hb hq'
    refine ⟨j, hjn, ?_⟩
    have htri := wordDist_triangle hS (a i) q (b j)
    omega
  · refine Or.inr ?_
    have hq' : Hyperbolic.IsBetween S (c 0) q (c nc) := by
      rw [hbc, hca]
      exact hq
    obtain ⟨j, hjn, hj⟩ := exists_index_wordDist_le_of_isBetween hS hδ hc hq'
    refine ⟨j, hjn, ?_⟩
    have htri := wordDist_triangle hS (a i) q (c j)
    omega

/-! ## Thin quadrangles, before the half-step -/

/-- **Dahmani--Guirardel--Osin's Lemma 4.15 for a quadrangle, in the
between-vocabulary.**  For four corners `x₁ → x₂ → x₃ → x₄ → x₁` and a point `p`
between `x₁` and `x₂`, there is a point of one of the other three sides within
`8δ` of `p`, given as a *between-point* rather than as an index.

This is the whole geometric content of
`exists_index_wordDist_le_of_quadrangle`: two applications of slimness, once
across the diagonal `[x₁,x₃]` and once across `[x₁,x₄]`, so that no diagonal
chain has to be built.  What that theorem adds is the half-step
`exists_index_wordDist_le_of_isBetween`, which converts a between-point into an
indexed vertex --- and *that* step is the one that needs the side to be a
geodesic chain.

Keeping the two apart is what lets a side of the polygon be **exempt** from the
quasi-geodesic clause.  Dahmani--Guirardel--Osin's Definition 4.13 exempts the
sides that are components of the polygon, and the corner-offset construction of
their Lemma 4.16 never uses an index on the distinguished side: it *discards*
that alternative by the offset count.  A between-point is all the discard needs,
so the exempt side may be an arbitrary run of `lam`-letters.

The constant is `4δ` for the alternative reached by one cut and `8δ` for the two
reached by two; the half-step costs a further `2δ`, which is where the `10δ` of
the indexed form comes from. -/
theorem exists_isBetween_of_quadrangle {S : Set G} {δ : ℕ}
    (hS : IsSymmetricGeneratingSet S)
    (hδ : Hyperbolic.IsFourPointHyperbolic S δ) {x₁ x₂ x₃ x₄ p : G}
    (hp : Hyperbolic.IsBetween S x₁ p x₂) :
    (∃ q : G, Hyperbolic.IsBetween S x₂ q x₃ ∧ wordDist S p q ≤ 4 * δ) ∨
      (∃ q : G, Hyperbolic.IsBetween S x₃ q x₄ ∧ wordDist S p q ≤ 8 * δ) ∨
        (∃ q : G, Hyperbolic.IsBetween S x₄ q x₁ ∧ wordDist S p q ≤ 8 * δ) := by
  have hslim := Hyperbolic.isSlimTriangles_of_isFourPointHyperbolic hS hδ
  rcases hslim x₁ x₂ x₃ p hp with ⟨q, hq, hd⟩ | ⟨q, hq, hd⟩
  · -- `q` lies on the diagonal `[x₁, x₃]`; cut a second time across `[x₁, x₄]`
    rcases hslim x₁ x₃ x₄ q hq with ⟨r, hr, hdr⟩ | ⟨r, hr, hdr⟩
    · refine Or.inr (Or.inr ⟨r, Hyperbolic.IsBetween.symm hS hr, ?_⟩)
      have h1 := wordDist_triangle hS p q r
      omega
    · refine Or.inr (Or.inl ⟨r, Hyperbolic.IsBetween.symm hS hr, ?_⟩)
      have h1 := wordDist_triangle hS p q r
      omega
  · exact Or.inl ⟨q, Hyperbolic.IsBetween.symm hS hq, hd⟩

/-! ## Thin quadrangles at the vertices -/

/-- **Dahmani--Guirardel--Osin's Lemma 4.15, at the vertices and at `μ = 1`,
`b = 0`.**  Four geodesic chains closing up into a quadrangle
`x₁ → x₂ → x₃ → x₄ → x₁`, with `x₁ = a 0`, `x₂ = a na = b 0`, `x₃ = b nb = c 0`
and `x₄ = c nc = e 0`: every vertex of the first side is within `10δ` of a
vertex of one of the other three.

Slimness is applied twice in the between-vocabulary --- once across the diagonal
`[x₁,x₃]`, once across `[x₁,x₄]` --- so no diagonal *chain* has to be built, and
the half-step to an actual vertex is applied once, at the end.  The diagonal is
auxiliary in Dahmani--Guirardel--Osin's argument too: what their Lemma 4.16
consumes is only that the near point lies on a *side* of the polygon, since the
cycle it assembles is made of segments of sides and their safety comes from the
distinguished component being isolated in that polygon. -/
theorem exists_index_wordDist_le_of_quadrangle {S : Set G} {δ : ℕ}
    (hS : IsSymmetricGeneratingSet S)
    (hδ : Hyperbolic.IsFourPointHyperbolic S δ)
    {a b c e : ℕ → G} {na nb nc ne : ℕ}
    (ha : IsGeodesicChain S a na) (hb : IsGeodesicChain S b nb)
    (hc : IsGeodesicChain S c nc) (he : IsGeodesicChain S e ne)
    (hab : b 0 = a na) (hbc : c 0 = b nb) (hce : e 0 = c nc)
    (hea : e ne = a 0)
    {i : ℕ} (hi : i ≤ na) :
    (∃ j : ℕ, j ≤ nb ∧ wordDist S (a i) (b j) ≤ 10 * δ) ∨
      (∃ j : ℕ, j ≤ nc ∧ wordDist S (a i) (c j) ≤ 10 * δ) ∨
        (∃ j : ℕ, j ≤ ne ∧ wordDist S (a i) (e j) ≤ 10 * δ) := by
  have hslim := Hyperbolic.isSlimTriangles_of_isFourPointHyperbolic hS hδ
  rcases hslim (a 0) (a na) (b nb) (a i) (ha.isBetween hi) with
    ⟨q, hq, hd⟩ | ⟨q, hq, hd⟩
  · -- `q` lies on the diagonal `[x₁, x₃]`; cut a second time across `[x₁, x₄]`
    rcases hslim (a 0) (b nb) (c nc) q hq with ⟨r, hr, hdr⟩ | ⟨r, hr, hdr⟩
    · refine Or.inr (Or.inr ?_)
      have hr' : Hyperbolic.IsBetween S (e 0) r (e ne) := by
        rw [hea, hce]
        exact Hyperbolic.IsBetween.symm hS hr
      obtain ⟨j, hjn, hj⟩ := exists_index_wordDist_le_of_isBetween hS hδ he hr'
      refine ⟨j, hjn, ?_⟩
      have h1 := wordDist_triangle hS (a i) q r
      have h2 := wordDist_triangle hS (a i) r (e j)
      omega
    · refine Or.inr (Or.inl ?_)
      have hr' : Hyperbolic.IsBetween S (c 0) r (c nc) := by
        rw [hbc]
        exact Hyperbolic.IsBetween.symm hS hr
      obtain ⟨j, hjn, hj⟩ := exists_index_wordDist_le_of_isBetween hS hδ hc hr'
      refine ⟨j, hjn, ?_⟩
      have h1 := wordDist_triangle hS (a i) q r
      have h2 := wordDist_triangle hS (a i) r (c j)
      omega
  · refine Or.inl ?_
    have hq' : Hyperbolic.IsBetween S (b 0) q (b nb) := by
      rw [hab]
      exact Hyperbolic.IsBetween.symm hS hq
    obtain ⟨j, hjn, hj⟩ := exists_index_wordDist_le_of_isBetween hS hδ hb hq'
    refine ⟨j, hjn, ?_⟩
    have htri := wordDist_triangle hS (a i) q (b j)
    omega

end GGT
end GroupApproximation
