import GroupApproximation.GGT.ElementaryMorseOrbit

/-!
# Two chains with the same constants, and what the bi-infinite case still needs

`GGT.ElementaryMorseChord` proves both halves of the segment Morse lemma with
the constants chosen before the chain: `exists_bound_chord_near_chain` puts every
point of a chord within `K` of a chain vertex, and `exists_bound_chain_near_chord`
puts every chain vertex within `K` of a chord point.  Composing them gives the
**two-chain** form, which is what an axis argument actually wants:

> two chains with the same step bound, the same progress rate, and *the same
> endpoints* have every vertex of one within a uniform `K` of some vertex of the
> other.

That is `exists_bound_chain_near_chain` below, proved outright.  The uniformity
is inherited: the two constants come out of the chord lemmas before either chain
is named, so `K` does not see the chains at all.

## Why this is the right shape for `E(h)`

For `g` commuting with a power `h^p`, `GGT.ElementaryMorse.orbitChain_smul_of_commute`
says the `g`-translate of the `h^p`-orbit chain through `x` *is* the `h^p`-orbit
chain through `g • x`, and `dist_zpow_smul_translate_of_commute` says it carries
the same step bound.  So the two objects to compare are two orbit chains of the
same element with the same constants --- exactly the hypothesis above, except for
the endpoints.

## The endpoints, and the leaf

On a window `[-n, n]` the two orbit chains do **not** share endpoints: they are
`d(x, g • x)` apart, and that distance is not bounded uniformly over `g ∈ E(h)`.
So `exists_bound_chain_near_chain` does not apply directly, and the honest
statement of what the segment form lacks is this.

The two chords of a window --- the geodesic from `y(-n)` to `y(n)` and the one
from `z(-n)` to `z(n)` --- form a geodesic quadrilateral whose two *short* sides
have length `d(x, g • x)`.  A point of one long side that is farther than that
length from both ends is within `2δ` of the other long side, by thinness; the
exceptional region sits at the ends and has size `d(x, g • x)`, so it is not
uniform, but it recedes as the window grows.  Any fixed vertex therefore ends up
in the uniform middle, and the resulting bound `K + 2δ + K'` does not depend on
`g`.  That is where the constant stops depending on the element, and it matches
Dahmani--Guirardel--Osin's `ϰ` on p.88 of arXiv:1111.7048.

`ChordsFellowTravelAwayFromEnds` names precisely that quadrilateral step and
nothing more.  It is a statement about four points of a hyperbolic space with no
group, no chain and no orbit in it, and it is the only thing between
`exists_bound_chain_near_chain` and the bi-infinite statement.  The repository's
`HullGeometry.exists_close_on_other_side_of_geodesic_triangle` gives `3δ`-thin
triangles, so a quadrilateral splits into two triangles at `6δ`; what that does
not by itself supply is the *localisation* --- that the failure is confined to
within the short sides' length of the ends --- which is the content below.
-/

namespace GroupApproximation
namespace GGT
namespace ElementaryMorse

open GroupApproximation.HullGeometry

universe v

variable {X : Type v} [PseudoMetricSpace X]

/-! ## Two chains with the same endpoints -/

/-- **The two-chain Morse lemma, at equal endpoints.**

Two chains with the same step bound `D`, the same progress rate `l` and slack
`B`, and the same first and last vertices, shadow each other: every vertex of one
lies within `K` of a vertex of the other, and `K` is chosen before either chain.

The proof is one composition: a vertex of the second chain is near the common
chord by `exists_bound_chain_near_chord`, and that point of the chord is near a
vertex of the first by `exists_bound_chord_near_chain`. -/
theorem exists_bound_chain_near_chain {δ D l B : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (hD0 : 0 ≤ D) (hl : 0 < l)
    (hB0 : 0 ≤ B) (hgeo : IsGeodesicSpace X) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (y z : ℕ → X) (N : ℕ),
      (∀ i, i < N → dist (y i) (y (i + 1)) ≤ D) →
      (∀ i j, i ≤ j → j ≤ N → l * ((j - i : ℕ) : ℝ) - B ≤ dist (y i) (y j)) →
      (∀ i, i < N → dist (z i) (z (i + 1)) ≤ D) →
      (∀ i j, i ≤ j → j ≤ N → l * ((j - i : ℕ) : ℝ) - B ≤ dist (z i) (z j)) →
      y 0 = z 0 → y N = z N →
        ∀ j, j ≤ N → ∃ i, i ≤ N ∧ dist (z j) (y i) ≤ K := by
  obtain ⟨K₁, hK₁0, hK₁⟩ := exists_bound_chord_near_chain hδ hδ0 hD0 hl hB0
  obtain ⟨K₂, hK₂0, hK₂⟩ := exists_bound_chain_near_chord hδ hδ0 hD0 hl hB0
  refine ⟨K₂ + K₁, by linarith, ?_⟩
  intro y z N hyedge hyprog hzedge hzprog h0 hN j hjN
  obtain ⟨f, hf, hf0, hfL⟩ := hgeo (y 0) (y N)
  have hL0 : (0 : ℝ) ≤ dist (y 0) (y N) := dist_nonneg
  have hfz0 : f 0 = z 0 := by rw [hf0, h0]
  have hfzL : f (dist (y 0) (y N)) = z N := by rw [hfL, hN]
  obtain ⟨t, ht, htz⟩ :=
    hK₂ z N hzedge hzprog (dist (y 0) (y N)) hL0 f hf hfz0 hfzL j hjN
  obtain ⟨i, hiN, hiy⟩ :=
    hK₁ y N hyedge hyprog (dist (y 0) (y N)) hL0 f hf hf0 hfL t ht
  refine ⟨i, hiN, ?_⟩
  calc dist (z j) (y i) ≤ dist (z j) (f t) + dist (f t) (y i) :=
        dist_triangle _ _ _
    _ ≤ K₂ + K₁ := by
        have h1 : dist (f t) (y i) = dist (y i) (f t) := dist_comm _ _
        rw [h1]
        exact add_le_add htz hiy

/-! ## What the bi-infinite case needs, and nothing more -/

/-- **The quadrilateral localisation step.**

Let two geodesics `p` and `q`, of lengths `Lp` and `Lq`, have endpoints within
`E` of each other --- `d(p 0, q 0) ≤ E` and `d(p Lp, q Lq) ≤ E`.  Then a point of
`p` at parameter farther than `E + C` from both ends of `p` lies within `C` of
some point of `q`.

The constant `C` is existential and internal to the statement, so the
hyperbolicity constant does not appear as a parameter: a discharge will produce
`C` from the `δ` of whatever hyperbolicity hypothesis it carries.

This is the one thing the segment Morse lemma does not supply.  Its content is
not thinness --- the repository already has `3δ`-thin triangles, so a
quadrilateral is `6δ`-thin --- but the *localisation*: the failure is confined to
within `E` of the ends, so a vertex that the window has pushed into the middle
gets a bound with no `E` in it.  That is exactly why the constant in the axis
argument stops depending on the group element: `E` is `d(x, g • x)`, which is not
uniform, but it only ever appears in the description of the excluded region.

Stated over four points of a hyperbolic space, with no group, no chain and no
orbit, so that discharging it needs nothing from this development. -/
def ChordsFellowTravelAwayFromEnds (X : Type v) [PseudoMetricSpace X] : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (E Lp Lq : ℝ), 0 ≤ E → 0 ≤ Lp → 0 ≤ Lq →
    ∀ p q : ℝ → X, IsGeodesicSegment p 0 Lp → IsGeodesicSegment q 0 Lq →
      dist (p 0) (q 0) ≤ E → dist (p Lp) (q Lq) ≤ E →
        ∀ s : ℝ, E + C ≤ s → s + E + C ≤ Lp →
          ∃ t ∈ Set.Icc (0 : ℝ) Lq, dist (p s) (q t) ≤ C

end ElementaryMorse
end GGT
end GroupApproximation
