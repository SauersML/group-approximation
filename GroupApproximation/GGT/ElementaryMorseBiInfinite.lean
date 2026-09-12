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
group, no chain and no orbit in it.  The repository's
`HullGeometry.exists_close_on_other_side_of_geodesic_triangle` gives `3δ`-thin
triangles, so a quadrilateral splits into two triangles at `6δ`; the
localisation proved below confines the failure to within the short sides'
length of the ends.

`exists_bound_middle_chain_near_chain` now composes that localisation with the
two finite-chain Morse directions.  Thus the only remaining step to the DGO
bi-infinite axis conclusion is group-specific bookkeeping: take arbitrarily
large windows whose radius is a multiple of the exponent in
`a hⁿ a⁻¹ = h^{±n}`, reversing the comparison chain in the negative-sign case.
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


/-! ### The localisation step, proved

Not a leaf after all.  The quadrilateral splits along the diagonal from `p 0` to
`q Lq` into two triangles and `3δ`-thinness is applied once in each.  Both
alternatives that would fail are killed by the same inequality: the point `p s`
is at distance `s` from `p 0` and `Lp - s` from `p Lp`, and the hypotheses put
both above `E + C`, while landing on a short side would put one of them below
`3δ + E` or `6δ + E`.  With `C = 6δ + 1` those are incompatible.

The surviving branch gives `3δ + 3δ`, and `E` occurs in neither conclusion ---
only inside the two contradictions.  That is the localisation: the failure is
confined to within `E` of the ends, so the constant that comes out has no `E`
in it. -/

/-- **The quadrilateral localisation step**, from `3δ`-thin geodesic triangles. -/
theorem chordsFellowTravelAwayFromEnds_of_geodesic {δ : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (hgeo : IsGeodesicSpace X) :
    ChordsFellowTravelAwayFromEnds X := by
  refine ⟨6 * δ + 1, by linarith, ?_⟩
  intro E Lp Lq hE hLp hLq p q hp hq h0 h1 s hs1 hs2
  have hs0 : 0 ≤ s := by linarith
  have hsLp : s ≤ Lp := by linarith
  have hLpe : dist (p 0) (p Lp) = Lp := by
    rw [hp.dist_endpoints hLp, sub_zero]
  have hLqe : dist (q 0) (q Lq) = Lq := by
    rw [hq.dist_endpoints hLq, sub_zero]
  have hE1 : dist (q Lq) (p Lp) ≤ E := by rw [dist_comm]; exact h1
  -- the two distances from `p s` to the ends of `p`
  have hpend : dist (p s) (p Lp) = Lp - s := by
    rw [hp s ⟨hs0, hsLp⟩ Lp ⟨hLp, le_rfl⟩,
      abs_of_nonpos (by linarith : s - Lp ≤ 0)]
    ring
  have hpstart : dist (p s) (p 0) = s := by
    rw [hp s ⟨hs0, hsLp⟩ 0 ⟨le_rfl, hLp⟩,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ s - 0)]
    ring
  -- the diagonal and the two short sides
  obtain ⟨g, hg, hg0, hg1⟩ := hgeo (p 0) (q Lq)
  obtain ⟨e1, he1, he10, he11⟩ := hgeo (q Lq) (p Lp)
  obtain ⟨e2, he2, he20, he21⟩ := hgeo (p 0) (q 0)
  have hde1 : ∀ u ∈ Set.Icc (0 : ℝ) (dist (q Lq) (p Lp)),
      dist (e1 u) (p Lp) ≤ E := by
    intro u hu
    have h := he1 u hu (dist (q Lq) (p Lp)) ⟨dist_nonneg, le_rfl⟩
    rw [he11] at h
    rw [h, abs_of_nonpos (by linarith [hu.2] : u - dist (q Lq) (p Lp) ≤ 0)]
    linarith [hu.1]
  have hde2 : ∀ w ∈ Set.Icc (0 : ℝ) (dist (p 0) (q 0)),
      dist (e2 w) (p 0) ≤ E := by
    intro w hw
    have h := he2 w hw 0 ⟨le_rfl, dist_nonneg⟩
    rw [he20] at h
    rw [h, abs_of_nonneg (by linarith [hw.1] : (0 : ℝ) ≤ w - 0)]
    linarith [hw.2]
  -- `p` and `q` re-parametrised by their own endpoint distances
  have hpAC : IsGeodesicSegment p 0 (dist (p 0) (p Lp)) := by rw [hLpe]; exact hp
  have hpAC1 : p (dist (p 0) (p Lp)) = p Lp := by rw [hLpe]
  have hqBC : IsGeodesicSegment q 0 (dist (q 0) (q Lq)) := by rw [hLqe]; exact hq
  have hqBC1 : q (dist (q 0) (q Lq)) = q Lq := by rw [hLqe]
  have hsmem : s ∈ Set.Icc (0 : ℝ) (dist (p 0) (p Lp)) := by
    rw [hLpe]; exact ⟨hs0, hsLp⟩
  -- first triangle: vertices `p 0`, `q Lq`, `p Lp`
  rcases exists_close_on_other_side_of_geodesic_triangle hδ hδ0
      hpAC rfl hpAC1 hg hg0 hg1 he1 he10 he11 hsmem with
    ⟨u, hu, hpu⟩ | ⟨u, hu, hpu⟩
  · -- second triangle: vertices `p 0`, `q 0`, `q Lq`
    rcases exists_close_on_other_side_of_geodesic_triangle hδ hδ0
        hg hg0 hg1 he2 he20 he21 hqBC rfl hqBC1 hu with
      ⟨w, hw, hgw⟩ | ⟨w, hw, hgw⟩
    · -- the diagonal point is near the short side `[p 0, q 0]`: impossible
      exfalso
      have htri := dist_triangle4 (p s) (g u) (e2 w) (p 0)
      have hbad := hde2 w hw
      rw [hpstart] at htri
      linarith
    · -- the diagonal point is near `q`: this is the conclusion
      refine ⟨w, ?_, ?_⟩
      · rw [← hLqe]; exact hw
      · have htri := dist_triangle (p s) (g u) (q w)
        linarith
  · -- `p s` is near the short side `[q Lq, p Lp]`: impossible
    exfalso
    have htri := dist_triangle (p s) (e1 u) (p Lp)
    have hbad := hde1 u hu
    rw [hpend] at htri
    linarith

/-! ## The uniform middle of two endpoint-close chains -/

/-- **Endpoint-close quasi-geodesic chains fellow travel uniformly away from
the ends.**

The endpoint error `E` is allowed to depend on the two chains.  It occurs only
in the two hypotheses saying that the chosen vertex lies far enough from the
ends; the resulting distance bound `K` is chosen before `E`, the chains, their
length, and the vertex.  This is the finite-window statement needed for DGO's
bi-infinite quasi-axis argument.

The proof is the source argument verbatim at chain level.  Put the chosen
vertex of `z` near the chord spanning `z`, use
`ChordsFellowTravelAwayFromEnds` to cross to the chord spanning `y`, and put
that chord point near a vertex of `y`.  The progress inequalities ensure that
the first chord point is outside the two exceptional end regions. -/
theorem exists_bound_middle_chain_near_chain {δ D l B : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (hD0 : 0 ≤ D)
    (hl : 0 < l) (hB0 : 0 ≤ B) (hgeo : IsGeodesicSpace X) :
    ∃ K R : ℝ, 0 ≤ K ∧ 0 ≤ R ∧
      ∀ (E : ℝ), 0 ≤ E → ∀ (y z : ℕ → X) (N : ℕ),
      (∀ i, i < N → dist (y i) (y (i + 1)) ≤ D) →
      (∀ i j, i ≤ j → j ≤ N →
        l * ((j - i : ℕ) : ℝ) - B ≤ dist (y i) (y j)) →
      (∀ i, i < N → dist (z i) (z (i + 1)) ≤ D) →
      (∀ i j, i ≤ j → j ≤ N →
        l * ((j - i : ℕ) : ℝ) - B ≤ dist (z i) (z j)) →
      dist (z 0) (y 0) ≤ E → dist (z N) (y N) ≤ E →
      ∀ j, j ≤ N →
        E + R + B ≤ l * (j : ℝ) →
        E + R + B ≤ l * ((N - j : ℕ) : ℝ) →
        ∃ i, i ≤ N ∧ dist (z j) (y i) ≤ K := by
  obtain ⟨K₁, hK₁0, hchordNear⟩ :=
    exists_bound_chord_near_chain hδ hδ0 hD0 hl hB0
  obtain ⟨K₂, hK₂0, hchainNear⟩ :=
    exists_bound_chain_near_chord hδ hδ0 hD0 hl hB0
  obtain ⟨C, hC0, hquad⟩ :=
    chordsFellowTravelAwayFromEnds_of_geodesic hδ hδ0 hgeo
  refine ⟨K₂ + C + K₁, C + K₂, by linarith, by linarith, ?_⟩
  intro E hE y z N hyEdge hyProg hzEdge hzProg hclose0 hcloseN
    j hjN hfar0 hfarN
  let Ly : ℝ := dist (y 0) (y N)
  let Lz : ℝ := dist (z 0) (z N)
  obtain ⟨p, hp, hp0, hp1⟩ := hgeo (y 0) (y N)
  obtain ⟨q, hq, hq0, hq1⟩ := hgeo (z 0) (z N)
  obtain ⟨s, hs, hzs⟩ := hchainNear z N hzEdge hzProg
    Lz dist_nonneg q hq hq0 hq1 j hjN
  have hzs' : dist (q s) (z j) ≤ K₂ := by
    rwa [dist_comm]
  have hs0 : E + C ≤ s := by
    have hprog := hzProg 0 j (Nat.zero_le j) hjN
    simp only [Nat.sub_zero] at hprog
    have hparam : dist (q 0) (q s) = s := by
      rw [hq 0 ⟨le_rfl, dist_nonneg⟩ s hs, zero_sub, abs_neg,
        abs_of_nonneg hs.1]
    have htri := dist_triangle (q 0) (q s) (z j)
    rw [hparam, hq0] at htri
    linarith
  have hsN : s + E + C ≤ Lz := by
    have hprog := hzProg j N hjN le_rfl
    have hparam : dist (q s) (q Lz) = Lz - s := by
      rw [hq s hs Lz ⟨dist_nonneg, le_rfl⟩,
        abs_of_nonpos (sub_nonpos.mpr hs.2)]
      ring
    have htri := dist_triangle (z j) (q s) (q Lz)
    rw [hparam, hq1] at htri
    linarith
  obtain ⟨t, ht, hqt⟩ := hquad E Lz Ly hE dist_nonneg dist_nonneg
    q p hq hp
    (by rw [hq0, hp0]; exact hclose0)
    (by rw [hq1, hp1]; exact hcloseN)
    s hs0 hsN
  obtain ⟨i, hiN, hiy⟩ := hchordNear y N hyEdge hyProg
    Ly dist_nonneg p hp hp0 hp1 t ht
  refine ⟨i, hiN, ?_⟩
  have htri := dist_triangle4 (z j) (q s) (p t) (y i)
  rw [dist_comm (p t) (y i)] at htri
  linarith

end ElementaryMorse
end GGT
end GroupApproximation
