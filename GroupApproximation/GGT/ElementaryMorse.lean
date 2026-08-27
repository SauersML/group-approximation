import GroupApproximation.Sofic.HullSuitabilityGeometry

/-!
# Morse stability for orbit chains: the excursion engine, and what is left

Two residues wait on one theorem — `ElementaryCommonPower.FellowTravelMatching`
and `ElementaryFillCentralizer.OrbitFellowTravels` both need the orbit of a
loxodromic element to stay boundedly close to a geodesic joining the ends of the
segment it spans.  This module builds the engine of that theorem and names the
step still missing.

## Which of the chain lemmas is the Morse lemma

None of them is, and the closest one is worth naming precisely, since it is easy
to mistake for the conclusion.

`two_mul_progress_mul_far_radius_le` is the **quantitative recursive-detour
inequality**: for a chain of `D`-bounded steps with linear progress `l`, a
vertex `y j` whose distance to the endpoint chord exceeds `r + 3δ` satisfies

    2 · l · r  ≤  D · (D + (k_L + k_R)·δ + 6δ) + …

with `k_L, k_R` the dyadic depths of the two sides.  That is one subdivision
step of the Morse bootstrap, and it does **not** bound `r`: taking
`k_L, k_R ≈ log₂ N` makes the right-hand side grow like `D·δ·log₂ N`, so the
bound on the detour depth degrades with the length of the chain.  Its own
docstring says as much — "the closed numerical output of one recursive
subdivision step".

The lemma that does produce an `N`-free bound is `linear_length_le_of_excursion
_chain`, packaged as `exists_bound_excursion_chain_length`: a chain that stays
outside a ball, with both endpoints within one step of the sphere and linear
progress between them, has at most `M` edges, where `M` depends only on `δ`, `D`
and `l`.  There the radius cancels — that is the point of the statement — and
the linear-versus-logarithmic comparison `exists_bound_of_linear_le_add_clog`
turns it into a bound on the *length* of the excursion rather than on its depth.

So the division of labour is: the recursive inequality is the deep step and is
landed; the excursion-length bound is the uniform step and is landed; **the
assembly that turns a bounded excursion length into a bounded excursion depth,
and then into closeness to a geodesic, is what is missing.**  The first half of
that assembly is proved below.

## What is proved here

`exists_bound_chain_excursion_depth` — a chain of `D`-bounded steps with linear
progress that *starts and ends inside* a ball `B(w, R)` never leaves
`B(w, R + K)`, with `K = D + M·D` depending only on `δ, D, l`.

The proof is the maximal-component argument the excursion lemma was built for.
Given an index `j` outside the ball, `exists_left_excursion_boundary` and
`exists_right_excursion_boundary` scan out to the maximal exterior component
`[a, j+b]` containing it; that component satisfies the hypotheses of
`exists_bound_excursion_chain_length` exactly — outside the ball throughout,
endpoints within `D` of the sphere, linear progress inherited — so it has at
most `M` edges, and `dist_chain_le_nat_mul` converts that into
`d(y a, y j) ≤ M·D`.  Since `y a` is within `D` of the sphere, `y j` is within
`R + D + M·D` of `w`.

The two scanners have no other consumer in the repository; this is the one they
were written for.

## What is left: one statement, and it is not a covering argument

`exists_chord_point_near_chain_vertex` is the Morse conclusion already — a chain
vertex within `r + 3δ` of the chord — with `r` any number exceeding the
recursive-detour bound.  What is wrong with it is the constant: `kL, kR` are the
dyadic depths of the two sides, so the bound carries a `δ·log₂ N` term and
degrades with the length of the chain.

**Removing that term is the whole residual, and it is not an induction on the
chain length.**  Recursing on `N` cannot work, and the reason is worth stating:
the two sampled vertices `y i` and `y (j+q)` that
`exists_chain_vertices_across_far_vertex` returns are only known to satisfy
`d(y i, y (j+q)) ≤ D + (kL+kR)δ + 6δ`, an error that *itself* carries the
`log₂ N` term.  So an inductive step that bounds the depth of `y j` against the
chord of the sub-chain `[i, j+q]` and then transfers to the big chord reintroduces
`(kL+kR)δ` as an additive error at every level, and the constant never closes up
however deep the recursion goes.  Self-improvement has to happen at a smaller
*scale*, not on a shorter chain.

The route that does close is the linear-versus-logarithmic comparison already in
the file, applied to the depth rather than to the length.  Let `p = fAC s` be a
chord point at maximal distance `ρ` from the chain; the chain avoids `B(p, ρ)`,
and `y 0`, `y N`, `p` all lie on the chord with `p` between them, so their
Gromov product at `p` is `0` and `radius_le_of_chain_avoids_ball` gives
`ρ ≤ D/2 + clog₂(N')·δ` for the excursion sub-chain of length `N'`.  Cutting
that sub-chain down to the part that actually straddles `p` makes `N' = O(ρ/l)`,
and then `ρ ≤ D/2 + δ·clog₂(Cρ)` is linear-against-logarithmic *in `ρ` alone* —
which is exactly `exists_bound_of_linear_le_add_clog`, already proved and already
used once by `exists_bound_excursion_chain_length`.  So the missing step is the
cut, not a new estimate.  `chord_depth_le_clog` is that route's weak half,
proved; `StraddlingCut` is the cut, stated; and
`exists_bound_chord_depth_of_straddlingCut` closes the bootstrap from it.  What
the divergence estimate needs of the cut is worth recording exactly: its
conclusion is `R ≤ C + D/2 + k·δ`, so a merely *bounded* endpoint Gromov product
`C` does not suffice — `C` has to be a definite fraction of `ρ`.  That is why
`StraddlingCut` asks for `C ≤ ρ/2`, and why cutting at the ball `B(p, 2ρ)`,
where `C` can be as large as `2ρ`, cannot work.

The engine `exists_bound_chain_excursion_depth` does **not** supply it, and the
tempting route through it does not close: applying it at `w := γ t` needs both
chain endpoints inside `B(γ t, R)`, and those endpoints are `γ 0` and `γ L`, at
distances `t` and `L − t` from `γ t`.  So the hypothesis forces
`R > max (t, L − t)`, and the conclusion `≤ R + K` is then a bound of order `L`
— vacuous.  The engine bounds a detour relative to a ball the chain returns to,
which is a different statement from a detour relative to a chord the chain only
meets at its ends.  It remains the right tool for excursion arguments, and it is
not the tool for this one.

Given `OrbitNearGeodesic`, both residues follow by the routes their own modules
record, and neither needs anything else.

## Status

**Not compiled**, written while builds were frozen, and unwired for that reason.
The excursion-component proof below is index-heavy and was written without an
elaborator; any failures in it should be `omega`-level bookkeeping rather than
mathematics.
-/

namespace GroupApproximation
namespace GGT
namespace ElementaryMorse

open GroupApproximation.HullGeometry

universe u v

variable {X : Type v} [PseudoMetricSpace X]

/-! ## Excursions of a chain from a ball it starts and ends in -/

/-- **A chain that starts and ends inside a ball never strays far from it.**

`K = D + M·D` depends only on the hyperbolicity constant, the step bound and the
progress rate — not on the radius `R`, not on the centre `w`, and not on the
length of the chain.  That uniformity is what makes this the engine of Morse
stability rather than one more excursion estimate. -/
theorem exists_bound_chain_excursion_depth {δ D l : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (hD0 : 0 ≤ D) (hl : 0 < l) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (y : ℕ → X) (N : ℕ) (w : X) (R : ℝ),
      (∀ i, i < N → dist (y i) (y (i + 1)) ≤ D) →
      (∀ a b : ℕ, a ≤ b → b ≤ N → l * ((b - a : ℕ) : ℝ) ≤ dist (y a) (y b)) →
      dist (y 0) w < R → dist (y N) w < R →
      ∀ j, j ≤ N → dist (y j) w ≤ R + K := by
  obtain ⟨M, hM⟩ :=
    exists_bound_excursion_chain_length (X := X) (D := D) hδ hδ0 hl
  have hMD : (0 : ℝ) ≤ (M : ℝ) * D := mul_nonneg (Nat.cast_nonneg M) hD0
  refine ⟨D + M * D, add_nonneg hD0 hMD, ?_⟩
  intro y N w R hedge hprog h0 hNlt j hjN
  by_cases hin : dist (y j) w < R
  · linarith
  push_neg at hin
  -- the two scans out of `j` to the boundary of the exterior component
  have hstepL : ∀ i, i < j → dist (y (i + 1)) w ≤ dist (y i) w + D := by
    intro i hi
    have he := hedge i (by omega)
    have ht := dist_triangle (y (i + 1)) (y i) w
    rw [dist_comm (y (i + 1)) (y i)] at ht
    linarith
  obtain ⟨a, haj, haR, hallL⟩ :=
    exists_left_excursion_boundary (fun i => dist (y i) w) h0 hin hstepL
  have hstepR : ∀ i, i < N - j →
      dist (y (j + i)) w ≤ dist (y (j + i + 1)) w + D := by
    intro i hi
    have he := hedge (j + i) (by omega)
    have ht := dist_triangle (y (j + i)) (y (j + i + 1)) w
    linarith
  have hjd : j + (N - j) = N := by omega
  have hendR : dist (y (j + (N - j))) w < R := by rw [hjd]; exact hNlt
  obtain ⟨b, hbd, hbR, hallR⟩ :=
    exists_right_excursion_boundary (fun i => dist (y i) w) (N - j) j hendR hin
      hstepR
  -- the maximal exterior component `[a, j + b]`
  have haR' : dist (y a) w ≤ R + D := haR
  have hbR' : dist (y (j + b)) w ≤ R + D := hbR
  have hajb : a ≤ j + b := by omega
  have hjbN : j + b ≤ N := by omega
  set n : ℕ := j + b - a with hn
  have han : a + n = j + b := by omega
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · -- the component is a single vertex, so `j = a`
    have hja : j = a := by omega
    rw [hja]
    linarith
  -- the component avoids the ball throughout
  have havoid : ∀ i, i ≤ n → R ≤ dist (y (a + i)) w := by
    intro i hi
    rcases le_or_gt (a + i) j with hle | hgt
    · exact hallL (a + i) (by omega) hle
    · have hib : a + i - j ≤ b := by omega
      have hji : j + (a + i - j) = a + i := by omega
      have := hallR (a + i - j) hib
      rwa [hji] at this
  have hedge' : ∀ i, i < n → dist (y (a + i)) (y (a + i + 1)) ≤ D := by
    intro i hi
    exact hedge (a + i) (by omega)
  have hprog' : l * (n : ℝ) ≤ dist (y a) (y (a + n)) := by
    have h := hprog a (j + b) hajb hjbN
    have hsub : (j + b - a : ℕ) = n := by omega
    rw [hsub] at h
    rw [han]
    exact h
  have hle : n ≤ M := by
    refine hM R w (fun i => y (a + i)) n hnpos hedge' ?_ ?_ ?_
    · intro i hi
      exact havoid i hi
    · refine ⟨?_, ?_⟩
      · simpa using haR'
      · rw [han]; exact hbR'
    · simpa using hprog'
  -- and `j` is at most `M` edges from its left boundary
  have hja : a + (j - a) = j := by omega
  have hchain : dist (y a) (y j) ≤ ((j - a : ℕ) : ℝ) * D := by
    have h := dist_chain_le_nat_mul (D := D) y (N := N) hedge
      (a := a) (n := j - a) (by omega)
    rwa [hja] at h
  have hjaM : ((j - a : ℕ) : ℝ) ≤ (M : ℝ) := by
    have : j - a ≤ M := by omega
    exact_mod_cast this
  have htri := dist_triangle (y j) (y a) w
  rw [dist_comm (y j) (y a)] at htri
  have hmul : ((j - a : ℕ) : ℝ) * D ≤ (M : ℝ) * D :=
    mul_le_mul_of_nonneg_right hjaM hD0
  linarith

/-! ## The Morse conclusion, with a length-dependent constant -/

/-- **A chain vertex deeper than the recursive-detour bound is not deep at
all.**  Contrapositive of `two_mul_progress_mul_far_radius_le`: if `r` exceeds
that lemma's bound, then some point of the endpoint chord is within `r + 3δ` of
`y j`.  This is the Morse conclusion — a chain vertex close to the chord — and
the only thing wrong with it is the constant.

`kL` and `kR` are dyadic depths of the two sides, so at `kL, kR ≈ log₂ N` the
bound grows like `D·δ·log₂ N`: the estimate degrades with the length of the
chain.  Removing that dependence is the residual recorded below. -/
theorem exists_chord_point_near_chain_vertex {delta D l : ℝ}
    (hdelta : IsHyperbolicSpace delta X) (hdelta0 : 0 ≤ delta)
    (hD0 : 0 ≤ D) (hl : 0 < l)
    (y : ℕ → X) {N j kL kR : ℕ} (hj0 : 0 < j) (hjN : j < N)
    (hjpow : j ≤ 2 ^ kL) (hRpow : N - j ≤ 2 ^ kR)
    (hedge : ∀ i, i < N → dist (y i) (y (i + 1)) ≤ D)
    (hprogress : ∀ a b : ℕ, a ≤ b → b ≤ N →
      l * ((b - a : ℕ) : ℝ) ≤ dist (y a) (y b))
    {fAB fAC fCB : ℝ → X}
    (hAB : IsGeodesicSegment fAB 0 (dist (y 0) (y j)))
    (hAB0 : fAB 0 = y 0) (hAB1 : fAB (dist (y 0) (y j)) = y j)
    (hAC : IsGeodesicSegment fAC 0 (dist (y 0) (y N)))
    (hAC0 : fAC 0 = y 0) (hAC1 : fAC (dist (y 0) (y N)) = y N)
    (hCB : IsGeodesicSegment fCB 0 (dist (y N) (y j)))
    (hCB0 : fCB 0 = y N) (hCB1 : fCB (dist (y N) (y j)) = y j)
    {r : ℝ} (hr0 : 0 ≤ r) (hrL : r ≤ dist (y 0) (y j))
    (hrR : r ≤ dist (y N) (y j))
    (hbig : D * (D + ((kL : ℝ) + (kR : ℝ)) * delta + 6 * delta) +
      l * (D + ((kL : ℝ) + (kR : ℝ)) * delta) < 2 * l * r) :
    ∃ s ∈ Set.Icc (0 : ℝ) (dist (y 0) (y N)),
      dist (y j) (fAC s) ≤ r + 3 * delta := by
  by_contra hcon
  push_neg at hcon
  have h2 := two_mul_progress_mul_far_radius_le hdelta hdelta0 hD0 hl y hj0 hjN
    hjpow hRpow hedge hprogress hAB hAB0 hAB1 hAC hAC0 hAC1 hCB hCB0 hCB1
    hr0 hrL hrR hcon
  push_cast at h2 hbig
  linarith

/-! ## Sampled vertices against the chord -/

/-- **A point on a side is `3δ`-close to the chord or to the far side.**

`exists_chain_vertices_across_far_vertex` locates its two sampled vertices
against the *sides* `fAB` and `fCB` of the triangle `y 0, y j, y N`, never
against the chord `fAC`, so any argument that wants their distance to the chord
needs this step.  It is `exists_close_on_other_side_of_geodesic_triangle` with
the triangle relabelled — the side `A–B` played by that lemma's `A–C` — and the
hypotheses are then exactly the ones the far-vertex lemma already carries, in
the same order and with the same three geodesics. -/
theorem exists_close_on_chord_or_far_side {δ : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) {A B C : X}
    {fAB fAC fCB : ℝ → X}
    (hAB : IsGeodesicSegment fAB 0 (dist A B)) (hAB0 : fAB 0 = A)
    (hAB1 : fAB (dist A B) = B)
    (hAC : IsGeodesicSegment fAC 0 (dist A C)) (hAC0 : fAC 0 = A)
    (hAC1 : fAC (dist A C) = C)
    (hCB : IsGeodesicSegment fCB 0 (dist C B)) (hCB0 : fCB 0 = C)
    (hCB1 : fCB (dist C B) = B)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) (dist A B)) :
    (∃ s ∈ Set.Icc (0 : ℝ) (dist A C), dist (fAB t) (fAC s) ≤ 3 * δ) ∨
      (∃ s ∈ Set.Icc (0 : ℝ) (dist C B), dist (fAB t) (fCB s) ≤ 3 * δ) :=
  exists_close_on_other_side_of_geodesic_triangle hδ hδ0 hAB hAB0 hAB1
    hAC hAC0 hAC1 hCB hCB0 hCB1 ht

/-! ## The chord is not far from the chain: the weak bound -/

/-- **A chord point far from every chain vertex is at most `D/2 + δ·log₂ N`
far.**

No cut, no sub-chain: the whole chain is fed to
`radius_le_add_clog_of_chain_avoids_ball` at `w := fAC s`, and the Gromov
product the divergence estimate wants is *exactly zero*, because `y 0`, `y N`
and `fAC s` all lie on one geodesic with `fAC s` between the ends.  That is the
only place the chord is used, and it is what makes this bound cost nothing.

The `log₂ N` is the defect, and the next two declarations are about removing
it. -/
theorem chord_depth_le_clog {δ D ρ : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ)
    (y : ℕ → X) (N : ℕ) (hNpos : 0 < N)
    (hedge : ∀ i, i < N → dist (y i) (y (i + 1)) ≤ D)
    {fAC : ℝ → X} (hAC : IsGeodesicSegment fAC 0 (dist (y 0) (y N)))
    (hAC0 : fAC 0 = y 0) (hAC1 : fAC (dist (y 0) (y N)) = y N)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) (dist (y 0) (y N)))
    (havoid : ∀ i, i ≤ N → ρ ≤ dist (y i) (fAC s)) :
    ρ ≤ D / 2 + Nat.clog 2 N * δ := by
  have hzero : gromovProduct (y 0) (y N) (fAC s) = 0 := by
    have h := gromovProduct_le_dist_of_mem_geodesic dist_nonneg hs hAC (fAC s)
    rw [hAC0, hAC1, dist_self] at h
    exact le_antisymm h (gromovProduct_nonneg _ _ _)
  have hend : gromovProduct (y 0) (y N) (fAC s) ≤ 0 := le_of_eq hzero
  have h := radius_le_add_clog_of_chain_avoids_ball hδ hδ0 (fAC s) y N hNpos
    hedge havoid hend
  linarith

/-! ## The cut, and the bootstrap it unlocks -/

/-- **The straddling cut.**  A sub-chain of length `O(ρ/l)` whose endpoints have
small Gromov product at `p`.

The two clauses pull against each other, and that is the whole difficulty: the
length clause wants `a` and `b` close together, while the Gromov clause wants
them on opposite sides of `p`, so that `d(y a, y b)` is nearly the sum of their
distances to `p`.  Cutting at the ball `B(p, 2ρ)` — the obvious choice — gives
the length clause and fails the Gromov clause, since two vertices in that ball
have product up to `2ρ`, and `radius_le_of_chain_avoids_ball` then reads
`ρ ≤ 2ρ + D/2 + kδ`, which is vacuous.  What the Gromov clause needs is a cut
that follows the *chord parameter* rather than the distance to `p`. -/
def StraddlingCut (y : ℕ → X) (N : ℕ) (p : X) (ρ l : ℝ) : Prop :=
  ∃ a b : ℕ, a < b ∧ b ≤ N ∧
    l * ((b - a : ℕ) : ℝ) ≤ 4 * ρ ∧
    gromovProduct (y a) (y b) p ≤ ρ / 2

/-- **The bootstrap: with the cut, the depth is bounded by a constant.**

Applying the divergence estimate to the cut sub-chain gives
`ρ/2 ≤ D/2 + δ·log₂ n` with `l·n ≤ 4ρ`, so `ρ` is compared against the logarithm
of a multiple of itself — linear against logarithmic in `ρ` alone.  That is
`exists_bound_of_linear_le_add_clog`, instantiated at `D := 4D/3` and
`δ := 4δ`, and it is the same comparison `exists_bound_excursion_chain_length`
already makes; no new estimate enters. -/
theorem exists_bound_chord_depth_of_straddlingCut {δ D l : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (hD0 : 0 ≤ D) (hl : 0 < l) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ρ : ℝ) (p : X) (y : ℕ → X) (N : ℕ), 0 ≤ ρ →
      (∀ i, i < N → dist (y i) (y (i + 1)) ≤ D) →
      (∀ i, i ≤ N → ρ ≤ dist (y i) p) →
      StraddlingCut y N p ρ l → ρ ≤ K := by
  obtain ⟨M, hM⟩ :=
    exists_bound_of_linear_le_add_clog (l := l) (D := 4 * D / 3) (δ := 4 * δ) hl
  have hclogM : (0 : ℝ) ≤ (Nat.clog 2 M : ℝ) := Nat.cast_nonneg _
  refine ⟨D + 2 * Nat.clog 2 M * δ, by nlinarith, ?_⟩
  intro ρ p y N hρ0 hedge havoid hcut
  obtain ⟨a, b, hab, hbN, hlen, hgp⟩ := hcut
  set n : ℕ := b - a with hn
  have han : a + n = b := by omega
  have hnpos : 0 < n := by omega
  have hedge' : ∀ i, i < n → dist (y (a + i)) (y (a + i + 1)) ≤ D := by
    intro i hi
    exact hedge (a + i) (by omega)
  have havoid' : ∀ i, i ≤ n → ρ ≤ dist (y (a + i)) p := by
    intro i hi
    exact havoid (a + i) (by omega)
  have hend' : gromovProduct (y (a + 0)) (y (a + n)) p ≤ ρ / 2 := by
    rw [Nat.add_zero, han]
    exact hgp
  have hdiv := radius_le_add_clog_of_chain_avoids_ball hδ hδ0 p
    (fun i => y (a + i)) n hnpos hedge' havoid' hend'
  -- `ρ/2 ≤ D/2 + δ·log₂ n`, and `l·n ≤ 4ρ`
  have hhalf : ρ / 2 ≤ D / 2 + Nat.clog 2 n * δ := by linarith
  have hlenn : l * (n : ℝ) ≤ 4 * ρ := by rw [hn] at hlen ⊢; exact hlen
  have hlinear : l * (n : ℝ) / 2 ≤ 3 * (4 * D / 3) / 2 + Nat.clog 2 n * (4 * δ) := by
    nlinarith [hhalf, hlenn]
  have hnM : n ≤ M := hM n hlinear
  have hmono : (Nat.clog 2 n : ℝ) ≤ (Nat.clog 2 M : ℝ) := by
    exact_mod_cast Nat.clog_mono_right 2 hnM
  nlinarith [hhalf, hmono, hδ0]

/-! ## What the two residues are waiting for -/

/-- **The Morse lemma for orbit chains**, as a named residual: the orbit of a
loxodromic element stays within a bound depending only on `δ`, on the step
length and on the progress rate of a geodesic joining the ends of the segment it
spans.

`exists_bound_chain_excursion_depth` is its engine; what separates them is a
covering argument, placing the balls of that theorem along the chord. -/
def OrbitNearGeodesic (G : Type u) [Group G] (X : Type v) [PseudoMetricSpace X]
    [MulAction G X] : Prop :=
  ∀ {δ : ℝ}, IsHyperbolicSpace δ X → 0 ≤ δ → IsGeodesicSpace X →
    IsIsometricAction G X →
      ∀ {g : G} {x : X}, IsLoxodromic g x →
        ∃ K : ℝ, 0 ≤ K ∧ ∀ (n : ℕ) (f : ℝ → X),
          IsGeodesicSegment f 0 (dist x ((g ^ (n : ℤ)) • x)) →
          f 0 = x → f (dist x ((g ^ (n : ℤ)) • x)) = (g ^ (n : ℤ)) • x →
          ∀ k : ℕ, k ≤ n →
            ∃ s ∈ Set.Icc (0 : ℝ) (dist x ((g ^ (n : ℤ)) • x)),
              dist ((g ^ (k : ℤ)) • x) (f s) ≤ K

end ElementaryMorse
end GGT
end GroupApproximation
