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

**Removing that term is the whole residual, and no covering argument enters.**
The classical route is the bootstrap the source lemma is shaped for: the two
sampled vertices `y i` and `y (j+q)` that
`exists_chain_vertices_across_far_vertex` returns are at chain-distance at most
`(D + (kL+kR)δ + 6δ)/l`, so the sub-chain carrying the detour has length
logarithmic in `N`; applying the same estimate to *that* sub-chain replaces
`log₂ N` by `log₂ log₂ N`, and iterating stabilises, because `log₂` is
eventually contracting.  That induction is the missing step.

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
