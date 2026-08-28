import GroupApproximation.GGT.ElementaryMorse

/-!
# The Morse lemma for chains: chord near chain, chain near chord

`ElementaryMorse` records a proof plan for the stability of quasi-geodesic
chains and names what was missing: a route to a *small Gromov product* for the
divergence estimate `radius_le_add_clog_of_chain_avoids_ball`, since the pair of
chain vertices pulled back from the chord has endpoint product `2ρ` at the chord
point and the estimate needs it below `ρ`.  The plan proposed a concatenated
path through two connecting geodesics.  That detour is unnecessary.

## The Gromov product is at most `2δ`, by the four-point condition twice

Let `p = f s₀` be a chord point, `p' = f s₁` and `p'' = f s₂` chord points on
either side of it, and `u`, `v` chain vertices near `p'` and `p''`.  Since the
three chord points lie on one geodesic with `p` between the other two,
`(p' | p'')_p = 0`.  Two applications of the four-point inequality at `p`:

    min ((p' | v)_p, (v | p'')_p) − δ ≤ (p' | p'')_p = 0,
    min ((p' | u)_p, (u | v)_p) − δ ≤ (p' | v)_p.

If `(v | p'')_p > δ` the first gives `(p' | v)_p ≤ δ`; if moreover
`(p' | u)_p > 2δ` the second gives `(u | v)_p ≤ 2δ`.  The lower bounds on
`(p' | u)_p` and `(v | p'')_p` hold as soon as `p'` and `p''` are taken at chord
distance `3r + 5δ + 1` from `p`, where `r` is the distance from `p` to the chain
and every chord point is within `3r` of the chain.  At the ends of the chord
the anchor is the endpoint itself, which is a chain vertex, and the lower bound
is the distance from that vertex to `p`, at least `r`.

So the divergence estimate applies to the sub-chain between `u` and `v` with
`C = 2δ`, and its length is linear in `r` because the chain makes linear
progress; `exists_bound_of_linear_le_add_clog` turns that into a bound on `r`
that depends only on the constants.  This is
`exists_bound_radius_of_chord_point`.

## The two halves of the Morse lemma

* `exists_bound_chord_near_chain` — every chord point is within `K₁` of some
  chain vertex.  The infimum of the radii within which the chain is dense along
  the chord is either at most `2K₀`, in which case density at `2K₀ + 1` is
  given, or larger, in which case some chord point is at distance at least half
  of it from the chain while the chain is dense at three halves of it, which
  the radius bound forbids.
* `exists_bound_chain_near_chord` — every chain vertex is within `K₂` of some
  chord point.  Given a vertex `y j`, the supremum `τ` of the chord parameters
  whose `K₁`-partner has index below `j` is approached from below by a point
  with a partner `i₁ < j` and from above (or is the end of the chord) by a point
  with a partner `i₂ ≥ j`; the two chord points are at most `2` apart, so the
  partners are `2K₁ + 2` apart, linear progress bounds `i₂ − i₁` and so
  `j − i₁`, and the step bound places `y j` within `D · (j − i₁)` of `y i₁`.

## Conventions

Progress is stated with additive slack, `l · (j − i) − B ≤ d(y i, y j)`, which
is exactly what `IsLoxodromic` provides for an orbit chain; no subsampling is
needed downstream.  The chord is a geodesic `f` on `[0, L]` with `f 0 = y 0` and
`f L = y N`; the value of `L` is never used, only that the parameter interval
carries the geodesic.

## Status

**Not compiled**, written while builds were frozen.
-/

namespace GroupApproximation
namespace GGT
namespace ElementaryMorse

open GroupApproximation.HullGeometry

universe v

variable {X : Type v} [PseudoMetricSpace X]

/-! ## The four-point condition, twice -/

/-- **A pair straddling a chord point has small Gromov product there.**  With
`p'`, `p''` on either side of `p` (product `0`) and `u`, `v` well beyond them
in the sense of the Gromov product, `(u | v)_p ≤ 2δ`. -/
theorem gromovProduct_le_two_mul_of_between {δ : ℝ} (hδ : IsHyperbolicSpace δ X)
    {p p' p'' u v : X}
    (hend : gromovProduct p' p'' p ≤ 0)
    (hu : 2 * δ < gromovProduct p' u p)
    (hv : δ < gromovProduct v p'' p) :
    gromovProduct u v p ≤ 2 * δ := by
  have h1 := hδ p p' v p''
  have h1' : gromovProduct p' v p ≤ δ := by
    have hmin : min (gromovProduct p' v p) (gromovProduct v p'' p) ≤ δ := by
      linarith
    rcases min_le_iff.mp hmin with h | h
    · exact h
    · exact absurd h (not_le.mpr hv)
  have h2 := hδ p p' u v
  have hmin : min (gromovProduct p' u p) (gromovProduct u v p) ≤ 2 * δ := by
    linarith
  rcases min_le_iff.mp hmin with h | h
  · exact absurd h (not_le.mpr hu)
  · exact h

/-! ## The divergence estimate on a sub-chain, in either orientation -/

/-- The divergence estimate on the sub-chain from `a` to `b`, `a < b`. -/
theorem radius_le_of_subchain_forward {δ D R C : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (p : X) (y : ℕ → X) {N a b : ℕ}
    (hab : a < b) (hbN : b ≤ N)
    (hedge : ∀ i, i < N → dist (y i) (y (i + 1)) ≤ D)
    (havoid : ∀ i, i ≤ N → R ≤ dist (y i) p)
    (hend : gromovProduct (y a) (y b) p ≤ C) :
    R ≤ C + D / 2 + Nat.clog 2 (b - a) * δ := by
  have hedge' : ∀ i, i < b - a → dist (y (a + i)) (y (a + i + 1)) ≤ D := by
    intro i hi
    exact hedge (a + i) (by omega)
  have havoid' : ∀ i, i ≤ b - a → R ≤ dist (y (a + i)) p := by
    intro i hi
    exact havoid (a + i) (by omega)
  have hend' : gromovProduct (y (a + 0)) (y (a + (b - a))) p ≤ C := by
    rw [Nat.add_zero, Nat.add_sub_of_le hab.le]
    exact hend
  exact radius_le_add_clog_of_chain_avoids_ball hδ hδ0 p (fun i => y (a + i))
    (b - a) (by omega) hedge' havoid' hend'

/-- The divergence estimate on the sub-chain from `a` down to `b`, `b < a`. -/
theorem radius_le_of_subchain_backward {δ D R C : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (p : X) (y : ℕ → X) {N a b : ℕ}
    (hab : b < a) (haN : a ≤ N)
    (hedge : ∀ i, i < N → dist (y i) (y (i + 1)) ≤ D)
    (havoid : ∀ i, i ≤ N → R ≤ dist (y i) p)
    (hend : gromovProduct (y a) (y b) p ≤ C) :
    R ≤ C + D / 2 + Nat.clog 2 (a - b) * δ := by
  have hedge' : ∀ i, i < a - b → dist (y (a - i)) (y (a - (i + 1))) ≤ D := by
    intro i hi
    have h1 : a - i = a - (i + 1) + 1 := by omega
    rw [dist_comm, h1]
    exact hedge (a - (i + 1)) (by omega)
  have havoid' : ∀ i, i ≤ a - b → R ≤ dist (y (a - i)) p := by
    intro i hi
    exact havoid (a - i) (by omega)
  have hend' : gromovProduct (y (a - 0)) (y (a - (a - b))) p ≤ C := by
    rw [Nat.sub_zero, Nat.sub_sub_self hab.le]
    exact hend
  exact radius_le_add_clog_of_chain_avoids_ball hδ hδ0 p (fun i => y (a - i))
    (a - b) (by omega) hedge' havoid' hend'

/-- **The sub-chain estimate.**  Two distinct vertices whose Gromov product at
`p` is at most `C` bound the avoidance radius of `p` by `C + D/2 + δ·log₂ n`,
where `n` is the number of steps between them, and linear progress bounds
`n` by their distance. -/
theorem exists_subchain_estimate {δ D R C l B : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (p : X) (y : ℕ → X) {N a b : ℕ}
    (hab : a ≠ b) (haN : a ≤ N) (hbN : b ≤ N)
    (hedge : ∀ i, i < N → dist (y i) (y (i + 1)) ≤ D)
    (hprog : ∀ i j, i ≤ j → j ≤ N →
      l * ((j - i : ℕ) : ℝ) - B ≤ dist (y i) (y j))
    (havoid : ∀ i, i ≤ N → R ≤ dist (y i) p)
    (hend : gromovProduct (y a) (y b) p ≤ C) :
    ∃ n : ℕ, 0 < n ∧ R ≤ C + D / 2 + Nat.clog 2 n * δ ∧
      l * (n : ℝ) - B ≤ dist (y a) (y b) := by
  rcases Nat.lt_or_gt_of_ne hab with h | h
  · exact ⟨b - a, by omega,
      radius_le_of_subchain_forward hδ hδ0 p y h hbN hedge havoid hend,
      hprog a b h.le hbN⟩
  · refine ⟨a - b, by omega,
      radius_le_of_subchain_backward hδ hδ0 p y h haN hedge havoid hend, ?_⟩
    rw [dist_comm]
    exact hprog b a h.le haN

/-! ## The two anchors -/

/-- **The left anchor.**  A chain vertex within `3r` of a chord point at most
`3r + 5δ + 1` before `s₀`, with Gromov product above `2δ` at `f s₀`; at the
start of the chord the anchor is `y 0` itself. -/
theorem exists_left_anchor {δ r L : ℝ} (hδ0 : 0 ≤ δ) (hr : 2 * δ < r)
    (y : ℕ → X) (N : ℕ) {f : ℝ → X} (hf : IsGeodesicSegment f 0 L)
    (hf0 : f 0 = y 0) {s₀ : ℝ} (hs₀ : s₀ ∈ Set.Icc (0 : ℝ) L)
    (havoid : ∀ i, i ≤ N → r ≤ dist (y i) (f s₀))
    (hdense : ∀ t ∈ Set.Icc (0 : ℝ) L, ∃ i, i ≤ N ∧ dist (y i) (f t) ≤ 3 * r) :
    ∃ (a : ℕ) (s₁ : ℝ), a ≤ N ∧ 0 ≤ s₁ ∧ s₁ ≤ s₀ ∧
      s₀ - s₁ ≤ 3 * r + 5 * δ + 1 ∧
      dist (y a) (f s₁) ≤ 3 * r ∧ 2 * δ < gromovProduct (f s₁) (y a) (f s₀) := by
  have hr0 : 0 ≤ r := by linarith
  by_cases hw : 3 * r + 5 * δ + 1 ≤ s₀
  · have hmem : s₀ - (3 * r + 5 * δ + 1) ∈ Set.Icc (0 : ℝ) L :=
      ⟨by linarith, by linarith [hs₀.2]⟩
    obtain ⟨a, haN, ha⟩ := hdense _ hmem
    refine ⟨a, s₀ - (3 * r + 5 * δ + 1), haN, hmem.1, by linarith, by linarith,
      ha, ?_⟩
    have hd : dist (f (s₀ - (3 * r + 5 * δ + 1))) (f s₀) = 3 * r + 5 * δ + 1 := by
      rw [hf.dist_eq hmem hs₀,
        show s₀ - (3 * r + 5 * δ + 1) - s₀ = -(3 * r + 5 * δ + 1) by ring,
        abs_neg, abs_of_nonneg (by linarith)]
    have ha' : dist (f (s₀ - (3 * r + 5 * δ + 1))) (y a) ≤ 3 * r := by
      rw [dist_comm]
      exact ha
    have hap := havoid a haN
    unfold gromovProduct
    rw [hd]
    linarith
  · push Not at hw
    refine ⟨0, 0, Nat.zero_le N, le_refl 0, hs₀.1, by linarith, ?_, ?_⟩
    · rw [hf0, dist_self]
      linarith
    · rw [hf0]
      unfold gromovProduct
      rw [dist_self]
      have := havoid 0 (Nat.zero_le N)
      linarith

/-- **The right anchor**, symmetric to the left one; at the end of the chord the
anchor is `y N` itself. -/
theorem exists_right_anchor {δ r L : ℝ} (hδ0 : 0 ≤ δ) (hr : 2 * δ < r)
    (y : ℕ → X) (N : ℕ) {f : ℝ → X} (hf : IsGeodesicSegment f 0 L)
    (hfL : f L = y N) {s₀ : ℝ} (hs₀ : s₀ ∈ Set.Icc (0 : ℝ) L)
    (havoid : ∀ i, i ≤ N → r ≤ dist (y i) (f s₀))
    (hdense : ∀ t ∈ Set.Icc (0 : ℝ) L, ∃ i, i ≤ N ∧ dist (y i) (f t) ≤ 3 * r) :
    ∃ (b : ℕ) (s₂ : ℝ), b ≤ N ∧ s₀ ≤ s₂ ∧ s₂ ≤ L ∧
      s₂ - s₀ ≤ 3 * r + 5 * δ + 1 ∧
      dist (y b) (f s₂) ≤ 3 * r ∧ 2 * δ < gromovProduct (f s₂) (y b) (f s₀) := by
  have hr0 : 0 ≤ r := by linarith
  by_cases hw : s₀ + (3 * r + 5 * δ + 1) ≤ L
  · have hmem : s₀ + (3 * r + 5 * δ + 1) ∈ Set.Icc (0 : ℝ) L :=
      ⟨by linarith [hs₀.1], hw⟩
    obtain ⟨b, hbN, hb⟩ := hdense _ hmem
    refine ⟨b, s₀ + (3 * r + 5 * δ + 1), hbN, by linarith, hw, by linarith,
      hb, ?_⟩
    have hd : dist (f (s₀ + (3 * r + 5 * δ + 1))) (f s₀) = 3 * r + 5 * δ + 1 := by
      rw [hf.dist_eq hmem hs₀,
        show s₀ + (3 * r + 5 * δ + 1) - s₀ = 3 * r + 5 * δ + 1 by ring,
        abs_of_nonneg (by linarith)]
    have hb' : dist (f (s₀ + (3 * r + 5 * δ + 1))) (y b) ≤ 3 * r := by
      rw [dist_comm]
      exact hb
    have hbp := havoid b hbN
    unfold gromovProduct
    rw [hd]
    linarith
  · push Not at hw
    refine ⟨N, L, le_refl N, hs₀.2, le_refl L, by linarith, ?_, ?_⟩
    · rw [hfL, dist_self]
      linarith
    · rw [hfL]
      unfold gromovProduct
      rw [dist_self]
      have := havoid N (le_refl N)
      linarith

/-! ## The radius bound -/

/-- **A chord point at distance `r` from the chain, with the chain `3r`-dense
along the chord, has `r` bounded by the constants alone.** -/
theorem exists_bound_radius_of_chord_point {δ D l B : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (hD0 : 0 ≤ D) (hl : 0 < l)
    (hB0 : 0 ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (y : ℕ → X) (N : ℕ),
      (∀ i, i < N → dist (y i) (y (i + 1)) ≤ D) →
      (∀ i j, i ≤ j → j ≤ N → l * ((j - i : ℕ) : ℝ) - B ≤ dist (y i) (y j)) →
      ∀ (L : ℝ) (f : ℝ → X), IsGeodesicSegment f 0 L → f 0 = y 0 → f L = y N →
        ∀ s₀ ∈ Set.Icc (0 : ℝ) L, ∀ r : ℝ, 0 ≤ r →
          (∀ i, i ≤ N → r ≤ dist (y i) (f s₀)) →
          (∀ t ∈ Set.Icc (0 : ℝ) L, ∃ i, i ≤ N ∧ dist (y i) (f t) ≤ 3 * r) →
          r ≤ K := by
  obtain ⟨M, hM⟩ := exists_bound_of_linear_le_add_clog
    (l := l) (D := (34 * δ + 6 * D + 2 * B + 2) / 3) (δ := 6 * δ) hl
  have hclogM : (0 : ℝ) ≤ (Nat.clog 2 M : ℝ) := Nat.cast_nonneg _
  have hKnn : 0 ≤ 2 * δ + D / 2 + Nat.clog 2 M * δ := by
    have := mul_nonneg hclogM hδ0
    linarith
  refine ⟨2 * δ + D / 2 + Nat.clog 2 M * δ, hKnn, ?_⟩
  intro y N hedge hprog L f hf hf0 hfL s₀ hs₀ r hr0 havoid hdense
  by_cases hr2 : r ≤ 2 * δ
  · have := mul_nonneg hclogM hδ0
    linarith
  push Not at hr2
  obtain ⟨a, s₁, haN, hs₁0, hs₁s₀, hs₁w, ha, hga⟩ :=
    exists_left_anchor hδ0 hr2 y N hf hf0 hs₀ havoid hdense
  obtain ⟨b, s₂, hbN, hs₀s₂, hs₂L, hs₂w, hb, hgb⟩ :=
    exists_right_anchor hδ0 hr2 y N hf hfL hs₀ havoid hdense
  have hmem₁ : s₁ ∈ Set.Icc (0 : ℝ) L := ⟨hs₁0, by linarith [hs₀.2]⟩
  have hmem₂ : s₂ ∈ Set.Icc (0 : ℝ) L := ⟨by linarith [hs₀.1], hs₂L⟩
  have hrestr : IsGeodesicSegment f s₁ s₂ := by
    intro s hs t ht
    exact hf s ⟨by linarith [hs.1], by linarith [hs.2]⟩
      t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hend : gromovProduct (f s₁) (f s₂) (f s₀) ≤ 0 := by
    have h := gromovProduct_le_dist_of_mem_geodesic (by linarith : s₁ ≤ s₂)
      (⟨hs₁s₀, hs₀s₂⟩ : s₀ ∈ Set.Icc s₁ s₂) hrestr (f s₀)
    rwa [dist_self] at h
  have hgb' : δ < gromovProduct (y b) (f s₂) (f s₀) := by
    rw [gromovProduct_comm]
    linarith
  have hab_gp : gromovProduct (y a) (y b) (f s₀) ≤ 2 * δ :=
    gromovProduct_le_two_mul_of_between hδ hend hga hgb'
  have hab : a ≠ b := by
    intro heq
    subst heq
    rw [gromovProduct_self] at hab_gp
    have := havoid _ haN
    linarith
  obtain ⟨n, -, hRn, hln⟩ :=
    exists_subchain_estimate hδ hδ0 (f s₀) y hab haN hbN hedge hprog havoid hab_gp
  have hs₁s₂ : dist (f s₁) (f s₂) ≤ 6 * r + 10 * δ + 2 := by
    rw [hf.dist_eq hmem₁ hmem₂, abs_of_nonpos (by linarith : s₁ - s₂ ≤ 0)]
    linarith
  have hdab : dist (y a) (y b) ≤ 12 * r + 10 * δ + 2 := by
    have h1 := dist_triangle (y a) (f s₁) (y b)
    have h2 := dist_triangle (f s₁) (f s₂) (y b)
    have hb' : dist (f s₂) (y b) ≤ 3 * r := by
      rw [dist_comm]
      exact hb
    linarith
  have hlin : l * (n : ℝ) / 2 ≤ 3 * ((34 * δ + 6 * D + 2 * B + 2) / 3) / 2 +
      Nat.clog 2 n * (6 * δ) := by
    have h3 : (Nat.clog 2 n : ℝ) * (6 * δ) = 6 * ((Nat.clog 2 n : ℝ) * δ) := by
      ring
    rw [h3]
    have h1 : l * (n : ℝ) - B ≤ 12 * r + 10 * δ + 2 := hln.trans hdab
    linarith
  have hnM : n ≤ M := hM n hlin
  have hclog : (Nat.clog 2 n : ℝ) ≤ Nat.clog 2 M := by
    exact_mod_cast Nat.clog_mono_right 2 hnM
  have := mul_le_mul_of_nonneg_right hclog hδ0
  linarith

/-! ## Chord near chain -/

/-- **Every chord point is within `K₁` of a chain vertex**, with `K₁` depending
only on `δ`, the step bound and the progress constants. -/
theorem exists_bound_chord_near_chain {δ D l B : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (hD0 : 0 ≤ D) (hl : 0 < l)
    (hB0 : 0 ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (y : ℕ → X) (N : ℕ),
      (∀ i, i < N → dist (y i) (y (i + 1)) ≤ D) →
      (∀ i j, i ≤ j → j ≤ N → l * ((j - i : ℕ) : ℝ) - B ≤ dist (y i) (y j)) →
      ∀ (L : ℝ), 0 ≤ L → ∀ (f : ℝ → X), IsGeodesicSegment f 0 L →
        f 0 = y 0 → f L = y N →
        ∀ t ∈ Set.Icc (0 : ℝ) L, ∃ i, i ≤ N ∧ dist (y i) (f t) ≤ K := by
  obtain ⟨K₀, hK₀, hK⟩ := exists_bound_radius_of_chord_point hδ hδ0 hD0 hl hB0
  refine ⟨2 * K₀ + 1, by linarith, ?_⟩
  intro y N hedge hprog L hL f hf hf0 hfL
  obtain ⟨T, hmemT⟩ : ∃ T : Set ℝ, ∀ r, r ∈ T ↔
      (0 ≤ r ∧ ∀ t ∈ Set.Icc (0 : ℝ) L, ∃ i, i ≤ N ∧ dist (y i) (f t) ≤ r) :=
    ⟨{r : ℝ | 0 ≤ r ∧ ∀ t ∈ Set.Icc (0 : ℝ) L, ∃ i, i ≤ N ∧ dist (y i) (f t) ≤ r},
      fun r => Iff.rfl⟩
  have hLT : L ∈ T := by
    refine (hmemT L).mpr ⟨hL, fun t ht => ⟨0, Nat.zero_le N, ?_⟩⟩
    rw [← hf0, hf.dist_eq ⟨le_refl 0, hL⟩ ht, zero_sub, abs_neg,
      abs_of_nonneg ht.1]
    exact ht.2
  have hne : T.Nonempty := ⟨L, hLT⟩
  have hbdd : BddBelow T := ⟨0, fun r hr => ((hmemT r).mp hr).1⟩
  by_cases hcase : sInf T ≤ 2 * K₀
  · obtain ⟨r, hrT, hr⟩ :=
      exists_lt_of_csInf_lt hne (by linarith : sInf T < sInf T + 1)
    intro t ht
    obtain ⟨i, hiN, hi⟩ := ((hmemT r).mp hrT).2 t ht
    exact ⟨i, hiN, by linarith⟩
  · push Not at hcase
    exfalso
    have hpoint : ∃ t₀ ∈ Set.Icc (0 : ℝ) L,
        ∀ i, i ≤ N → sInf T / 2 ≤ dist (y i) (f t₀) := by
      by_contra hcon
      push Not at hcon
      have hmem : sInf T / 2 ∈ T := by
        refine (hmemT _).mpr ⟨by linarith, fun t ht => ?_⟩
        obtain ⟨i, hiN, hi⟩ := hcon t ht
        exact ⟨i, hiN, hi.le⟩
      have := csInf_le hbdd hmem
      linarith
    obtain ⟨t₀, ht₀, havoid⟩ := hpoint
    obtain ⟨r, hrT, hr⟩ := exists_lt_of_csInf_lt hne
      (by linarith : sInf T < 3 * (sInf T / 2))
    have hdense : ∀ t ∈ Set.Icc (0 : ℝ) L,
        ∃ i, i ≤ N ∧ dist (y i) (f t) ≤ 3 * (sInf T / 2) := by
      intro t ht
      obtain ⟨i, hiN, hi⟩ := ((hmemT r).mp hrT).2 t ht
      exact ⟨i, hiN, by linarith⟩
    have := hK y N hedge hprog L f hf hf0 hfL t₀ ht₀ (sInf T / 2) (by linarith)
      havoid hdense
    linarith

/-! ## Chain near chord -/

/-- **Every chain vertex is within `K₂` of a chord point**, with `K₂` depending
only on `δ`, the step bound and the progress constants. -/
theorem exists_bound_chain_near_chord {δ D l B : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (hD0 : 0 ≤ D) (hl : 0 < l)
    (hB0 : 0 ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (y : ℕ → X) (N : ℕ),
      (∀ i, i < N → dist (y i) (y (i + 1)) ≤ D) →
      (∀ i j, i ≤ j → j ≤ N → l * ((j - i : ℕ) : ℝ) - B ≤ dist (y i) (y j)) →
      ∀ (L : ℝ), 0 ≤ L → ∀ (f : ℝ → X), IsGeodesicSegment f 0 L →
        f 0 = y 0 → f L = y N →
        ∀ j, j ≤ N → ∃ t ∈ Set.Icc (0 : ℝ) L, dist (y j) (f t) ≤ K := by
  obtain ⟨K₁, hK₁0, hK₁⟩ := exists_bound_chord_near_chain hδ hδ0 hD0 hl hB0
  have hK2 : 0 ≤ K₁ + D * ((2 * K₁ + 2 + B) / l) :=
    add_nonneg hK₁0 (mul_nonneg hD0 (div_nonneg (by linarith) hl.le))
  refine ⟨K₁ + D * ((2 * K₁ + 2 + B) / l), hK2, ?_⟩
  intro y N hedge hprog L hL f hf hf0 hfL j hjN
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · subst hj0
    refine ⟨0, ⟨le_refl 0, hL⟩, ?_⟩
    rw [hf0, dist_self]
    exact hK2
  obtain ⟨S, hmemS⟩ : ∃ S : Set ℝ, ∀ t, t ∈ S ↔
      (t ∈ Set.Icc (0 : ℝ) L ∧ ∃ i, i < j ∧ dist (y i) (f t) ≤ K₁) :=
    ⟨{t : ℝ | t ∈ Set.Icc (0 : ℝ) L ∧ ∃ i, i < j ∧ dist (y i) (f t) ≤ K₁},
      fun t => Iff.rfl⟩
  have h0S : (0 : ℝ) ∈ S := by
    refine (hmemS 0).mpr ⟨⟨le_refl 0, hL⟩, 0, hjpos, ?_⟩
    rw [hf0, dist_self]
    exact hK₁0
  have hne : S.Nonempty := ⟨0, h0S⟩
  have hbdd : BddAbove S := ⟨L, fun t ht => ((hmemS t).mp ht).1.2⟩
  have hτL : sSup S ≤ L := csSup_le hne (fun t ht => ((hmemS t).mp ht).1.2)
  obtain ⟨t₁, ht₁S, ht₁⟩ :=
    exists_lt_of_lt_csSup hne (by linarith : sSup S - 1 < sSup S)
  obtain ⟨ht₁I, i₁, hi₁j, hi₁⟩ := (hmemS t₁).mp ht₁S
  have ht₁le : t₁ ≤ sSup S := le_csSup hbdd ht₁S
  have hright : ∃ t₂ ∈ Set.Icc (0 : ℝ) L, t₂ ≤ sSup S + 1 ∧ sSup S ≤ t₂ ∧
      ∃ i₂, i₂ ≤ N ∧ j ≤ i₂ ∧ dist (y i₂) (f t₂) ≤ K₁ := by
    by_cases hτ : sSup S < L
    · have hτ0 : 0 ≤ sSup S := le_csSup hbdd h0S
      have ht₂I : min (sSup S + 1) L ∈ Set.Icc (0 : ℝ) L :=
        ⟨le_min (by linarith) hL, min_le_right _ _⟩
      have hτt₂ : sSup S < min (sSup S + 1) L := lt_min (by linarith) hτ
      obtain ⟨i₂, hi₂N, hi₂⟩ := hK₁ y N hedge hprog L hL f hf hf0 hfL _ ht₂I
      refine ⟨min (sSup S + 1) L, ht₂I, min_le_left _ _, hτt₂.le, i₂, hi₂N, ?_,
        hi₂⟩
      by_contra hlt
      push Not at hlt
      have hmem : min (sSup S + 1) L ∈ S := (hmemS _).mpr ⟨ht₂I, i₂, hlt, hi₂⟩
      exact absurd (le_csSup hbdd hmem) (not_le.mpr hτt₂)
    · push Not at hτ
      refine ⟨L, ⟨hL, le_refl L⟩, by linarith, hτL, N, le_refl N, hjN, ?_⟩
      rw [hfL, dist_self]
      exact hK₁0
  obtain ⟨t₂, ht₂I, ht₂le, hτt₂, i₂, hi₂N, hji₂, hi₂⟩ := hright
  have hd12 : dist (y i₁) (y i₂) ≤ 2 * K₁ + 2 := by
    have h1 := dist_triangle (y i₁) (f t₁) (y i₂)
    have h2 := dist_triangle (f t₁) (f t₂) (y i₂)
    have hf12 : dist (f t₁) (f t₂) ≤ 2 := by
      rw [hf.dist_eq ht₁I ht₂I, abs_le]
      constructor <;> linarith
    have hi₂' : dist (f t₂) (y i₂) ≤ K₁ := by
      rw [dist_comm]
      exact hi₂
    linarith
  have hprog12 := hprog i₁ i₂ (by omega) hi₂N
  have hcast : ((j - i₁ : ℕ) : ℝ) ≤ ((i₂ - i₁ : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_le_sub_right hji₂ i₁
  have hidx : ((j - i₁ : ℕ) : ℝ) ≤ (2 * K₁ + 2 + B) / l := by
    rw [le_div_iff₀ hl, mul_comm _ l]
    have := mul_le_mul_of_nonneg_left hcast hl.le
    linarith
  have hdj : dist (y i₁) (y j) ≤ ((j - i₁ : ℕ) : ℝ) * D := by
    have h := dist_chain_le_nat_mul (a := i₁) (n := j - i₁) y hedge (by omega)
    rwa [Nat.add_sub_of_le hi₁j.le] at h
  refine ⟨t₁, ht₁I, ?_⟩
  have h1 := dist_triangle (y j) (y i₁) (f t₁)
  have hji : dist (y j) (y i₁) ≤ D * ((2 * K₁ + 2 + B) / l) := by
    rw [dist_comm]
    calc dist (y i₁) (y j) ≤ ((j - i₁ : ℕ) : ℝ) * D := hdj
      _ ≤ (2 * K₁ + 2 + B) / l * D := mul_le_mul_of_nonneg_right hidx hD0
      _ = D * ((2 * K₁ + 2 + B) / l) := by ring
  linarith

end ElementaryMorse
end GGT
end GroupApproximation
