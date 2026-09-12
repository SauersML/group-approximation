import GroupApproximation.GGT.OlshanskiiChord

/-!
# The balanced bisection of a geodesic polygon

The second module of the Ol'shanskii reconstruction: every closed geodesic
`n`-gon (`n ≥ 8`) admits a short cut — two points on two sides, at distance
at most `6δ(c+1) + 1` for `n ≤ 2^c` — whose side indices are
quarter-separated: `n ≤ 4(b - a) ≤ 3n`.  Cutting along it therefore splits
the polygon into two pieces whose side counts both lie strictly between
`n/4` and `3n/4 + 2`, which is the form the linear isolated-component
campaign consumes (Mat. Sb. **182** (1991), Lemma 23).

**The mechanism**, reconstructed from first principles since no reachable
source carries the proof.  Take the chord `d` from `vs 0` to the middle
vertex `vs m`.  By the dyadic chord lemma every point of `d` is `D`-close
to a side of the first arc *and* — reading `d` backwards as the chord of
the second arc, which is where the closure hypothesis `vs n = vs 0` is
spent — to a side of the second arc.  Sample `d` at unit spacing.  If some
sample carries a near-pair whose index gap already lies in the window, that
pair is the cut.  Otherwise every pair everywhere is *small*
(`4(j-i) ≤ n`) or *large* (`3n ≤ 4(j-i)`); the terminal sample is small
(the two sides meeting at `vs m`, gap `1`) and the initial sample is large
(the two sides meeting at `vs 0` itself, gap `n - 1` — the closure again),
so the least small sample has a large pair one unit before it.  That yields
**four** mutually close points on four sides, and the arithmetic
`3n ≤ 4(j₁-i₁) ∧ 4(j₂-i₂) ≤ n  ⟹  n + 4i₁ ≤ 4i₂ ∨ n + 4j₂ ≤ 4j₁`
forces one of the two *same-arc* index gaps into the window: the cut then
runs between two first-arc sides or two second-arc sides.  No
intermediate-value reasoning survives into the proof — the jump past the
window is itself the witness.

The sampling spacing is `1`, not `δ`, so the statement needs no strict
positivity of `δ` and the bound carries a `+ 1` where the original carries
its `+ η`.
-/

namespace GroupApproximation
namespace Olshanskii

open GroupApproximation.HullGeometry

universe v

variable {X : Type v} [PseudoMetricSpace X]

/-- A *near pair* at a point `x`: a side of the first arc and a side of the
second arc, each carrying a point within `D` of `x`.  The pair records the
two witness points, not just the indices, because the four-point argument
cuts between the points themselves. -/
def NearPair (vs : ℕ → X) (sides : ℕ → ℝ → X) (m n : ℕ) (D : ℝ)
    (x : X) (i j : ℕ) : Prop :=
  i < m ∧ m ≤ j ∧ j < n ∧
    (∃ s ∈ Set.Icc (0 : ℝ) (dist (vs i) (vs (i + 1))),
      dist x (sides i s) ≤ D) ∧
    (∃ s ∈ Set.Icc (0 : ℝ) (dist (vs j) (vs (j + 1))),
      dist x (sides j s) ≤ D)

/-- **The balanced bisection.**  A closed geodesic `n`-gon with `8 ≤ n ≤ 2^c`
has two sides, quarter-separated in index, carrying points at distance at
most `6δ(c+1) + 1` from each other. -/
theorem exists_balanced_cut {δ : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (hgeo : IsGeodesicSpace X)
    {n c : ℕ} (hn : 8 ≤ n) (hc : n ≤ 2 ^ c)
    (vs : ℕ → X) (sides : ℕ → ℝ → X)
    (hsides : IsSideFamily vs sides n) (hclose : vs n = vs 0) :
    ∃ a b : ℕ, a < b ∧ b < n ∧ n ≤ 4 * (b - a) ∧ 4 * (b - a) ≤ 3 * n ∧
      ∃ s ∈ Set.Icc (0 : ℝ) (dist (vs a) (vs (a + 1))),
        ∃ s' ∈ Set.Icc (0 : ℝ) (dist (vs b) (vs (b + 1))),
          dist (sides a s) (sides b s') ≤ 6 * δ * ((c : ℝ) + 1) + 1 := by
  classical
  set m : ℕ := n / 2 with hmdef
  have hm1 : 1 ≤ m := by omega
  have hmn : m < n := by omega
  set D : ℝ := 3 * δ * ((c : ℝ) + 1) with hDdef
  have hD0 : 0 ≤ D := by
    have hc0 : (0 : ℝ) ≤ (c : ℝ) + 1 := by positivity
    have h3 : (0 : ℝ) ≤ 3 * δ := by linarith
    exact mul_nonneg h3 hc0
  -- the chord from `vs 0` to the middle vertex
  obtain ⟨d, hd, hd0, hd1⟩ := hgeo (vs 0) (vs m)
  set L : ℝ := dist (vs 0) (vs m) with hLdef
  have hL0 : 0 ≤ L := dist_nonneg
  -- every point of the chord carries a near pair
  have hpair : ∀ t ∈ Set.Icc (0 : ℝ) L,
      ∃ i j, NearPair vs sides m n D (d t) i j := by
    intro t ht
    -- the first arc: sides `0 … m - 1`
    have hsidesL : IsSideFamily vs sides m := by
      intro i hi
      exact hsides i (by omega)
    obtain ⟨i, hi, s, hs, hdistL⟩ :=
      exists_close_side_of_chord hδ hδ0 hgeo c m hm1 (le_trans (by omega) hc)
        vs sides hsidesL d hd hd0 hd1 t ht
    -- the second arc: sides `m … n - 1`, with the reversed chord
    have hsidesR := hsides.shift (le_of_lt hmn)
    have hkm1 : 1 ≤ n - m := by omega
    have hkmc : n - m ≤ 2 ^ c := le_trans (by omega) hc
    have hvend : vs (m + (n - m)) = vs 0 := by
      have harg : m + (n - m) = n := by omega
      rw [harg]
      exact hclose
    have hv0 : vs (m + 0) = vs m := by
      have h0 : m + 0 = m := by omega
      rw [h0]
    have hLR : dist (vs (m + 0)) (vs (m + (n - m))) = L := by
      rw [hv0, hvend, dist_comm]
    have hrev : IsGeodesicSegment (fun u => d (L - u)) 0
        (dist (vs (m + 0)) (vs (m + (n - m)))) := by
      rw [hLR]
      exact IsGeodesicSegment.reverse_zero hL0 hd
    have hrev0 : (fun u => d (L - u)) 0 = vs (m + 0) := by
      rw [hv0]
      show d (L - 0) = vs m
      have hLL : L - 0 = L := by ring
      rw [hLL]
      exact hd1
    have hrev1 : (fun u => d (L - u))
        (dist (vs (m + 0)) (vs (m + (n - m)))) = vs (m + (n - m)) := by
      rw [hLR, hvend]
      show d (L - L) = vs 0
      have hzero : L - L = 0 := by ring
      rw [hzero]
      exact hd0
    have htrev : L - t ∈ Set.Icc (0 : ℝ)
        (dist (vs (m + 0)) (vs (m + (n - m)))) := by
      rw [hLR]
      constructor
      · linarith [ht.2]
      · linarith [ht.1]
    obtain ⟨j', hj', s', hs', hdistR⟩ :=
      exists_close_side_of_chord hδ hδ0 hgeo c (n - m) hkm1 hkmc
        (fun a => vs (m + a)) (fun a => sides (m + a)) hsidesR
        (fun u => d (L - u)) hrev hrev0 hrev1 (L - t) htrev
    have hdistR' : dist (d t) (sides (m + j') s') ≤ D := by
      have harg : L - (L - t) = t := by ring
      calc dist (d t) (sides (m + j') s')
          = dist (d (L - (L - t))) (sides (m + j') s') := by rw [harg]
        _ ≤ D := hdistR
    refine ⟨i, m + j', hi, by omega, by omega, ⟨s, hs, hdistL⟩, ?_⟩
    have harg2 : m + j' + 1 = m + (j' + 1) := by omega
    rw [harg2]
    exact ⟨s', hs', hdistR'⟩
  -- a near pair whose gap lies in the window is the cut
  have hcut : ∀ (x : X) (i j : ℕ), NearPair vs sides m n D x i j →
      n ≤ 4 * (j - i) → 4 * (j - i) ≤ 3 * n →
      ∃ a b : ℕ, a < b ∧ b < n ∧ n ≤ 4 * (b - a) ∧ 4 * (b - a) ≤ 3 * n ∧
        ∃ s ∈ Set.Icc (0 : ℝ) (dist (vs a) (vs (a + 1))),
          ∃ s' ∈ Set.Icc (0 : ℝ) (dist (vs b) (vs (b + 1))),
            dist (sides a s) (sides b s') ≤ 6 * δ * ((c : ℝ) + 1) + 1 := by
    intro x i j hpr hlo hhi
    obtain ⟨hi, hmj, hj, ⟨s, hs, hdi⟩, ⟨s', hs', hdj⟩⟩ := hpr
    have hij : i < j := by omega
    refine ⟨i, j, hij, hj, hlo, hhi, s, hs, s', hs', ?_⟩
    have htri := dist_triangle (sides i s) x (sides j s')
    have hsymm : dist (sides i s) x = dist x (sides i s) := dist_comm _ _
    have hsum : dist (sides i s) x + dist x (sides j s') ≤ D + D := by
      rw [hsymm]
      exact add_le_add hdi hdj
    have hDD : D + D = 6 * δ * ((c : ℝ) + 1) := by
      rw [hDdef]
      ring
    have hfinal : dist (sides i s) (sides j s')
        ≤ 6 * δ * ((c : ℝ) + 1) := by
      rw [hDD] at hsum
      exact le_trans htri hsum
    linarith
  -- the sampling: `τ k = min k L`, unit spacing
  set τ : ℕ → ℝ := fun k => min (k : ℝ) L with hτdef
  have hτmem : ∀ k, τ k ∈ Set.Icc (0 : ℝ) L := by
    intro k
    constructor
    · have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      exact le_min hk0 hL0
    · exact min_le_right _ _
  have hτstep : ∀ k, dist (d (τ k)) (d (τ (k + 1))) ≤ 1 := by
    intro k
    have h1 := hτmem k
    have h2 := hτmem (k + 1)
    have hdist := hd (τ k) h1 (τ (k + 1)) h2
    have hle : τ k ≤ τ (k + 1) := by
      have hcast : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
        push_cast
        linarith
      exact min_le_min hcast (le_refl L)
    have hup : τ (k + 1) ≤ (k : ℝ) + 1 := by
      have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      have hmin : τ (k + 1) ≤ ((k + 1 : ℕ) : ℝ) := min_le_left _ _
      rw [hcast] at hmin
      exact hmin
    have hgap : τ (k + 1) - τ k ≤ 1 := by
      rcases min_choice ((k : ℝ)) L with hch | hch
      · have hk : (k : ℝ) ≤ τ k := le_of_eq hch.symm
        linarith
      · have hLτ : L ≤ τ k := le_of_eq hch.symm
        have hτk1 : τ (k + 1) ≤ L := min_le_right _ _
        linarith
    calc dist (d (τ k)) (d (τ (k + 1))) = |τ k - τ (k + 1)| := hdist
      _ = τ (k + 1) - τ k := by
          rw [abs_sub_comm]
          exact abs_of_nonneg (by linarith)
      _ ≤ 1 := hgap
  set K : ℕ := Nat.ceil L with hKdef
  have hτK : τ K = L := min_eq_right (Nat.le_ceil L)
  have hτ0 : τ 0 = 0 := by
    have h0 : ((0 : ℕ) : ℝ) = 0 := Nat.cast_zero
    calc τ 0 = min ((0 : ℕ) : ℝ) L := rfl
      _ = min 0 L := by rw [h0]
      _ = 0 := min_eq_left hL0
  -- the direct case: some sample already carries a window pair
  by_cases hA : ∃ k, ∃ i j, NearPair vs sides m n D (d (τ k)) i j ∧
      n ≤ 4 * (j - i) ∧ 4 * (j - i) ≤ 3 * n
  · obtain ⟨k, i, j, hpr, hlo, hhi⟩ := hA
    exact hcut (d (τ k)) i j hpr hlo hhi
  -- the dichotomy: every pair at every sample is small or large
  push Not at hA
  have hdicho : ∀ k i j, NearPair vs sides m n D (d (τ k)) i j →
      4 * (j - i) ≤ n ∨ 3 * n ≤ 4 * (j - i) := by
    intro k i j hpr
    by_cases hsmall : 4 * (j - i) ≤ n
    · left
      exact hsmall
    · right
      have hgt : n ≤ 4 * (j - i) := by omega
      exact le_of_lt (hA k i j hpr hgt)
  -- the terminal sample is small: the two sides meeting at `vs m`
  have hdK : d (τ K) = vs m := by
    rw [hτK]
    exact hd1
  have hSmallK : ∃ i j, NearPair vs sides m n D (d (τ K)) i j ∧
      4 * (j - i) ≤ n := by
    obtain ⟨hsegA, hsegA0, hsegA1⟩ := hsides (m - 1) (by omega)
    obtain ⟨hsegB, hsegB0, hsegB1⟩ := hsides m hmn
    have hidx : m - 1 + 1 = m := by omega
    refine ⟨m - 1, m, ⟨by omega, le_refl m, hmn, ?_, ?_⟩, by omega⟩
    · -- the end of side `m - 1` is `vs m`
      refine ⟨dist (vs (m - 1)) (vs (m - 1 + 1)),
        ⟨dist_nonneg, le_refl _⟩, ?_⟩
      have hend : sides (m - 1) (dist (vs (m - 1)) (vs (m - 1 + 1)))
          = vs m := by
        rw [hsegA1, hidx]
      rw [hdK, hend]
      have hzero : dist (vs m) (vs m) = 0 := dist_self _
      rw [hzero]
      exact hD0
    · -- the start of side `m` is `vs m`
      refine ⟨0, ⟨le_refl 0, dist_nonneg⟩, ?_⟩
      rw [hdK, hsegB0]
      have hzero : dist (vs m) (vs m) = 0 := dist_self _
      rw [hzero]
      exact hD0
  set Small : ℕ → Prop := fun k => ∃ i j,
    NearPair vs sides m n D (d (τ k)) i j ∧ 4 * (j - i) ≤ n with hSdef
  have hex : ∃ k, Small k := ⟨K, hSmallK⟩
  set k₀ : ℕ := Nat.find hex with hk₀def
  have hk₀spec : Small k₀ := Nat.find_spec hex
  obtain ⟨i₂, j₂, hpr₂, hsm₂⟩ := hk₀spec
  -- a large pair at unit distance (or at the same point, for `k₀ = 0`)
  have hlarge : ∃ (x₁ : X) (i₁ j₁ : ℕ),
      NearPair vs sides m n D x₁ i₁ j₁ ∧ 3 * n ≤ 4 * (j₁ - i₁) ∧
        dist x₁ (d (τ k₀)) ≤ 1 := by
    rcases Nat.eq_zero_or_pos k₀ with hk0 | hkpos
    · -- the canonical large pair at `vs 0` itself
      obtain ⟨hsegA, hsegA0, hsegA1⟩ := hsides 0 (by omega)
      obtain ⟨hsegB, hsegB0, hsegB1⟩ := hsides (n - 1) (by omega)
      have hd00 : d (τ k₀) = vs 0 := by
        rw [hk0, hτ0]
        exact hd0
      have hidx : n - 1 + 1 = n := by omega
      refine ⟨d (τ k₀), 0, n - 1, ⟨by omega, by omega, by omega, ?_, ?_⟩,
        by omega, ?_⟩
      · -- the start of side `0` is `vs 0`
        refine ⟨0, ⟨le_refl 0, dist_nonneg⟩, ?_⟩
        rw [hd00, hsegA0]
        have hzero : dist (vs 0) (vs 0) = 0 := dist_self _
        rw [hzero]
        exact hD0
      · -- the end of side `n - 1` is `vs n = vs 0`
        refine ⟨dist (vs (n - 1)) (vs (n - 1 + 1)),
          ⟨dist_nonneg, le_refl _⟩, ?_⟩
        have hend : sides (n - 1) (dist (vs (n - 1)) (vs (n - 1 + 1)))
            = vs 0 := by
          rw [hsegB1, hidx]
          exact hclose
        rw [hd00, hend]
        have hzero : dist (vs 0) (vs 0) = 0 := dist_self _
        rw [hzero]
        exact hD0
      · have hzero : dist (d (τ k₀)) (d (τ k₀)) = 0 := dist_self _
        rw [hzero]
        norm_num
    · -- `k₀ ≥ 1`: the predecessor sample is not small, hence large
      have hpred : ¬ Small (k₀ - 1) := Nat.find_min hex (by omega)
      obtain ⟨i₁, j₁, hpr₁⟩ := hpair (τ (k₀ - 1)) (hτmem (k₀ - 1))
      have hnotsmall : ¬ (4 * (j₁ - i₁) ≤ n) := by
        intro hcontra
        exact hpred ⟨i₁, j₁, hpr₁, hcontra⟩
      have hlrg : 3 * n ≤ 4 * (j₁ - i₁) := by
        rcases hdicho (k₀ - 1) i₁ j₁ hpr₁ with hsm | hlg
        · exact absurd hsm hnotsmall
        · exact hlg
      have hstep : dist (d (τ (k₀ - 1))) (d (τ k₀)) ≤ 1 := by
        have harg : k₀ - 1 + 1 = k₀ := by omega
        have hst := hτstep (k₀ - 1)
        rw [harg] at hst
        exact hst
      exact ⟨d (τ (k₀ - 1)), i₁, j₁, hpr₁, hlrg, hstep⟩
  obtain ⟨x₁, i₁, j₁, hpr₁, hlrg₁, hx₁⟩ := hlarge
  obtain ⟨hi₁, hmj₁, hj₁, ⟨sA, hsA, hdA⟩, ⟨sB, hsB, hdB⟩⟩ := hpr₁
  obtain ⟨hi₂, hmj₂, hj₂, ⟨sC, hsC, hdC⟩, ⟨sD', hsD, hdD⟩⟩ := hpr₂
  -- the four-point arithmetic: one same-arc gap lands in the window
  have hsplit : (n + 4 * i₁ ≤ 4 * i₂ ∧ i₁ < i₂) ∨
      (n + 4 * j₂ ≤ 4 * j₁ ∧ j₂ < j₁) := by omega
  -- any first point and any second point are within `2D + 1`
  have hcross : ∀ (p q : X), dist x₁ p ≤ D → dist (d (τ k₀)) q ≤ D →
      dist p q ≤ 6 * δ * ((c : ℝ) + 1) + 1 := by
    intro p q hp hq
    have h1 := dist_triangle p x₁ (d (τ k₀))
    have h2 := dist_triangle p (d (τ k₀)) q
    have hpx : dist p x₁ = dist x₁ p := dist_comm _ _
    have hDD : D + D = 6 * δ * ((c : ℝ) + 1) := by
      rw [hDdef]
      ring
    rw [hpx] at h1
    have hmid : dist p (d (τ k₀)) ≤ D + 1 := by
      linarith
    have hfinal : dist p q ≤ D + 1 + D := by
      linarith
    linarith [hDD.le, hDD.ge]
  rcases hsplit with ⟨hwin, hab⟩ | ⟨hwin, hab⟩
  · -- the cut runs between the two first-arc sides `i₁ < i₂`
    refine ⟨i₁, i₂, hab, by omega, by omega, by omega,
      sA, hsA, sC, hsC, ?_⟩
    exact hcross (sides i₁ sA) (sides i₂ sC) hdA hdC
  · -- the cut runs between the two second-arc sides `j₂ < j₁`
    refine ⟨j₂, j₁, hab, by omega, by omega, by omega,
      sD', hsD, sB, hsB, ?_⟩
    have h := hcross (sides j₁ sB) (sides j₂ sD') hdB hdD
    have hsymm : dist (sides j₂ sD') (sides j₁ sB)
        = dist (sides j₁ sB) (sides j₂ sD') := dist_comm _ _
    rw [hsymm]
    exact h

end Olshanskii
end GroupApproximation
