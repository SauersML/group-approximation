import GroupApproximation.GGT.VanKampen.Estimating.UnboundPolygonCut

/-!
# The small-polygon case of Ol'shanskii's Lemma 25

Ol'shanskii's Lemma 25, in the aggregate form Osin cites as `N123`, splits the
sides of a geodesic `r`-gon into three classes and assumes only that the first
class is long in total: `sigma_1 > a * r` and `sigma_3 < a * r / 1000`.  Its
proof recurses on the side count until a piece has at most eight sides.

This file is that base case.  At `r <= 8` no recursion is needed: the landed
sampling lemma `Olshanskii.exists_long_close_pair` already applies, because its
hypothesis is the raw one, `(r - 1) * (beta + 4 * D) + rho < |p_1|`, and at
eight sides that reads `15 * a / 1000 + 336 * delta < a`, which holds once
`a >= 342 * delta`.

The packaged form `exists_long_close_pair_of_short_complement` does not apply
here, and the reason is worth recording: it asks for `1000 * rho < |p_1|`,
while the aggregate hypothesis only gives `rho < a * r / 1000`, so at `r = 8`
it is short by a factor of eight.  The raw form spends the short class against
the sampling spacing instead of against the long side, and that is what makes
the small case go through.

Constants: the closeness is `12 * delta`, the dyadic chord constant at eight
sides, and the subsegments have length `a / 1000`.  Both are Osin's `c_1` and
his `10^-3 a`, and both depend only on `delta`.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen
namespace Estimating

open GroupApproximation.HullGeometry
open GroupApproximation.Olshanskii

universe v

/-- The sampling hypothesis of `exists_long_close_pair` holds at eight sides.
The bound is `15 * a / 1000 + 336 * delta`, and `a >= 342 * delta` leaves it
below `a` with room to spare. -/
theorem smallPolygon_sampling_bound {a delta : ℝ} {n : ℕ}
    (hn8 : n ≤ 8) (ha0 : 0 < a) (hdelta : 0 ≤ delta)
    (hac : 342 * delta ≤ a) :
    ((n : ℝ) - 1) * (a / 1000 + 4 * (12 * delta)) + a / 1000 * (n : ℝ) < a := by
  have hnR : (n : ℝ) ≤ 8 := by exact_mod_cast hn8
  have hn1 : (n : ℝ) - 1 ≤ 7 := by linarith
  have hpos : (0 : ℝ) ≤ a / 1000 + 4 * (12 * delta) := by linarith
  have h1 : ((n : ℝ) - 1) * (a / 1000 + 4 * (12 * delta)) ≤
      7 * (a / 1000 + 4 * (12 * delta)) :=
    mul_le_mul_of_nonneg_right hn1 hpos
  have h2 : a / 1000 * (n : ℝ) ≤ a / 1000 * 8 :=
    mul_le_mul_of_nonneg_left hnR (by linarith)
  linarith

/-- **Ol'shanskii's Lemma 25 at eight sides or fewer.**  A closed geodesic
`n`-gon with `n <= 8`, read from a side longer than `a`, whose other sides
outside a class `S` have total length at most `a * n / 1000`, has a side in
`S` carrying a segment of length `a / 1000` that runs `12 * delta`-close to a
segment of the same length on the long side.

This is the base of the recursion: `sigma_3 < a * r / 1000` and
`|p_1| > a >= 342 * delta` are exactly Osin's `N123` hypotheses at small `r`,
and the conclusion is his, with `c_1 = 12 * delta`. -/
theorem exists_long_close_pair_small_polygon {X : Type v} [PseudoMetricSpace X]
    {delta a : ℝ}
    (hdelta : IsHyperbolicSpace delta X) (hdelta0 : 0 ≤ delta)
    (hgeo : IsGeodesicSpace X)
    {n b : ℕ} (hn : 2 ≤ n) (hn8 : n ≤ 8)
    {vs : ℕ → X} {sides : ℕ → ℝ → X}
    (hpoly : IsClosedPolygonAt vs sides b n)
    (S : Set ℕ) (w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hshort : ∀ i, b < i → i < b + n → i ∉ S →
      dist (vs i) (vs (i + 1)) ≤ w i)
    (hshortTotal : ∑ j ∈ Finset.range (n - 1), w (b + 1 + j) ≤ a / 1000 * n)
    (ha0 : 0 < a) (hac : 342 * delta ≤ a)
    (hlong : a < dist (vs b) (vs (b + 1))) :
    ∃ i, b < i ∧ i < b + n ∧ i ∈ S ∧
      ∃ u ∈ Set.Icc (0 : ℝ) (dist (vs b) (vs (b + 1))),
        ∃ u' ∈ Set.Icc (0 : ℝ) (dist (vs b) (vs (b + 1))),
          ∃ s ∈ Set.Icc (0 : ℝ) (dist (vs i) (vs (i + 1))),
            ∃ s' ∈ Set.Icc (0 : ℝ) (dist (vs i) (vs (i + 1))),
              a / 1000 ≤ u' - u ∧ a / 1000 ≤ |s' - s| ∧
                dist (sides b u) (sides i s) ≤ 12 * delta ∧
                dist (sides b u') (sides i s') ≤ 12 * delta := by
  have hc : n - 1 ≤ 2 ^ 3 := by omega
  have hD : 3 * delta * (((3 : ℕ) : ℝ) + 1) ≤ 12 * delta := by
    push_cast
    linarith
  have hbeta : (0 : ℝ) < a / 1000 := by linarith
  have hbound :
      ((n : ℝ) - 1) * (a / 1000 + 4 * (12 * delta)) + a / 1000 * (n : ℝ) <
        dist (vs b) (vs (b + 1)) :=
    lt_trans (smallPolygon_sampling_bound hn8 ha0 hdelta0 hac) hlong
  exact exists_long_close_pair hdelta hdelta0 hgeo hn hc hpoly hD S w hw
    hshort hshortTotal hbeta hbound

/-! ## Model checks -/

/-- The sampling bound is tight in the constant it needs: at `n = 8` and
`a = 342 * delta` the left side is `0.9974...` times `a`, so the argument has
margin, and the constant `342` is not padding an unavailable inequality. -/
theorem smallPolygon_sampling_bound_eightGon_model {delta : ℝ}
    (hdelta : 0 < delta) :
    ((8 : ℝ) - 1) * (342 * delta / 1000 + 4 * (12 * delta)) +
        342 * delta / 1000 * (8 : ℝ) < 342 * delta :=
  smallPolygon_sampling_bound (n := 8) (a := 342 * delta) (delta := delta)
    (le_refl 8) (by linarith) (le_of_lt hdelta) (le_refl _)

/-- The bound fails without the lower bound on `a` against `delta`: at
`a = delta` and eight sides the chord term alone already exceeds `a`. -/
theorem smallPolygon_sampling_bound_needs_constant {delta : ℝ}
    (hdelta : 0 < delta) :
    ¬ (((8 : ℝ) - 1) * (delta / 1000 + 4 * (12 * delta)) +
        delta / 1000 * (8 : ℝ) < delta) := by
  intro hlt
  linarith

end Estimating
end VanKampen
end GGT
end GroupApproximation
