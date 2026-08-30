import GroupApproximation.GGT.OlshanskiiChord

/-!
# Ol'shanskii's Lemma 25: a long side of a polygon fellow-travels another side

Third module of the reconstruction of Ol'shanskii's polygon lemmas
(Mat. Sb. **182** (1991), Lemmas 23 and 25), whose proofs appear in none of
the sources this repository can reach.  The statement reconstructed here is
Lemma 25 in the form Hull's small-cancellation argument consumes it: the
sides of a closed geodesic `n`-gon are split into a *short* class of total
length at most `ρ` and a *long* class; if one long side exceeds the whole
short class plus a linear-in-`n` allowance, then it and some *other* long
side carry long segments that run alongside each other.

## The proof, and why it is not the recursion

Fix a side `b`.  Reverse it: the other `n - 1` sides form a broken line with
the same two endpoints, so by the dyadic chord lemma
(`exists_close_side_of_chord`) every point of side `b` lies within
`D := 3δ(c+1)` of one of the other sides, where `n - 1 ≤ 2 ^ c`.  Sample side
`b` at spacing `Δ := β + 2 D` and record, for each sample, the index of a
side carrying a `D`-close witness.

*If two samples record the same long side, that is the conclusion.*  Their
witnesses are at least `Δ - 2 D = β` apart on that side, because two points
`D`-close to points `Δ` apart on a geodesic are at least `Δ - 2 D` apart.

*Otherwise* each long side takes at most one sample, and a short side of
length `ℓ` takes at most `1 + (ℓ + 2 D)/Δ` of them, by the same estimate read
backwards.  Counting the samples fibrewise over the recorded index gives
`(N+1) Δ ≤ (n-1) Δ + ρ + 2 D (n-1)`, while the samples fill side `b`, so
`(N+1) Δ` exceeds its length.  The hypothesis is exactly the gap between
these two, and the two cases are exhaustive.

**This is not the route the plan called for, and the divergence is
deliberate.**  The planned route was Ol'shanskii's own: bisect recursively
until every piece has at most eight sides, then run a bounded number of thin
quadrilaterals inside a piece.  That route buys the printed closeness
constant `13δ` -- which is exactly the eight-gon chord constant, `3δ·4 = 12δ`
plus slack -- but it pays for it in the short class: each cut becomes a new
short side, there are between `(n-8)/4` and `n-5` cuts (a cut adds exactly
four to the total side count, and every piece it produces has at least five
sides), and summing the per-cut chord bound over the recursion tree is of
order `n log n` in the worst case.  The hypothesis `θ > ξ n` with `ξ` an
absolute multiple of `δ` pays only order `n`.  Spelled out at the printed
constants, the recursion needs `2·10³ δ n (2 + log₂ n) < 3·10⁴ δ n`, that is
`n < 2¹³`; no absolute `ξ` repairs it, since the slack `10³/10⁴` is a
constant and the deficit is a logarithm.

So the reconstruction keeps Ol'shanskii's hypothesis *shape* and his numeral
`3·10⁴`, and moves the logarithm into the constant instead of into the
budget: `ξ ≥ 3·10⁴ δ` becomes `ξ ≥ 3·10⁴ δ (c+1)` for `n - 1 ≤ 2 ^ c`, and
the closeness `13δ` becomes `3δ(c+1)` between the endpoints of the two
segments, or `3δ(c+1) + 6δ` between the segments themselves
(`exists_close_of_subsegments`).  Consumers take `c := Nat.clog 2 (n-1)`.
Every other feature of the printed statement -- the linear `ξ n`, the factor
`10³` on `ρ`, the segment length `ξ/1000` -- comes out unchanged; see
`exists_long_close_pair_of_short_complement`.

The balanced-cut theorem of the second module is not used here: it is the
input to Lemma 23's consumer, the linear isolated-component bound, and not to
this one.

## Conventions

Sides arrive as explicit geodesic parametrisations, as in the first module,
and the polygon is read from the vertex `b` with the closing condition
`vs (b + n) = vs b`; the indices `b, …, b + n - 1` name its sides, so no
modular arithmetic enters.  The short class is presented by a weight function
`w` rather than by a length sum over a subset, which makes the total-length
hypothesis a single sum over `Finset.range (n-1)` and costs the consumer
nothing.  The constant is `3δ` per dyadic level, not Ol'shanskii's `δ`,
because hyperbolicity here is the four-point condition and its triangles are
`3δ`-thin.
-/

namespace GroupApproximation
namespace Olshanskii

open GroupApproximation.HullGeometry

universe v

variable {X : Type v} [PseudoMetricSpace X]

/-- A closed geodesic polygon read from the vertex `b`: the `n` sides
`b, …, b + n - 1` are geodesics between consecutive vertices, and the walk
closes up at `vs (b + n) = vs b`. -/
def IsClosedPolygonAt (vs : ℕ → X) (sides : ℕ → ℝ → X) (b n : ℕ) : Prop :=
  (∀ i, b ≤ i → i < b + n →
      IsGeodesicSegment (sides i) 0 (dist (vs i) (vs (i + 1))) ∧
        sides i 0 = vs i ∧ sides i (dist (vs i) (vs (i + 1))) = vs (i + 1)) ∧
    vs (b + n) = vs b

/-! ### Reparametrising a geodesic on a subinterval -/

/-- A geodesic restricted to `[u, u']` and shifted to start at `0`. -/
theorem isGeodesicSegment_shift {f : ℝ → X} {M u u' : ℝ}
    (h : IsGeodesicSegment f 0 M) (hu : 0 ≤ u) (hu' : u' ≤ M) :
    IsGeodesicSegment (fun r => f (u + r)) 0 (u' - u) := by
  intro s hs t ht
  have hs' : u + s ∈ Set.Icc (0 : ℝ) M :=
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have ht' : u + t ∈ Set.Icc (0 : ℝ) M :=
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  show dist (f (u + s)) (f (u + t)) = |s - t|
  rw [h (u + s) hs' (u + t) ht']
  have he : u + s - (u + t) = s - t := by ring
  rw [he]

/-- A geodesic restricted to `[u, u']`, shifted to start at `0` and read
backwards. -/
theorem isGeodesicSegment_shift_rev {f : ℝ → X} {M u u' : ℝ}
    (h : IsGeodesicSegment f 0 M) (hu : 0 ≤ u) (hu' : u' ≤ M) :
    IsGeodesicSegment (fun r => f (u' - r)) 0 (u' - u) := by
  intro s hs t ht
  have hs' : u' - s ∈ Set.Icc (0 : ℝ) M :=
    ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have ht' : u' - t ∈ Set.Icc (0 : ℝ) M :=
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  show dist (f (u' - s)) (f (u' - t)) = |s - t|
  rw [h (u' - s) hs' (u' - t) ht']
  have he : u' - s - (u' - t) = -(s - t) := by ring
  rw [he, abs_neg]

/-! ### Two geodesics with close endpoints fellow-travel -/

/-- **Endpoints close, whole segments close.**  If the two ends of one
geodesic are within `E` of the two ends of another, every point of the first
is within `E + 6δ` of the second.  Two thin triangles: one across the
diagonal `x → y'`, one back across `x → x'`, and each degenerate alternative
is absorbed by the `E`-short side it lands on. -/
theorem exists_close_of_endpoints_close {δ E : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (hgeo : IsGeodesicSpace X)
    {x y x' y' : X} {f f' : ℝ → X}
    (hf : IsGeodesicSegment f 0 (dist x y)) (hf0 : f 0 = x)
    (hf1 : f (dist x y) = y)
    (hf' : IsGeodesicSegment f' 0 (dist x' y')) (hf'0 : f' 0 = x')
    (hf'1 : f' (dist x' y') = y')
    (hx : dist x x' ≤ E) (hy : dist y y' ≤ E)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) (dist x y)) :
    ∃ s ∈ Set.Icc (0 : ℝ) (dist x' y'), dist (f t) (f' s) ≤ E + 6 * δ := by
  have hE0 : (0 : ℝ) ≤ E := le_trans dist_nonneg hx
  obtain ⟨h, hh, hh0, hh1⟩ := hgeo x y'
  obtain ⟨k, hk, hk0, hk1⟩ := hgeo y' y
  rcases exists_close_on_other_side_of_geodesic_triangle hδ hδ0
      hf hf0 hf1 hh hh0 hh1 hk hk0 hk1 ht with ⟨z, hz, hzd⟩ | ⟨z, hz, hzd⟩
  · -- the point is `3δ`-close to the diagonal `[x, y']`
    obtain ⟨p, hp, hp0, hp1⟩ := hgeo x x'
    rcases exists_close_on_other_side_of_geodesic_triangle hδ hδ0
        hh hh0 hh1 hp hp0 hp1 hf' hf'0 hf'1 hz with ⟨q, hq, hqd⟩ | ⟨q, hq, hqd⟩
    · -- it lands on the short side `[x, x']`, so it is near `x' = f' 0`
      refine ⟨0, ⟨le_refl 0, dist_nonneg⟩, ?_⟩
      have hend : dist (p q) (p (dist x x')) = |q - dist x x'| :=
        hp q hq (dist x x') ⟨dist_nonneg, le_refl _⟩
      rw [hp1] at hend
      have hqle : q ≤ dist x x' := hq.2
      have habs : |q - dist x x'| = dist x x' - q := by
        rw [abs_sub_comm]
        exact abs_of_nonneg (by linarith)
      rw [habs] at hend
      have hq0 : (0 : ℝ) ≤ q := hq.1
      have hpx : dist (p q) x' ≤ E := by linarith
      have h4 := dist_triangle4 (f t) (h z) (p q) x'
      rw [hf'0]
      linarith
    · -- it lands on the second geodesic itself
      refine ⟨q, hq, ?_⟩
      have htri := dist_triangle (f t) (h z) (f' q)
      linarith
  · -- the point is `3δ`-close to the short side `[y', y]`, so near `y'`
    refine ⟨dist x' y', ⟨dist_nonneg, le_refl _⟩, ?_⟩
    rw [hf'1]
    have hend : dist (k z) (k 0) = |z - 0| :=
      hk z hz 0 ⟨le_refl 0, dist_nonneg⟩
    rw [hk0] at hend
    have hz0 : (0 : ℝ) ≤ z := hz.1
    have habs : |z - 0| = z := by
      rw [sub_zero]
      exact abs_of_nonneg hz0
    rw [habs] at hend
    have hzy : z ≤ dist y' y := hz.2
    have hyy : dist y' y = dist y y' := dist_comm _ _
    rw [hyy] at hzy
    have hky : dist (k z) y' ≤ E := by linarith
    have htri := dist_triangle (f t) (k z) y'
    linarith

/-- **Subsegments with close endpoints fellow-travel.**  The packaged form of
`exists_close_of_endpoints_close`: the two subsegments are cut out of two
given geodesics, in either relative orientation. -/
theorem exists_close_of_subsegments {δ E : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (hgeo : IsGeodesicSpace X)
    {f f' : ℝ → X} {M M' u u' s s' : ℝ}
    (hf : IsGeodesicSegment f 0 M) (hu : 0 ≤ u) (huu : u ≤ u') (hu' : u' ≤ M)
    (hf' : IsGeodesicSegment f' 0 M')
    (hs : 0 ≤ s) (hsM : s ≤ M') (hs' : 0 ≤ s') (hs'M : s' ≤ M')
    (hx : dist (f u) (f' s) ≤ E) (hy : dist (f u') (f' s') ≤ E)
    {r : ℝ} (hr : r ∈ Set.Icc u u') :
    ∃ q, min s s' ≤ q ∧ q ≤ max s s' ∧ dist (f r) (f' q) ≤ E + 6 * δ := by
  have hume : u ∈ Set.Icc (0 : ℝ) M := ⟨hu, le_trans huu hu'⟩
  have hu'me : u' ∈ Set.Icc (0 : ℝ) M := ⟨le_trans hu huu, hu'⟩
  have hdxy : dist (f u) (f u') = u' - u := by
    rw [hf u hume u' hu'me, abs_sub_comm]
    exact abs_of_nonneg (by linarith)
  have hg : IsGeodesicSegment (fun z => f (u + z)) 0 (dist (f u) (f u')) := by
    rw [hdxy]
    exact isGeodesicSegment_shift hf hu hu'
  have hg0 : (fun z => f (u + z)) 0 = f u := by
    show f (u + 0) = f u
    rw [add_zero]
  have hg1 : (fun z => f (u + z)) (dist (f u) (f u')) = f u' := by
    rw [hdxy]
    show f (u + (u' - u)) = f u'
    have he : u + (u' - u) = u' := by ring
    rw [he]
  have hrt : r - u ∈ Set.Icc (0 : ℝ) (dist (f u) (f u')) := by
    rw [hdxy]
    exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hshift : f (u + (r - u)) = f r := by
    have he : u + (r - u) = r := by ring
    rw [he]
  have hsme : s ∈ Set.Icc (0 : ℝ) M' := ⟨hs, hsM⟩
  have hs'me : s' ∈ Set.Icc (0 : ℝ) M' := ⟨hs', hs'M⟩
  rcases le_total s s' with hss | hss
  · -- the two subsegments run in the same direction
    have hd' : dist (f' s) (f' s') = s' - s := by
      rw [hf' s hsme s' hs'me, abs_sub_comm]
      exact abs_of_nonneg (by linarith)
    have hg' : IsGeodesicSegment (fun z => f' (s + z)) 0
        (dist (f' s) (f' s')) := by
      rw [hd']
      exact isGeodesicSegment_shift hf' hs hs'M
    have hg'0 : (fun z => f' (s + z)) 0 = f' s := by
      show f' (s + 0) = f' s
      rw [add_zero]
    have hg'1 : (fun z => f' (s + z)) (dist (f' s) (f' s')) = f' s' := by
      rw [hd']
      show f' (s + (s' - s)) = f' s'
      have he : s + (s' - s) = s' := by ring
      rw [he]
    obtain ⟨q0, hq0, hq0d⟩ := exists_close_of_endpoints_close hδ hδ0 hgeo
      hg hg0 hg1 hg' hg'0 hg'1 hx hy hrt
    rw [hshift] at hq0d
    rw [hd'] at hq0
    refine ⟨s + q0, ?_, ?_, hq0d⟩
    · rw [min_eq_left hss]
      linarith [hq0.1]
    · rw [max_eq_right hss]
      linarith [hq0.2]
  · -- the second subsegment runs backwards
    have hd' : dist (f' s) (f' s') = s - s' := by
      rw [hf' s hsme s' hs'me]
      exact abs_of_nonneg (by linarith)
    have hg' : IsGeodesicSegment (fun z => f' (s - z)) 0
        (dist (f' s) (f' s')) := by
      rw [hd']
      exact isGeodesicSegment_shift_rev hf' hs' hsM
    have hg'0 : (fun z => f' (s - z)) 0 = f' s := by
      show f' (s - 0) = f' s
      rw [sub_zero]
    have hg'1 : (fun z => f' (s - z)) (dist (f' s) (f' s')) = f' s' := by
      rw [hd']
      show f' (s - (s - s')) = f' s'
      have he : s - (s - s') = s' := by ring
      rw [he]
    obtain ⟨q0, hq0, hq0d⟩ := exists_close_of_endpoints_close hδ hδ0 hgeo
      hg hg0 hg1 hg' hg'0 hg'1 hx hy hrt
    rw [hshift] at hq0d
    rw [hd'] at hq0
    refine ⟨s - q0, ?_, ?_, hq0d⟩
    · rw [min_eq_right hss]
      linarith [hq0.2]
    · rw [max_eq_left hss]
      linarith [hq0.1]

/-! ### Every point of a side is close to another side -/

/-- **The complementary arc.**  In a closed geodesic `n`-gon read from `b`,
every point of side `b` lies within `3δ(c+1)` of one of the other `n - 1`
sides, where `n - 1 ≤ 2 ^ c`.  Side `b`, read backwards, is a geodesic chord
of the broken line formed by the others, so this is the dyadic chord lemma;
the closing condition `vs (b + n) = vs b` is what makes the endpoints
agree. -/
theorem exists_close_other_side {δ : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (hgeo : IsGeodesicSpace X)
    {n c b : ℕ} (hn : 2 ≤ n) (hc : n - 1 ≤ 2 ^ c)
    {vs : ℕ → X} {sides : ℕ → ℝ → X}
    (hpoly : IsClosedPolygonAt vs sides b n)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) (dist (vs b) (vs (b + 1)))) :
    ∃ j < n - 1, ∃ s ∈ Set.Icc (0 : ℝ)
        (dist (vs (b + 1 + j)) (vs (b + 1 + j + 1))),
      dist (sides b (dist (vs b) (vs (b + 1)) - t)) (sides (b + 1 + j) s)
        ≤ 3 * δ * ((c : ℝ) + 1) := by
  have hside := hpoly.1
  have hcl := hpoly.2
  have hbn : b < b + n := by omega
  obtain ⟨hb, hb0, hb1⟩ := hside b (le_refl b) hbn
  have hL0 : (0 : ℝ) ≤ dist (vs b) (vs (b + 1)) := dist_nonneg
  -- the broken line formed by the remaining sides
  have hfam : IsSideFamily (fun j => vs (b + 1 + j))
      (fun j => sides (b + 1 + j)) (n - 1) := by
    intro j hj
    have h1 : b ≤ b + 1 + j := by omega
    have h2 : b + 1 + j < b + n := by omega
    have hstep := hside (b + 1 + j) h1 h2
    have harg : b + 1 + j + 1 = b + 1 + (j + 1) := by omega
    rw [harg] at hstep
    exact hstep
  have hk1 : 1 ≤ n - 1 := by omega
  have hA : vs (b + 1 + 0) = vs (b + 1) := by
    have harg : b + 1 + 0 = b + 1 := by omega
    rw [harg]
  have hB : vs (b + 1 + (n - 1)) = vs b := by
    have harg : b + 1 + (n - 1) = b + n := by omega
    rw [harg]
    exact hcl
  have hLR : dist (vs (b + 1 + 0)) (vs (b + 1 + (n - 1)))
      = dist (vs b) (vs (b + 1)) := by
    rw [hA, hB, dist_comm]
  -- side `b`, read backwards, is a chord of that broken line
  have hrev : IsGeodesicSegment
      (fun r => sides b (dist (vs b) (vs (b + 1)) - r)) 0
      (dist (vs (b + 1 + 0)) (vs (b + 1 + (n - 1)))) := by
    rw [hLR]
    exact IsGeodesicSegment.reverse_zero hL0 hb
  have hrev0 : (fun r => sides b (dist (vs b) (vs (b + 1)) - r)) 0
      = vs (b + 1 + 0) := by
    rw [hA]
    show sides b (dist (vs b) (vs (b + 1)) - 0) = vs (b + 1)
    rw [sub_zero]
    exact hb1
  have hrev1 : (fun r => sides b (dist (vs b) (vs (b + 1)) - r))
      (dist (vs (b + 1 + 0)) (vs (b + 1 + (n - 1)))) = vs (b + 1 + (n - 1)) := by
    rw [hLR, hB]
    show sides b (dist (vs b) (vs (b + 1)) - dist (vs b) (vs (b + 1))) = vs b
    rw [sub_self]
    exact hb0
  have ht' : t ∈ Set.Icc (0 : ℝ)
      (dist (vs (b + 1 + 0)) (vs (b + 1 + (n - 1)))) := by
    rw [hLR]
    exact ht
  obtain ⟨j, hj, s, hs, hd⟩ :=
    exists_close_side_of_chord hδ hδ0 hgeo c (n - 1) hk1 hc
      (fun j => vs (b + 1 + j)) (fun j => sides (b + 1 + j)) hfam
      (fun r => sides b (dist (vs b) (vs (b + 1)) - r)) hrev hrev0 hrev1 t ht'
  refine ⟨j, hj, s, ?_, hd⟩
  have harg : b + 1 + (j + 1) = b + 1 + j + 1 := by omega
  rw [harg] at hs
  exact hs

/-! ### Lemma 25 -/

/-- **Ol'shanskii's Lemma 25**, reconstructed.  In a closed geodesic `n`-gon
read from `b`, split the sides other than `b` into a class `S` and its
complement, and bound the length of each side outside `S` by `w i`, with
`∑ w ≤ ρ`.  If side `b` is longer than `(n-1)(β + 4D) + ρ`, then some side in
`S` carries two points at parameter distance at least `β`, each within `D` of
a point of side `b`, and those two points of side `b` are themselves at least
`β` apart.

`D` is any bound on the dyadic chord constant `3δ(c+1)` for `n - 1 ≤ 2 ^ c`.
The `4D` is the whole cost of the argument: `2D` widens the sampling spacing
so that witnesses on a common side are still `β` apart, and `2D` pays for the
two ends of the shadow that a short side casts on side `b`. -/
theorem exists_long_close_pair {δ D ρ β : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (hgeo : IsGeodesicSpace X)
    {n c b : ℕ} (hn : 2 ≤ n) (hc : n - 1 ≤ 2 ^ c)
    {vs : ℕ → X} {sides : ℕ → ℝ → X}
    (hpoly : IsClosedPolygonAt vs sides b n)
    (hD : 3 * δ * ((c : ℝ) + 1) ≤ D)
    (S : Set ℕ) (w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hshort : ∀ i, b < i → i < b + n → i ∉ S → dist (vs i) (vs (i + 1)) ≤ w i)
    (hρ : ∑ j ∈ Finset.range (n - 1), w (b + 1 + j) ≤ ρ)
    (hβ : 0 < β)
    (hlong : ((n : ℝ) - 1) * (β + 4 * D) + ρ < dist (vs b) (vs (b + 1))) :
    ∃ i, b < i ∧ i < b + n ∧ i ∈ S ∧
      ∃ u ∈ Set.Icc (0 : ℝ) (dist (vs b) (vs (b + 1))),
        ∃ u' ∈ Set.Icc (0 : ℝ) (dist (vs b) (vs (b + 1))),
          ∃ s ∈ Set.Icc (0 : ℝ) (dist (vs i) (vs (i + 1))),
            ∃ s' ∈ Set.Icc (0 : ℝ) (dist (vs i) (vs (i + 1))),
              β ≤ u' - u ∧ β ≤ |s' - s| ∧
                dist (sides b u) (sides i s) ≤ D ∧
                dist (sides b u') (sides i s') ≤ D := by
  have hside := hpoly.1
  have hbn : b < b + n := by omega
  obtain ⟨hb, -, -⟩ := hside b (le_refl b) hbn
  have hLnn : (0 : ℝ) ≤ dist (vs b) (vs (b + 1)) := dist_nonneg
  have hcast0 : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg c
  have hD0 : (0 : ℝ) ≤ 3 * δ * ((c : ℝ) + 1) :=
    mul_nonneg (by linarith) (by linarith)
  have hDnn : (0 : ℝ) ≤ D := le_trans hD0 hD
  have hstep : (0 : ℝ) < β + 2 * D := by linarith
  -- the samples along side `b`, clamped to its length
  obtain ⟨σ, hσ⟩ : ∃ σ : ℕ → ℝ, ∀ k : ℕ,
      σ k = min ((k : ℝ) * (β + 2 * D)) (dist (vs b) (vs (b + 1))) :=
    ⟨fun k => min ((k : ℝ) * (β + 2 * D)) (dist (vs b) (vs (b + 1))),
      fun _ => rfl⟩
  have hσmem : ∀ k, σ k ∈ Set.Icc (0 : ℝ) (dist (vs b) (vs (b + 1))) := by
    intro k
    rw [hσ k]
    refine ⟨?_, min_le_right _ _⟩
    have h1 : (0 : ℝ) ≤ (k : ℝ) * (β + 2 * D) :=
      mul_nonneg (Nat.cast_nonneg k) hstep.le
    exact le_min h1 hLnn
  -- each sample records a side of the complementary arc
  have hall : ∀ k : ℕ, ∃ j, j < n - 1 ∧ ∃ s,
      s ∈ Set.Icc (0 : ℝ) (dist (vs (b + 1 + j)) (vs (b + 1 + j + 1))) ∧
        dist (sides b (dist (vs b) (vs (b + 1)) - σ k)) (sides (b + 1 + j) s)
          ≤ 3 * δ * ((c : ℝ) + 1) := fun k =>
    exists_close_other_side hδ hδ0 hgeo hn hc hpoly (hσmem k)
  choose jf hjf sf hsf hdf using hall
  -- two samples recording the same side are close along it
  have hcore : ∀ k k' : ℕ, jf k = jf k' →
      |σ k - σ k'| ≤ 2 * (3 * δ * ((c : ℝ) + 1)) + |sf k - sf k'| := by
    intro k k' heq
    have h1 : b ≤ b + 1 + jf k := by omega
    have h2 : b + 1 + jf k < b + n := by
      have hjk := hjf k
      omega
    obtain ⟨hgj, -, -⟩ := hside (b + 1 + jf k) h1 h2
    have hsk : sf k ∈ Set.Icc (0 : ℝ)
        (dist (vs (b + 1 + jf k)) (vs (b + 1 + jf k + 1))) := hsf k
    have hsk' : sf k' ∈ Set.Icc (0 : ℝ)
        (dist (vs (b + 1 + jf k)) (vs (b + 1 + jf k + 1))) := by
      rw [heq]
      exact hsf k'
    have hdk : dist (sides b (dist (vs b) (vs (b + 1)) - σ k))
        (sides (b + 1 + jf k) (sf k)) ≤ 3 * δ * ((c : ℝ) + 1) := hdf k
    have hdk' : dist (sides b (dist (vs b) (vs (b + 1)) - σ k'))
        (sides (b + 1 + jf k) (sf k')) ≤ 3 * δ * ((c : ℝ) + 1) := by
      rw [heq]
      exact hdf k'
    have hmk := hσmem k
    have hmk' := hσmem k'
    have hxk : dist (vs b) (vs (b + 1)) - σ k
        ∈ Set.Icc (0 : ℝ) (dist (vs b) (vs (b + 1))) :=
      ⟨by linarith [hmk.2], by linarith [hmk.1]⟩
    have hxk' : dist (vs b) (vs (b + 1)) - σ k'
        ∈ Set.Icc (0 : ℝ) (dist (vs b) (vs (b + 1))) :=
      ⟨by linarith [hmk'.2], by linarith [hmk'.1]⟩
    have hspan : dist (sides b (dist (vs b) (vs (b + 1)) - σ k))
        (sides b (dist (vs b) (vs (b + 1)) - σ k')) = |σ k - σ k'| := by
      rw [hb _ hxk _ hxk']
      have he : dist (vs b) (vs (b + 1)) - σ k
          - (dist (vs b) (vs (b + 1)) - σ k') = -(σ k - σ k') := by ring
      rw [he, abs_neg]
    have hwit : dist (sides (b + 1 + jf k) (sf k))
        (sides (b + 1 + jf k) (sf k')) = |sf k - sf k'| := hgj _ hsk _ hsk'
    have h4 := dist_triangle4 (sides b (dist (vs b) (vs (b + 1)) - σ k))
      (sides (b + 1 + jf k) (sf k)) (sides (b + 1 + jf k) (sf k'))
      (sides b (dist (vs b) (vs (b + 1)) - σ k'))
    have hsym : dist (sides (b + 1 + jf k) (sf k'))
        (sides b (dist (vs b) (vs (b + 1)) - σ k'))
        = dist (sides b (dist (vs b) (vs (b + 1)) - σ k'))
          (sides (b + 1 + jf k) (sf k')) := dist_comm _ _
    rw [hspan, hwit, hsym] at h4
    linarith
  -- how many samples fit along side `b`
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ,
      N = ⌊dist (vs b) (vs (b + 1)) / (β + 2 * D)⌋₊ :=
    ⟨⌊dist (vs b) (vs (b + 1)) / (β + 2 * D)⌋₊, rfl⟩
  have hNle : (N : ℝ) * (β + 2 * D) ≤ dist (vs b) (vs (b + 1)) := by
    rw [hNdef]
    have h1 : ((⌊dist (vs b) (vs (b + 1)) / (β + 2 * D)⌋₊ : ℕ) : ℝ)
        ≤ dist (vs b) (vs (b + 1)) / (β + 2 * D) :=
      Nat.floor_le (div_nonneg hLnn hstep.le)
    exact (le_div_iff₀ hstep).mp h1
  have hNgt : dist (vs b) (vs (b + 1)) < ((N : ℝ) + 1) * (β + 2 * D) := by
    rw [hNdef]
    have h1 : dist (vs b) (vs (b + 1)) / (β + 2 * D)
        < (⌊dist (vs b) (vs (b + 1)) / (β + 2 * D)⌋₊ : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    exact (div_lt_iff₀ hstep).mp h1
  have hσeq : ∀ k : ℕ, k ≤ N → σ k = (k : ℝ) * (β + 2 * D) := by
    intro k hk
    rw [hσ k]
    refine min_eq_left ?_
    have hkc : (k : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hk
    have hmul := mul_le_mul_of_nonneg_right hkc hstep.le
    linarith
  -- the fibres of the recorded index
  obtain ⟨F, hF⟩ : ∃ F : ℕ → Finset ℕ, ∀ j : ℕ,
      F j = (Finset.range (N + 1)).filter (fun k => jf k = j) :=
    ⟨fun j => (Finset.range (N + 1)).filter (fun k => jf k = j), fun _ => rfl⟩
  by_contra hcon
  -- no side of `S` records two samples, or the conclusion would hold
  have hfiberS : ∀ j : ℕ, j < n - 1 → b + 1 + j ∈ S → (F j).card ≤ 1 := by
    intro j hj hjS
    have hwin : ∀ p q : ℕ, p ≤ N → q ≤ N → p < q → jf p = j → jf q = j →
        False := by
      intro p q hpN hqN hpq hjp hjq
      apply hcon
      have hlt1 : b < b + 1 + j := by omega
      have hlt2 : b + 1 + j < b + n := by omega
      have hσp : σ p = (p : ℝ) * (β + 2 * D) := hσeq p hpN
      have hσq : σ q = (q : ℝ) * (β + 2 * D) := hσeq q hqN
      have hpqN : p + 1 ≤ q := by omega
      have hpqR : (p : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast hpqN
      have hgap : β + 2 * D ≤ σ q - σ p := by
        have h1 : ((p : ℝ) + 1) * (β + 2 * D) ≤ (q : ℝ) * (β + 2 * D) :=
          mul_le_mul_of_nonneg_right hpqR hstep.le
        rw [hσp, hσq]
        linarith
      have hnn : (0 : ℝ) ≤ σ q - σ p := by linarith
      have hcc := hcore p q (hjp.trans hjq.symm)
      have habs : |σ p - σ q| = σ q - σ p := by
        rw [abs_sub_comm]
        exact abs_of_nonneg hnn
      rw [habs] at hcc
      have hsfgap : β ≤ |sf p - sf q| := by linarith
      have hmp := hσmem p
      have hmq := hσmem q
      have hup : dist (vs b) (vs (b + 1)) - σ q
          ∈ Set.Icc (0 : ℝ) (dist (vs b) (vs (b + 1))) :=
        ⟨by linarith [hmq.2], by linarith [hmq.1]⟩
      have huq : dist (vs b) (vs (b + 1)) - σ p
          ∈ Set.Icc (0 : ℝ) (dist (vs b) (vs (b + 1))) :=
        ⟨by linarith [hmp.2], by linarith [hmp.1]⟩
      have hsq : sf q ∈ Set.Icc (0 : ℝ)
          (dist (vs (b + 1 + j)) (vs (b + 1 + j + 1))) := by
        have h := hsf q
        rw [hjq] at h
        exact h
      have hsp : sf p ∈ Set.Icc (0 : ℝ)
          (dist (vs (b + 1 + j)) (vs (b + 1 + j + 1))) := by
        have h := hsf p
        rw [hjp] at h
        exact h
      have hdq : dist (sides b (dist (vs b) (vs (b + 1)) - σ q))
          (sides (b + 1 + j) (sf q)) ≤ D := by
        have h := hdf q
        rw [hjq] at h
        linarith
      have hdp : dist (sides b (dist (vs b) (vs (b + 1)) - σ p))
          (sides (b + 1 + j) (sf p)) ≤ D := by
        have h := hdf p
        rw [hjp] at h
        linarith
      have hspangoal : β ≤ dist (vs b) (vs (b + 1)) - σ p
          - (dist (vs b) (vs (b + 1)) - σ q) := by linarith
      exact ⟨b + 1 + j, hlt1, hlt2, hjS,
        dist (vs b) (vs (b + 1)) - σ q, hup,
        dist (vs b) (vs (b + 1)) - σ p, huq,
        sf q, hsq, sf p, hsp, hspangoal, hsfgap, hdq, hdp⟩
    by_contra hc2
    have hc3 : 1 < (F j).card := by omega
    obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp hc3
    rw [hF j] at hp hq
    have hpm := Finset.mem_filter.mp hp
    have hqm := Finset.mem_filter.mp hq
    have hpr := Finset.mem_range.mp hpm.1
    have hqr := Finset.mem_range.mp hqm.1
    have hpN : p ≤ N := by omega
    have hqN : q ≤ N := by omega
    rcases lt_or_gt_of_ne hpq with hlt | hlt
    · exact hwin p q hpN hqN hlt hpm.2 hqm.2
    · exact hwin q p hqN hpN hlt hqm.2 hpm.2
  -- every fibre is short: the `S`-sides by the above, the others by `w`
  have hfiber : ∀ j : ℕ, j < n - 1 →
      ((F j).card : ℝ) * (β + 2 * D)
        ≤ (β + 2 * D) + w (b + 1 + j) + 2 * D := by
    intro j hj
    have hwj := hw (b + 1 + j)
    rcases Classical.em (b + 1 + j ∈ S) with hjS | hjS
    · have h1 := hfiberS j hj hjS
      have h2 : ((F j).card : ℝ) ≤ 1 := by exact_mod_cast h1
      have h3 : ((F j).card : ℝ) * (β + 2 * D) ≤ 1 * (β + 2 * D) :=
        mul_le_mul_of_nonneg_right h2 hstep.le
      linarith
    · have hlt1 : b < b + 1 + j := by omega
      have hlt2 : b + 1 + j < b + n := by omega
      have hshortj : dist (vs (b + 1 + j)) (vs (b + 1 + j + 1))
          ≤ w (b + 1 + j) := hshort (b + 1 + j) hlt1 hlt2 hjS
      rcases Finset.eq_empty_or_nonempty (F j) with he | hne
      · rw [he]
        simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
        linarith
      · have hmemfil : ∀ k, k ∈ F j → k ∈ Finset.range (N + 1) ∧ jf k = j := by
          intro k hk
          rw [hF j] at hk
          exact Finset.mem_filter.mp hk
        have hminmem : (F j).min' hne ∈ F j := Finset.min'_mem _ _
        have hmaxmem : (F j).max' hne ∈ F j := Finset.max'_mem _ _
        have hminle : (F j).min' hne ≤ (F j).max' hne :=
          Finset.min'_le (F j) _ hmaxmem
        have hsub : F j ⊆ Finset.Icc ((F j).min' hne) ((F j).max' hne) := by
          intro k hk
          rw [Finset.mem_Icc]
          exact ⟨Finset.min'_le (F j) k hk, Finset.le_max' (F j) k hk⟩
        have hcard : (F j).card ≤ (F j).max' hne + 1 - (F j).min' hne := by
          have h1 := Finset.card_le_card hsub
          rwa [Nat.card_Icc] at h1
        have hminfil := hmemfil _ hminmem
        have hmaxfil := hmemfil _ hmaxmem
        have hminr := Finset.mem_range.mp hminfil.1
        have hmaxr := Finset.mem_range.mp hmaxfil.1
        have hminN : (F j).min' hne ≤ N := by omega
        have hmaxN : (F j).max' hne ≤ N := by omega
        have hjmin : jf ((F j).min' hne) = j := hminfil.2
        have hjmax : jf ((F j).max' hne) = j := hmaxfil.2
        have hσmin := hσeq _ hminN
        have hσmax := hσeq _ hmaxN
        have h1 : sf ((F j).min' hne) ∈ Set.Icc (0 : ℝ)
            (dist (vs (b + 1 + j)) (vs (b + 1 + j + 1))) := by
          have h := hsf ((F j).min' hne)
          rw [hjmin] at h
          exact h
        have h2 : sf ((F j).max' hne) ∈ Set.Icc (0 : ℝ)
            (dist (vs (b + 1 + j)) (vs (b + 1 + j + 1))) := by
          have h := hsf ((F j).max' hne)
          rw [hjmax] at h
          exact h
        have hsfle : |sf ((F j).min' hne) - sf ((F j).max' hne)|
            ≤ dist (vs (b + 1 + j)) (vs (b + 1 + j + 1)) := by
          refine abs_le.mpr ⟨?_, ?_⟩
          · linarith [h1.1, h1.2, h2.1, h2.2]
          · linarith [h1.1, h1.2, h2.1, h2.2]
        have hcc := hcore ((F j).min' hne) ((F j).max' hne)
          (hjmin.trans hjmax.symm)
        have hcastle : (((F j).min' hne : ℕ) : ℝ)
            ≤ (((F j).max' hne : ℕ) : ℝ) := Nat.cast_le.mpr hminle
        have hmulle : (((F j).min' hne : ℕ) : ℝ) * (β + 2 * D)
            ≤ (((F j).max' hne : ℕ) : ℝ) * (β + 2 * D) :=
          mul_le_mul_of_nonneg_right hcastle hstep.le
        have habs : |σ ((F j).min' hne) - σ ((F j).max' hne)|
            = σ ((F j).max' hne) - σ ((F j).min' hne) := by
          rw [abs_sub_comm]
          refine abs_of_nonneg ?_
          rw [hσmin, hσmax]
          linarith
        rw [habs, hσmin, hσmax] at hcc
        have hle1 : (F j).min' hne ≤ (F j).max' hne + 1 := by omega
        have hcast : (((F j).max' hne + 1 - (F j).min' hne : ℕ) : ℝ)
            = (((F j).max' hne : ℕ) : ℝ) + 1
              - (((F j).min' hne : ℕ) : ℝ) := by
          rw [Nat.cast_sub hle1, Nat.cast_add, Nat.cast_one]
        have hcard1 : ((F j).card : ℝ)
            ≤ (((F j).max' hne + 1 - (F j).min' hne : ℕ) : ℝ) :=
          Nat.cast_le.mpr hcard
        rw [hcast] at hcard1
        have hmul : ((F j).card : ℝ) * (β + 2 * D)
            ≤ ((((F j).max' hne : ℕ) : ℝ) + 1
              - (((F j).min' hne : ℕ) : ℝ)) * (β + 2 * D) :=
          mul_le_mul_of_nonneg_right hcard1 hstep.le
        linarith
  -- the fibrewise count
  have hcount : N + 1 = ∑ j ∈ Finset.range (n - 1), (F j).card := by
    have hmaps : ∀ k ∈ Finset.range (N + 1), jf k ∈ Finset.range (n - 1) := by
      intro k _
      exact Finset.mem_range.mpr (hjf k)
    have h1 := Finset.card_eq_sum_card_fiberwise hmaps
    rw [Finset.card_range] at h1
    rw [h1]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [hF j]
  have hNR : (N : ℝ) + 1
      = ∑ j ∈ Finset.range (n - 1), (((F j).card : ℕ) : ℝ) := by
    have h2 : ((N + 1 : ℕ) : ℝ)
        = ((∑ j ∈ Finset.range (n - 1), (F j).card : ℕ) : ℝ) := by
      rw [hcount]
    push_cast at h2
    exact h2
  have h1n : 1 ≤ n := by omega
  have hcastn : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub h1n, Nat.cast_one]
  have hsum : ((N : ℝ) + 1) * (β + 2 * D)
      ≤ ((n : ℝ) - 1) * (β + 4 * D) + ρ := by
    calc ((N : ℝ) + 1) * (β + 2 * D)
        = (∑ j ∈ Finset.range (n - 1), (((F j).card : ℕ) : ℝ))
            * (β + 2 * D) := by rw [hNR]
      _ = ∑ j ∈ Finset.range (n - 1), (((F j).card : ℕ) : ℝ) * (β + 2 * D) := by
          rw [Finset.sum_mul]
      _ ≤ ∑ j ∈ Finset.range (n - 1), ((β + 4 * D) + w (b + 1 + j)) := by
          refine Finset.sum_le_sum ?_
          intro j hj
          have hfj := hfiber j (Finset.mem_range.mp hj)
          linarith
      _ = (∑ _j ∈ Finset.range (n - 1), (β + 4 * D))
            + ∑ j ∈ Finset.range (n - 1), w (b + 1 + j) := Finset.sum_add_distrib
      _ = ((n : ℝ) - 1) * (β + 4 * D)
            + ∑ j ∈ Finset.range (n - 1), w (b + 1 + j) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hcastn]
      _ ≤ ((n : ℝ) - 1) * (β + 4 * D) + ρ := by linarith
  linarith

/-- **Ol'shanskii's Lemma 25 in its printed shape.**  The sides other than
`b` are split into a class `S` and a complement of total length at most `ρ`;
side `b` has length at least `θ`; and `θ` exceeds both `ξ n` and `10³ ρ`,
where `ξ` is at least `3·10⁴` times the dyadic chord constant.  Then some
other side of `S` runs alongside side `b` for a stretch of length `ξ/1000` on
each, at distance `ξ/(3·10⁴)` between the corresponding ends.

The printed hypothesis is `ξ ≥ 3·10⁴ δ`; the reconstruction needs
`ξ ≥ 3·10⁴ δ (Nat.clog 2 (n-1)+1)`, and everything else is unchanged.
The dyadic exponent is fixed here rather than exposed as caller-supplied data:
this is the strongest conclusion furnished by the direct chord proof and it
prevents consumers from silently reinstating the unsupported absolute
constant.  The module docstring records why the logarithm cannot be removed
by the recursion the printed proof runs. -/
theorem exists_long_close_pair_of_short_complement {δ ρ θ ξ : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (hgeo : IsGeodesicSpace X)
    {n b : ℕ} (hn : 2 ≤ n)
    {vs : ℕ → X} {sides : ℕ → ℝ → X}
    (hpoly : IsClosedPolygonAt vs sides b n)
    (S : Set ℕ) (w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hshort : ∀ i, b < i → i < b + n → i ∉ S → dist (vs i) (vs (i + 1)) ≤ w i)
    (hρ : ∑ j ∈ Finset.range (n - 1), w (b + 1 + j) ≤ ρ)
    (hξ0 : 0 < ξ)
    (hξ : 30000 * (3 * δ * ((Nat.clog 2 (n - 1) : ℝ) + 1)) ≤ ξ)
    (hθn : (n : ℝ) * ξ < θ) (hθρ : 1000 * ρ < θ)
    (hθb : θ ≤ dist (vs b) (vs (b + 1))) :
    ∃ i, b < i ∧ i < b + n ∧ i ∈ S ∧
      ∃ u ∈ Set.Icc (0 : ℝ) (dist (vs b) (vs (b + 1))),
        ∃ u' ∈ Set.Icc (0 : ℝ) (dist (vs b) (vs (b + 1))),
          ∃ s ∈ Set.Icc (0 : ℝ) (dist (vs i) (vs (i + 1))),
            ∃ s' ∈ Set.Icc (0 : ℝ) (dist (vs i) (vs (i + 1))),
              ξ / 1000 ≤ u' - u ∧ ξ / 1000 ≤ |s' - s| ∧
                dist (sides b u) (sides i s) ≤ ξ / 30000 ∧
                dist (sides b u') (sides i s') ≤ ξ / 30000 := by
  let c := Nat.clog 2 (n - 1)
  have hc : n - 1 ≤ 2 ^ c := Nat.le_pow_clog (by norm_num) (n - 1)
  have hD : 3 * δ * ((c : ℝ) + 1) ≤ ξ / 30000 := by
    dsimp [c]
    linarith
  have hβ : (0 : ℝ) < ξ / 1000 := by linarith
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hθ0 : 0 < θ := lt_trans (mul_pos hnpos hξ0) hθn
  have hlong : ((n : ℝ) - 1) * (ξ / 1000 + 4 * (ξ / 30000)) + ρ
      < dist (vs b) (vs (b + 1)) := by
    have hexp : ((n : ℝ) - 1) * (ξ / 1000 + 4 * (ξ / 30000))
        = ((n : ℝ) * ξ) * (17 / 15000) - ξ * (17 / 15000) := by ring
    rw [hexp]
    linarith
  exact exists_long_close_pair hδ hδ0 hgeo hn hc hpoly hD S w hw hshort hρ hβ
    hlong

end Olshanskii
end GroupApproximation
