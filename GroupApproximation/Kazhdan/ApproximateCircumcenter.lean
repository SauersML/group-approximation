import GroupApproximation.Kazhdan.HilbertCircumcenter

/-!
# Approximate circumcenters of almost-invariant sets

The Guichardet direction of the fixed-point argument, quantitatively and
without completeness: a near-optimal covering point of a bounded set is
moved very little by any isometry that almost maps a slightly larger set
onto the set, provided the Chebyshev radii of the two sets nearly agree.

Combined with the elementary pigeonhole for monotone bounded radius
sequences, this extracts approximate coboundary primitives from bounded
almost-cocycles ball by ball: choose a window where the Chebyshev radius
of the truncated orbit stabilizes, take any near-optimal covering point,
and every generator displaces it quadratically little.  No Chebyshev
center is ever constructed, so no completeness or uniqueness enters.
-/

namespace GroupApproximation
namespace ApproximateCircumcenter

open Circumcenter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
/-- Covering radii are monotone in the covered set. -/
theorem coveringRadius_mono {S T : Set E} (hS : S.Nonempty)
    (hT : Bornology.IsBounded T) (hST : S ⊆ T) (x : E) :
    coveringRadius S x ≤ coveringRadius T x :=
  coveringRadius_le hS fun _ hs ↦ dist_le_coveringRadius hT x (hST hs)

omit [InnerProductSpace ℝ E] in
/-- The Chebyshev radius of a nonempty bounded set is nonnegative. -/
theorem chebyshevRadius_nonneg {S : Set E} (hne : S.Nonempty)
    (hbdd : Bornology.IsBounded S) : 0 ≤ chebyshevRadius S :=
  le_ciInf fun x ↦ coveringRadius_nonneg hne hbdd x

/-- **Separation of near-optimal covering points.**  Any two points cover
a set no better than its Chebyshev radius allows, so their distance is
controlled by their covering defects.  This is the parallelogram estimate
of `coveringRadius_midpoint_sq` in the form used to compare a point with
its isometric translate. -/
theorem dist_sq_le_of_coveringRadius {S : Set E} (hne : S.Nonempty)
    (hbdd : Bornology.IsBounded S) (y z : E) :
    dist y z ^ 2 ≤ 2 * coveringRadius S y ^ 2 +
      2 * coveringRadius S z ^ 2 - 4 * chebyshevRadius S ^ 2 := by
  have hmid := coveringRadius_midpoint_sq hne hbdd y z
  have hmin : chebyshevRadius S ≤ coveringRadius S (midpoint ℝ y z) :=
    chebyshevRadius_le hne hbdd _
  have hρ0 : 0 ≤ chebyshevRadius S := chebyshevRadius_nonneg hne hbdd
  have hsq : chebyshevRadius S ^ 2 ≤
      coveringRadius S (midpoint ℝ y z) ^ 2 := by
    nlinarith [hmin, hρ0]
  linarith [hmid, hsq]

/-- **Displacement of a near-optimal covering point under an
almost-equivariant isometry.**  Let `Ssmall ⊆ Sbig` be nonempty bounded
sets, let `f` be an isometry mapping `Sbig` approximately onto `Ssmall`
(every point of `Ssmall` is within `ε` of the `f`-image of `Sbig`), and
let `z` cover `Sbig` within `R₀`.  Then the displacement of `z` under `f`
satisfies

`dist z (f z) ^ 2 ≤ 2 R₀ ^ 2 + 2 (R₀ + ε) ^ 2 − 4 (chebyshevRadius Ssmall) ^ 2`,

which is quadratically small once the Chebyshev radii of `Ssmall` and
`Sbig` nearly agree and `z` is near-optimal for `Sbig`. -/
theorem dist_map_sq_le {Ssmall Sbig : Set E} (hne : Ssmall.Nonempty)
    (hbddS : Bornology.IsBounded Ssmall)
    (hbddB : Bornology.IsBounded Sbig) (hsub : Ssmall ⊆ Sbig)
    {f : E → E} (hf : ∀ a b : E, dist (f a) (f b) = dist a b)
    {ε : ℝ}
    (hcover : ∀ t ∈ Ssmall, ∃ u ∈ Sbig, dist t (f u) ≤ ε)
    {z : E} {R₀ : ℝ} (hz : coveringRadius Sbig z ≤ R₀) :
    dist z (f z) ^ 2 ≤ 2 * R₀ ^ 2 + 2 * (R₀ + ε) ^ 2 -
      4 * chebyshevRadius Ssmall ^ 2 := by
  have hzsmall : coveringRadius Ssmall z ≤ R₀ :=
    (coveringRadius_mono hne hbddB hsub z).trans hz
  have hfz : coveringRadius Ssmall (f z) ≤ R₀ + ε := by
    refine coveringRadius_le hne fun t ht ↦ ?_
    obtain ⟨u, hu, hut⟩ := hcover t ht
    have hzu : dist z u ≤ coveringRadius Sbig z :=
      dist_le_coveringRadius hbddB z hu
    calc
      dist (f z) t ≤ dist (f z) (f u) + dist (f u) t := dist_triangle _ _ _
      _ = dist z u + dist t (f u) := by rw [hf, dist_comm (f u) t]
      _ ≤ R₀ + ε := by linarith
  have hbase := dist_sq_le_of_coveringRadius hne hbddS z (f z)
  have hznn : 0 ≤ coveringRadius Ssmall z :=
    coveringRadius_nonneg hne hbddS z
  have hfznn : 0 ≤ coveringRadius Ssmall (f z) :=
    coveringRadius_nonneg hne hbddS (f z)
  have h1 : coveringRadius Ssmall z ^ 2 ≤ R₀ ^ 2 := by
    nlinarith [hzsmall, hznn]
  have h2 : coveringRadius Ssmall (f z) ^ 2 ≤ (R₀ + ε) ^ 2 := by
    nlinarith [hfz, hfznn]
  linarith [hbase, h1, h2]

/-- **Radius pigeonhole.**  A monotone bounded sequence admits, for every
window length and tolerance, a window over which it grows by at most the
tolerance. -/
theorem exists_stable_window (ρ : ℕ → ℝ) {R : ℝ}
    (hR : ∀ n, ρ n ≤ R) (m : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : ℕ, ρ (r + m) ≤ ρ r + δ := by
  by_contra hall
  push Not at hall
  have hstep : ∀ j : ℕ, ρ 0 + j * δ < ρ (j * m) + δ := by
    intro j
    induction j with
    | zero =>
        rw [zero_mul]
        push_cast
        linarith
    | succ i ih =>
        have hi := hall (i * m)
        have hmul : (i + 1) * m = i * m + m := by ring
        rw [hmul]
        push_cast
        linarith
  obtain ⟨j, hj⟩ := exists_nat_gt ((R - ρ 0) / δ)
  have hjδ : R - ρ 0 < j * δ := by
    rw [div_lt_iff₀ hδ] at hj
    exact hj
  have hlast := hstep (j + 1)
  have hbound := hR ((j + 1) * m)
  push_cast at hlast
  linarith

end ApproximateCircumcenter
end GroupApproximation
