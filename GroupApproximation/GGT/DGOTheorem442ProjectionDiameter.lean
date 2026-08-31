import GroupApproximation.GGT.ElementaryProjectionCriterion
import GroupApproximation.GGT.HyperbolicThinTriangles

/-!
# DGO Theorem 4.42: bounded diameter of approximate orbit projections

This is the single-subgroup form of DGO Lemma 4.44.  The source uses
`δ`-approximate nearest-point projections to a quasiconvex orbit.  Our
four-point-to-thin-triangle bridge has constant `3δ`, so the bound obtained
here is `14δ + 2σ` rather than the source's `6δ + 2σ`; no downstream argument
uses the sharper number.

The proof is the printed one in a form suited to the existing API.  Take the
midpoint of a geodesic between two approximate projections.  Quasiconvexity
places a subgroup-orbit point near it, while triangle thinness places it near
one of the two sides from the external point.  If the midpoint were far from
the corresponding endpoint, that orbit point would be closer than an
approximate projection, a contradiction.
-/

namespace GroupApproximation
namespace GGT
namespace Elementary

open GroupApproximation.HullGeometry

universe u v

variable {G : Type u} [Group G] {S : Type v} [PseudoMetricSpace S]
  [MulAction G S]

/-- The orbit of `s` under a subgroup, as a point set. -/
def subgroupOrbitAt (H : Subgroup G) (s : S) : Set S :=
  {x | ∃ h : G, h ∈ H ∧ h • s = x}

omit [PseudoMetricSpace S] in
@[simp] theorem mem_subgroupOrbitAt_iff (H : Subgroup G) (s x : S) :
    x ∈ subgroupOrbitAt H s ↔ ∃ h : G, h ∈ H ∧ h • s = x :=
  Iff.rfl

/-- A `δ`-approximate nearest point in the subgroup orbit.  This is equation
(43) in DGO, with the infimum-free universal inequality that its proof uses. -/
def IsApproxOrbitProjectionAt (H : Subgroup G) (s a x : S) (δ : ℝ) : Prop :=
  x ∈ subgroupOrbitAt H s ∧
    ∀ z ∈ subgroupOrbitAt H s, dist a x ≤ dist a z + δ

/-- **DGO Lemma 4.44, with the repository's `3δ` thin-triangle constant.**

Two `δ`-approximate projections of one point to a `σ`-quasiconvex subgroup
orbit are at distance at most `14δ + 2σ`. -/
theorem dist_approxOrbitProjection_le
    {δ σ : ℝ} (hδ : IsHyperbolicSpace δ S) (hδ0 : 0 ≤ δ)
    (hgeo : IsGeodesicSpace S)
    {H : Subgroup G} {s a x y : S}
    (hquasi : ∀ (p q : G), p ∈ H → q ∈ H →
      ∀ f : ℝ → S, IsGeodesicSegment f 0 (dist (p • s) (q • s)) →
        f 0 = p • s → f (dist (p • s) (q • s)) = q • s →
          ∀ t ∈ Set.Icc (0 : ℝ) (dist (p • s) (q • s)),
            ∃ c : G, c ∈ H ∧ dist (f t) (c • s) ≤ σ)
    (hx : IsApproxOrbitProjectionAt H s a x δ)
    (hy : IsApproxOrbitProjectionAt H s a y δ) :
    dist x y ≤ 14 * δ + 2 * σ := by
  obtain ⟨px, hpxH, hpx⟩ := hx.1
  obtain ⟨py, hpyH, hpy⟩ := hy.1
  obtain ⟨fxy, hfxy, hfxy0, hfxy1⟩ := hgeo x y
  obtain ⟨fxa, hfxa, hfxa0, hfxa1⟩ := hgeo x a
  obtain ⟨fya, hfya, hfya0, hfya1⟩ := hgeo y a
  let t : ℝ := dist x y / 2
  have ht : t ∈ Set.Icc (0 : ℝ) (dist x y) := by
    constructor
    · dsimp [t]
      positivity
    · dsimp [t]
      linarith [dist_nonneg (x := x) (y := y)]
  have hztx : dist (fxy t) x = t := by
    rw [dist_comm]
    calc
      dist x (fxy t) = dist (fxy 0) (fxy t) := by rw [hfxy0]
      _ = |(0 : ℝ) - t| := hfxy.dist_eq ⟨le_rfl, dist_nonneg⟩ ht
      _ = t := by rw [abs_of_nonpos (by linarith [ht.1])]; ring
  have hzty : dist (fxy t) y = t := by
    calc
      dist (fxy t) y = dist (fxy t) (fxy (dist x y)) := by rw [hfxy1]
      _ = |t - dist x y| := hfxy.dist_eq ht ⟨dist_nonneg, le_rfl⟩
      _ = t := by
        rw [abs_of_nonpos (by linarith [ht.2])]
        dsimp [t]
        ring
  have hfxy' : IsGeodesicSegment fxy 0 (dist (px • s) (py • s)) := by
    simpa only [hpx, hpy] using hfxy
  obtain ⟨c, hcH, hzc⟩ := hquasi px py hpxH hpyH fxy hfxy'
    (by simpa [hpx] using hfxy0) (by simpa [hpx, hpy] using hfxy1) t
    (by simpa [hpx, hpy] using ht)
  have hcOrbit : c • s ∈ subgroupOrbitAt H s := ⟨c, hcH, rfl⟩
  have hxNear := hx.2 (c • s) hcOrbit
  have hyNear := hy.2 (c • s) hcOrbit
  have hthin := geodesicTriangle_thin_const hδ hδ0 x y a
    (dist x y) (dist x a) (dist y a) fxy fxa fya
    dist_nonneg dist_nonneg dist_nonneg
    hfxy hfxy0 hfxy1 hfxa hfxa0 hfxa1 hfya hfya0 hfya1 ht
  rcases hthin with ⟨r, hr, hzr⟩ | ⟨r, hr, hzr⟩
  · have hxr : dist x (fxa r) = r := by
      calc
        dist x (fxa r) = dist (fxa 0) (fxa r) := by rw [hfxa0]
        _ = |(0 : ℝ) - r| := hfxa.dist_eq ⟨le_rfl, dist_nonneg⟩ hr
        _ = r := by rw [abs_of_nonpos (by linarith [hr.1])]; ring
    have hra : dist (fxa r) a = dist x a - r := by
      calc
        dist (fxa r) a = dist (fxa r) (fxa (dist x a)) := by rw [hfxa1]
        _ = |r - dist x a| := hfxa.dist_eq hr ⟨dist_nonneg, le_rfl⟩
        _ = dist x a - r := by
          rw [abs_of_nonpos (by linarith [hr.2])]
          ring
    have hac : dist a (c • s) ≤ dist a (fxa r) + dist (fxa r) (fxy t) +
        dist (fxy t) (c • s) := dist_triangle4 _ _ _ _
    have hmid : t ≤ 7 * δ + σ := by
      have hzx := dist_triangle (fxy t) (fxa r) x
      rw [dist_comm a x] at hxNear
      rw [dist_comm a (fxa r), hra, dist_comm (fxa r) (fxy t)] at hac
      rw [hztx, dist_comm (fxa r) x, hxr] at hzx
      linarith
    dsimp [t] at hmid
    linarith
  · have hyr : dist y (fya r) = r := by
      calc
        dist y (fya r) = dist (fya 0) (fya r) := by rw [hfya0]
        _ = |(0 : ℝ) - r| := hfya.dist_eq ⟨le_rfl, dist_nonneg⟩ hr
        _ = r := by rw [abs_of_nonpos (by linarith [hr.1])]; ring
    have hra : dist (fya r) a = dist y a - r := by
      calc
        dist (fya r) a = dist (fya r) (fya (dist y a)) := by rw [hfya1]
        _ = |r - dist y a| := hfya.dist_eq hr ⟨dist_nonneg, le_rfl⟩
        _ = dist y a - r := by
          rw [abs_of_nonpos (by linarith [hr.2])]
          ring
    have hac : dist a (c • s) ≤ dist a (fya r) + dist (fya r) (fxy t) +
        dist (fxy t) (c • s) := dist_triangle4 _ _ _ _
    have hmid : t ≤ 7 * δ + σ := by
      have hzy := dist_triangle (fxy t) (fya r) y
      rw [dist_comm a y] at hyNear
      rw [dist_comm a (fya r), hra, dist_comm (fya r) (fxy t)] at hac
      rw [hzty, dist_comm (fya r) y, hyr] at hzy
      linarith
    dsimp [t] at hmid
    linarith

/-- DGO's orbit-quasiconvexity predicate supplies one uniform projection
diameter constant. -/
theorem exists_approxOrbitProjection_diameter_bound
    {δ : ℝ} (hδ : IsHyperbolicSpace δ S) (hδ0 : 0 ≤ δ)
    (hgeo : IsGeodesicSpace S) {H : Subgroup G} {s : S}
    (hqc : IsQuasiconvexOrbitAt H s) :
    ∃ ν : ℝ, 0 ≤ ν ∧ ∀ (a x y : S),
      IsApproxOrbitProjectionAt H s a x δ →
      IsApproxOrbitProjectionAt H s a y δ → dist x y ≤ ν := by
  obtain ⟨σ, hσ0, hquasi⟩ := hqc
  refine ⟨14 * δ + 2 * σ, by positivity, ?_⟩
  intro a x y hx hy
  exact dist_approxOrbitProjection_le hδ hδ0 hgeo hquasi hx hy

end Elementary
end GGT
end GroupApproximation
