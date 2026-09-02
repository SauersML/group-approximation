import GroupApproximation.GGT.DGOTheorem442NearMinimalBase

/-!
# Endpoint projections of near-minimal double-coset representatives

DGO section 4.5 bounds the projection of a chosen edge representative to
either endpoint orbit.  This file proves the identity-endpoint estimate.
If a projection point were far from the basepoint, quasiconvexity supplies a
nearby orbit point on the geodesic to it.  Thinness puts that point near one
of the other two sides.  One side contradicts approximate projection, and
the other produces a shorter representative in the same double coset.

With the repository's `3 * delta` thin-triangle constant, the resulting bound
is `2 * sigma + 15 * delta`.
-/

namespace GroupApproximation
namespace GGT
namespace Elementary

open GroupApproximation.HullGeometry
open CosetGraph

universe u v

variable {G : Type u} [Group G] {S : Type v} [PseudoMetricSpace S]
  [MulAction G S]

/-- The projection to the identity endpoint of a near-minimal double-coset
representative lies uniformly near the basepoint.  This is the endpoint case
of estimate (46) in DGO section 4.5. -/
theorem dist_approxProjection_nearMinimal_le
    {delta sigma : ℝ} (hdelta : IsHyperbolicSpace delta S)
    (hdelta0 : 0 ≤ delta) (hdeltapos : 0 < delta)
    (hgeo : IsGeodesicSpace S) (hiso : IsIsometricAction G S)
    {H : Subgroup G} {s : S}
    (hquasi : ∀ (p q : G), p ∈ H → q ∈ H →
      ∀ f : ℝ → S, IsGeodesicSegment f 0 (dist (p • s) (q • s)) →
        f 0 = p • s → f (dist (p • s) (q • s)) = q • s →
          ∀ t ∈ Set.Icc (0 : ℝ) (dist (p • s) (q • s)),
            ∃ c : G, c ∈ H ∧ dist (f t) (c • s) ≤ sigma)
    (hsigma0 : 0 ≤ sigma) {g : G}
    (hnear : IsDoubleCosetNearMinimal H s delta g)
    {q : S}
    (hq : IsApproxProjectionTo (subgroupOrbitAt H s) (g • s) q delta) :
    dist s q ≤ 2 * sigma + 15 * delta := by
  by_contra hnot
  have hfar : 2 * sigma + 15 * delta < dist s q := lt_of_not_ge hnot
  obtain ⟨h, hhH, hqEq⟩ := hq.1
  obtain ⟨fsq, hfsq, hfsq0, hfsq1⟩ := hgeo s q
  obtain ⟨fsg, hfsg, hfsg0, hfsg1⟩ := hgeo s (g • s)
  obtain ⟨fqg, hfqg, hfqg0, hfqg1⟩ := hgeo q (g • s)
  let t : ℝ := dist s q - (sigma + 8 * delta)
  have ht : t ∈ Set.Icc (0 : ℝ) (dist s q) := by
    constructor
    · dsimp only [t]
      linarith
    · dsimp only [t]
      linarith
  have hsu : dist s (fsq t) = t := by
    calc
      dist s (fsq t) = dist (fsq 0) (fsq t) := by rw [hfsq0]
      _ = |(0 : ℝ) - t| := hfsq.dist_eq ⟨le_rfl, dist_nonneg⟩ ht
      _ = t := by rw [abs_of_nonpos (by linarith [ht.1])]; ring
  have huq : dist (fsq t) q = sigma + 8 * delta := by
    calc
      dist (fsq t) q = dist (fsq t) (fsq (dist s q)) := by rw [hfsq1]
      _ = |t - dist s q| := hfsq.dist_eq ht ⟨dist_nonneg, le_rfl⟩
      _ = sigma + 8 * delta := by
        rw [abs_of_nonpos (by dsimp only [t]; linarith)]
        dsimp only [t]
        ring
  have hfsq' : IsGeodesicSegment fsq 0
      (dist ((1 : G) • s) (h • s)) := by
    simpa only [one_smul, hqEq] using hfsq
  obtain ⟨c, hcH, huc⟩ := hquasi 1 h H.one_mem hhH fsq hfsq'
    (by simpa only [one_smul] using hfsq0)
    (by simpa only [one_smul, hqEq] using hfsq1) t
    (by simpa only [one_smul, hqEq] using ht)
  have hcOrbit : c • s ∈ subgroupOrbitAt H s := ⟨c, hcH, rfl⟩
  have hproj := hq.2 (c • s) hcOrbit
  have hthin := geodesicTriangle_thin_const hdelta hdelta0 s q (g • s)
    (dist s q) (dist s (g • s)) (dist q (g • s)) fsq fsg fqg
    dist_nonneg dist_nonneg dist_nonneg
    hfsq hfsq0 hfsq1 hfsg hfsg0 hfsg1 hfqg hfqg0 hfqg1 ht
  rcases hthin with ⟨r, hr, hur⟩ | ⟨r, hr, hur⟩
  · have hsr : dist s (fsg r) = r := by
      calc
        dist s (fsg r) = dist (fsg 0) (fsg r) := by rw [hfsg0]
        _ = |(0 : ℝ) - r| := hfsg.dist_eq ⟨le_rfl, dist_nonneg⟩ hr
        _ = r := by rw [abs_of_nonpos (by linarith [hr.1])]; ring
    have hrg : dist (fsg r) (g • s) = dist s (g • s) - r := by
      calc
        dist (fsg r) (g • s) =
            dist (fsg r) (fsg (dist s (g • s))) := by rw [hfsg1]
        _ = |r - dist s (g • s)| :=
          hfsg.dist_eq hr ⟨dist_nonneg, le_rfl⟩
        _ = dist s (g • s) - r := by
          rw [abs_of_nonpos (by linarith [hr.2])]
          ring
    have hrLower : t - 3 * delta ≤ r := by
      have htri := dist_triangle s (fsg r) (fsq t)
      rw [hsr, dist_comm (fsg r) (fsq t)] at htri
      linarith
    have hcg : dist (c • s) (g • s) ≤
        sigma + 3 * delta + (dist s (g • s) - r) := by
      have htri := dist_triangle4 (c • s) (fsq t) (fsg r) (g • s)
      have hucRev : dist (c • s) (fsq t) ≤ sigma := by rwa [dist_comm]
      rw [hrg] at htri
      linarith
    have hcandDist : dist s ((c⁻¹ * g * 1) • s) =
        dist (c • s) (g • s) := by
      calc
        dist s ((c⁻¹ * g * 1) • s) =
            dist (c • s) (c • ((c⁻¹ * g * 1) • s)) :=
          (hiso c s ((c⁻¹ * g * 1) • s)).symm
        _ = dist (c • s) (g • s) := by
          simp only [← mul_smul]
          congr 2
          group
    have hminimal := hnear c⁻¹ (H.inv_mem hcH) 1 H.one_mem
    rw [hcandDist] at hminimal
    dsimp only [t] at hrLower
    linarith
  · have hqr : dist q (fqg r) = r := by
      calc
        dist q (fqg r) = dist (fqg 0) (fqg r) := by rw [hfqg0]
        _ = |(0 : ℝ) - r| := hfqg.dist_eq ⟨le_rfl, dist_nonneg⟩ hr
        _ = r := by rw [abs_of_nonpos (by linarith [hr.1])]; ring
    have hrg : dist (fqg r) (g • s) = dist q (g • s) - r := by
      calc
        dist (fqg r) (g • s) =
            dist (fqg r) (fqg (dist q (g • s))) := by rw [hfqg1]
        _ = |r - dist q (g • s)| :=
          hfqg.dist_eq hr ⟨dist_nonneg, le_rfl⟩
        _ = dist q (g • s) - r := by
          rw [abs_of_nonpos (by linarith [hr.2])]
          ring
    have hrLower : sigma + 5 * delta ≤ r := by
      have htri := dist_triangle (fsq t) (fqg r) q
      rw [huq, dist_comm (fqg r) q, hqr] at htri
      linarith
    have hgc : dist (g • s) (c • s) ≤
        (dist q (g • s) - r) + 3 * delta + sigma := by
      have htri := dist_triangle4 (g • s) (fqg r) (fsq t) (c • s)
      rw [dist_comm (g • s) (fqg r), hrg,
        dist_comm (fqg r) (fsq t)] at htri
      linarith
    rw [dist_comm (g • s) q] at hproj
    linarith

end Elementary
end GGT
end GroupApproximation
