import GroupApproximation.GGT.DGOQuadrilateralLongSide
import GroupApproximation.GGT.DGOTheorem442CosetProjections

/-!
# DGO Lemma 4.46: projections between distinct coset orbits are bounded

This is the single-subgroup coset form used in DGO's proof of Theorem 4.42.
The proof follows the printed quadrilateral argument.  A long segment between
two projections shadows one other side of the quadrilateral.  Approximate
minimality excludes the two transverse sides, while quasiconvexity and
geometric separation exclude the side in the source coset orbit.
-/

namespace GroupApproximation
namespace GGT
namespace Elementary

open GroupApproximation.HullGeometry
open GroupApproximation.DGOWindmill

universe u v

variable {G : Type u} [Group G] {S : Type v} [PseudoMetricSpace S]
  [MulAction G S]

/-- **DGO Lemma 4.46, single-subgroup coset form.**  Approximate projections
of arbitrary points of one left-coset orbit to a distinct left-coset orbit
have uniformly bounded diameter. -/
theorem exists_dist_approxProjection_between_distinct_leftCosets_bound
    {δ : ℝ} (hδ : IsHyperbolicSpace δ S) (hδ0 : 0 ≤ δ)
    (hgeo : IsGeodesicSpace S) (hiso : IsIsometricAction G S)
    {H : Subgroup G} {s : S} (hqc : IsQuasiconvexOrbitAt H s)
    (hsep : GeometricallySeparatedAt H s) :
    ∃ ν : ℝ, 0 ≤ ν ∧ ∀ (f g : G), f⁻¹ * g ∉ H →
      ∀ (a₁ a₂ b₁ b₂ : S),
        a₁ ∈ leftCosetOrbitAt H f s →
        a₂ ∈ leftCosetOrbitAt H f s →
        IsApproxProjectionTo (leftCosetOrbitAt H g s) a₁ b₁ δ →
        IsApproxProjectionTo (leftCosetOrbitAt H g s) a₂ b₂ δ →
        dist b₁ b₂ ≤ ν := by
  obtain ⟨σ, hσ0, hquasi⟩ := hqc
  let ε : ℝ := 6 * δ + 2 * σ + 1
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨R, hR0, hforce⟩ := hsep ε hε
  let β : ℝ := R + 2 * σ + 8 * δ + 1
  have hβ : 0 < β := by dsimp [β]; positivity
  let ν : ℝ := 3 * (β + 12 * δ)
  refine ⟨ν, by dsimp [ν]; positivity, ?_⟩
  intro f g hfg a₁ a₂ b₁ b₂ ha₁ ha₂ hb₁ hb₂
  by_contra hn
  have hlong : ν < dist b₁ b₂ := lt_of_not_ge hn
  obtain ⟨fBB, hBB, hBB0, hBB1⟩ := hgeo b₁ b₂
  obtain ⟨fB₁A₁, hB₁A₁, hB₁A₁0, hB₁A₁1⟩ := hgeo b₁ a₁
  obtain ⟨fAA, hAA, hAA0, hAA1⟩ := hgeo a₁ a₂
  obtain ⟨fA₂B₂, hA₂B₂, hA₂B₂0, hA₂B₂1⟩ := hgeo a₂ b₂
  obtain ⟨j, u, u', t, t', hu, hu', huu', ht, ht', htt', hclose, hclose'⟩ :=
    exists_long_close_pair_on_other_quadrilateral_side hδ hδ0 hgeo hβ
      hBB hBB0 hBB1 hB₁A₁ hB₁A₁0 hB₁A₁1 hAA hAA0 hAA1
      hA₂B₂ hA₂B₂0 hA₂B₂1 (by simpa [ν] using hlong)
  have hBqc : IsQuasiconvexSet (leftCosetOrbitAt H g s) σ :=
    isQuasiconvexSet_leftCosetOrbitAt hiso hquasi g
  obtain ⟨p, hpB, hup⟩ :=
    hBqc b₁ hb₁.1 b₂ hb₂.1 fBB hBB hBB0 hBB1 u hu
  obtain ⟨p', hpB', hup'⟩ :=
    hBqc b₁ hb₁.1 b₂ hb₂.1 fBB hBB hBB0 hBB1 u' hu'
  have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hj with hj | hj | hj
  · subst j
    simp at ht ht' hclose hclose'
    have hmax : β ≤ max t t' := by
      rcases le_total t t' with hle | hle
      · rw [abs_of_nonneg (sub_nonneg.mpr hle)] at htt'
        rw [max_eq_right hle]
        linarith [ht.1]
      · rw [abs_of_nonpos (sub_nonpos.mpr hle)] at htt'
        rw [max_eq_left hle]
        linarith [ht'.1]
    rcases le_total t t' with hle | hle
    · have hgeoDist : dist a₁ (fB₁A₁ t') = dist b₁ a₁ - t' := by
        calc
          dist a₁ (fB₁A₁ t') = dist (fB₁A₁ (dist b₁ a₁)) (fB₁A₁ t') := by rw [hB₁A₁1]
          _ = |dist b₁ a₁ - t'| := hB₁A₁.dist_eq ⟨dist_nonneg, le_rfl⟩ ht'
          _ = dist b₁ a₁ - t' := abs_of_nonneg (sub_nonneg.mpr ht'.2)
      have htri := dist_triangle4 a₁ (fB₁A₁ t') (fBB u') p'
      have hmin' := hb₁.2 p' hpB'
      have hcloseRev : dist (fB₁A₁ t') (fBB u') ≤ 6 * δ := by rwa [dist_comm]
      rw [dist_comm b₁ a₁] at hgeoDist
      have : t' ≤ 7 * δ + σ := by linarith
      have hβt : β ≤ t' := by simpa [max_eq_right hle] using hmax
      dsimp [β] at hβt
      linarith
    · have hgeoDist : dist a₁ (fB₁A₁ t) = dist b₁ a₁ - t := by
        calc
          dist a₁ (fB₁A₁ t) = dist (fB₁A₁ (dist b₁ a₁)) (fB₁A₁ t) := by rw [hB₁A₁1]
          _ = |dist b₁ a₁ - t| := hB₁A₁.dist_eq ⟨dist_nonneg, le_rfl⟩ ht
          _ = dist b₁ a₁ - t := abs_of_nonneg (sub_nonneg.mpr ht.2)
      have htri := dist_triangle4 a₁ (fB₁A₁ t) (fBB u) p
      have hmin := hb₁.2 p hpB
      have hcloseRev : dist (fB₁A₁ t) (fBB u) ≤ 6 * δ := by rwa [dist_comm]
      rw [dist_comm b₁ a₁] at hgeoDist
      have : t ≤ 7 * δ + σ := by linarith
      have hβt : β ≤ t := by simpa [max_eq_left hle] using hmax
      dsimp [β] at hβt
      linarith
  · subst j
    simp at ht ht' hclose hclose'
    have hAqc : IsQuasiconvexSet (leftCosetOrbitAt H f s) σ :=
      isQuasiconvexSet_leftCosetOrbitAt hiso hquasi f
    obtain ⟨q, hqA, htq⟩ := hAqc a₁ ha₁ a₂ ha₂ fAA hAA hAA0 hAA1 t ht
    obtain ⟨q', hqA', htq'⟩ := hAqc a₁ ha₁ a₂ ha₂ fAA hAA hAA0 hAA1 t' ht'
    obtain ⟨bp, hbpH, rfl⟩ := hpB
    obtain ⟨bp', hbp'H, rfl⟩ := hpB'
    obtain ⟨aq, haqH, rfl⟩ := hqA
    obtain ⟨aq', haq'H, rfl⟩ := hqA'
    have hfar : R ≤ dist ((g * bp) • s) ((g * bp') • s) := by
      have hsegment := hBB.dist_eq hu hu'
      have htri := dist_triangle4 (fBB u) ((g * bp) • s)
        ((g * bp') • s) (fBB u')
      have habs : |u - u'| = u' - u := by
        rw [abs_of_nonpos (by linarith [huu', hβ])]
        ring
      rw [hsegment, habs] at htri
      have hupRev : dist ((g * bp) • s) (fBB u) ≤ σ := by rwa [dist_comm]
      have hup'Rev : dist ((g * bp') • s) (fBB u') ≤ σ := by rwa [dist_comm]
      dsimp [β] at huu'
      linarith
    have hnear : dist ((g * bp) • s) ((f * aq) • s) ≤ ε := by
      have htri := dist_triangle4 ((g * bp) • s) (fBB u) (fAA t) ((f * aq) • s)
      have hupRev : dist ((g * bp) • s) (fBB u) ≤ σ := by rwa [dist_comm]
      dsimp [ε]
      linarith
    have hnear' : dist ((g * bp') • s) ((f * aq') • s) ≤ ε := by
      have htri := dist_triangle4 ((g * bp') • s) (fBB u') (fAA t') ((f * aq') • s)
      have hup'Rev : dist ((g * bp') • s) (fBB u') ≤ σ := by rwa [dist_comm]
      dsimp [ε]
      linarith
    have hfar0 : R ≤ dist (bp • s) (bp' • s) := by
      calc
        R ≤ dist ((g * bp) • s) ((g * bp') • s) := hfar
        _ = dist (g⁻¹ • ((g * bp) • s)) (g⁻¹ • ((g * bp') • s)) :=
          (hiso g⁻¹ ((g * bp) • s) ((g * bp') • s)).symm
        _ = dist (bp • s) (bp' • s) := by simp only [← mul_smul, inv_mul_cancel_left]
    have hnear0 : dist (bp • s) (((g⁻¹ * f) * aq) • s) ≤ ε := by
      calc
        dist (bp • s) (((g⁻¹ * f) * aq) • s) =
            dist (g⁻¹ • ((g * bp) • s)) (g⁻¹ • ((f * aq) • s)) := by
              simp only [← mul_smul, inv_mul_cancel_left, mul_assoc]
        _ = dist ((g * bp) • s) ((f * aq) • s) :=
          hiso g⁻¹ ((g * bp) • s) ((f * aq) • s)
        _ ≤ ε := hnear
    have hnear0' : dist (bp' • s) (((g⁻¹ * f) * aq') • s) ≤ ε := by
      calc
        dist (bp' • s) (((g⁻¹ * f) * aq') • s) =
            dist (g⁻¹ • ((g * bp') • s)) (g⁻¹ • ((f * aq') • s)) := by
              simp only [← mul_smul, inv_mul_cancel_left, mul_assoc]
        _ = dist ((g * bp') • s) ((f * aq') • s) :=
          hiso g⁻¹ ((g * bp') • s) ((f * aq') • s)
        _ ≤ ε := hnear'
    have hgf : g⁻¹ * f ∈ H := by
      apply hforce (g⁻¹ * f)
      intro D hDR
      refine ⟨bp, bp', hbpH, hbp'H, le_trans (le_of_lt hDR) hfar0,
        ⟨aq, haqH, ?_⟩, ⟨aq', haq'H, ?_⟩⟩
      · exact hnear0
      · exact hnear0'
    apply hfg
    have := H.inv_mem hgf
    simpa only [mul_inv_rev, inv_inv] using this
  · subst j
    simp at ht ht' hclose hclose'
    have hmin : min t t' + β ≤ dist a₂ b₂ := by
      rcases le_total t t' with hle | hle
      · have habs : |t' - t| = t' - t := abs_of_nonneg (sub_nonneg.mpr hle)
        rw [habs] at htt'
        rw [min_eq_left hle]
        linarith [ht'.2]
      · have habs : |t' - t| = t - t' := by
          rw [abs_of_nonpos (sub_nonpos.mpr hle)]
          ring
        rw [habs] at htt'
        rw [min_eq_right hle]
        linarith [ht.2]
    rcases le_total t t' with hle | hle
    · have hgeoDist : dist a₂ (fA₂B₂ t) = t := by
        calc
          dist a₂ (fA₂B₂ t) = dist (fA₂B₂ 0) (fA₂B₂ t) := by rw [hA₂B₂0]
          _ = |(0 : ℝ) - t| := hA₂B₂.dist_eq ⟨le_rfl, dist_nonneg⟩ ht
          _ = t := by rw [abs_of_nonpos (by linarith [ht.1])]; ring
      have htri := dist_triangle4 a₂ (fA₂B₂ t) (fBB u) p
      have hproj := hb₂.2 p hpB
      have hcloseRev : dist (fA₂B₂ t) (fBB u) ≤ 6 * δ := by rwa [dist_comm]
      have hbound : dist a₂ b₂ ≤ t + 7 * δ + σ := by linarith
      have hβbound : t + β ≤ dist a₂ b₂ := by simpa [min_eq_left hle] using hmin
      dsimp [β] at hβbound
      linarith
    · have hgeoDist : dist a₂ (fA₂B₂ t') = t' := by
        calc
          dist a₂ (fA₂B₂ t') = dist (fA₂B₂ 0) (fA₂B₂ t') := by rw [hA₂B₂0]
          _ = |(0 : ℝ) - t'| := hA₂B₂.dist_eq ⟨le_rfl, dist_nonneg⟩ ht'
          _ = t' := by rw [abs_of_nonpos (by linarith [ht'.1])]; ring
      have htri := dist_triangle4 a₂ (fA₂B₂ t') (fBB u') p'
      have hproj := hb₂.2 p' hpB'
      have hcloseRev : dist (fA₂B₂ t') (fBB u') ≤ 6 * δ := by rwa [dist_comm]
      have hbound : dist a₂ b₂ ≤ t' + 7 * δ + σ := by linarith
      have hβbound : t' + β ≤ dist a₂ b₂ := by simpa [min_eq_right hle] using hmin
      dsimp [β] at hβbound
      linarith

end Elementary
end GGT
end GroupApproximation
