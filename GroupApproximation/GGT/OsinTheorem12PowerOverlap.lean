import GroupApproximation.GGT.OsinTheorem12GeodesicProjection
import GroupApproximation.GGT.HullSCConeOffHeavyUniformThreshold

/-!
# DGO Lemma 6.7 for one WPD power orbit

The quantitative pigeonhole theorem in `ElementaryIndependence` exposes every
constant used by DGO Lemma 6.7.  Global acylindricity was only used there to
obtain one finite coarse stabilizer of the first axis.  In the application to
Osin's theorem that first axis is fixed, so WPD supplies exactly that finite
set.  This module performs that specialization and keeps the threshold uniform
over all bounded translates of the second copy of the same axis.
-/

namespace GroupApproximation
namespace GGT
namespace Elementary

open GroupApproximation.HullGeometry
open GroupApproximation.HullSC

universe u v

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X]
  [MulAction G X]

/-- WPD is unchanged on replacing an element by its inverse. -/
theorem IsWPDAt.inv (hiso : IsIsometricAction G X) {h : G} {x : X}
    (hwpd : IsWPDAt h x) : IsWPDAt h⁻¹ x := by
  intro eps heps
  obtain ⟨M, hfin⟩ := hwpd eps heps
  have hsub := pairStab_smul_subset hiso eps (h ^ (-(M : ℤ))) x ((h ^ M) • x)
  have himage : ((fun k : G => h ^ (-(M : ℤ)) * k * (h ^ (-(M : ℤ)))⁻¹) ''
      pairStab G eps x ((h ^ M) • x)).Finite := hfin.image _
  refine ⟨M, himage.subset ?_⟩
  intro k hk
  have hk' : k ∈ pairStab G eps ((h ^ (-(M : ℤ))) • x)
      x := by
    rw [mem_pairStab] at hk ⊢
    simpa only [zpow_neg, zpow_natCast, inv_pow] using hk.symm
  have hcancel : (h ^ (-(M : ℤ))) • ((h ^ M) • x) = x := by
    rw [← mul_smul]
    simp
  have hktrans : k ∈ pairStab G eps ((h ^ (-(M : ℤ))) • x)
      ((h ^ (-(M : ℤ))) • ((h ^ M) • x)) := by
    simpa only [hcancel] using hk'
  exact hsub hktrans

/-- A single fellow-travel threshold for a fixed WPD first axis and every
second axis satisfying fixed numerical loxodromy bounds. -/
theorem exists_common_zpow_of_forward_fellow_travel_fixed_wpd
    {δ C la Ba Da lb Bb Db : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (hgeo : IsGeodesicSpace X)
    (hiso : IsIsometricAction G X) (hC : 0 ≤ C)
    (hla : 0 < la) (hBa0 : 0 ≤ Ba) (hDa0 : 0 ≤ Da)
    (hlb : 0 < lb) (hBb0 : 0 ≤ Bb) (hDb0 : 0 ≤ Db)
    {a : G} {x : X}
    (hlox_a : ∀ n : ℕ, la * n - Ba ≤ dist x ((a ^ n) • x))
    (hdisp_a : dist x (a • x) ≤ Da) (hwpd : IsWPDAt a x) :
    ∃ T : ℝ, 0 < T ∧ ∀ (b : G),
      (∀ n : ℕ, lb * n - Bb ≤ dist x ((b ^ n) • x)) →
      dist x (b • x) ≤ Db →
      ∀ (n m : ℕ) (f q : ℝ → X),
        IsGeodesicSegment f 0 (dist x ((a ^ n) • x)) → f 0 = x →
        f (dist x ((a ^ n) • x)) = (a ^ n) • x →
        IsGeodesicSegment q 0 (dist x ((b ^ m) • x)) → q 0 = x →
        q (dist x ((b ^ m) • x)) = (b ^ m) • x →
        T ≤ dist x ((a ^ n) • x) → T ≤ dist x ((b ^ m) • x) →
        (∀ t : ℝ, 0 ≤ t → t ≤ T → dist (f t) (q t) ≤ C) →
        ∃ p r : ℤ, p ≠ 0 ∧ r ≠ 0 ∧ a ^ p = b ^ r := by
  obtain ⟨Ka, hKa0, hKa⟩ :=
    ElementaryMorse.exists_bound_chain_near_chord
      (D := Da) hδ hδ0 hDa0 hla hBa0
  obtain ⟨Kb, hKb0, hKb⟩ :=
    ElementaryMorse.exists_bound_chain_near_chord
      (D := Db) hδ hδ0 hDb0 hlb hBb0
  obtain ⟨Ga, hGa0, hGa⟩ :=
    ElementaryMorse.gromovProduct_ends_le_of_chain
      (D := Da) hδ hδ0 hDa0 hla hBa0 hgeo
  obtain ⟨Gb, hGb0, hGb⟩ :=
    ElementaryMorse.gromovProduct_ends_le_of_chain
      (D := Db) hδ hδ0 hDb0 hlb hBb0 hgeo
  let epsPair : ℝ :=
    (2 * Ka + 2 * Kb + C + Db) +
      (2 * Ka + 2 * Kb + C + 2 * Ga + 2 * Gb + 2 * Db) + 1
  have heps : 0 < epsPair := by dsimp [epsPair]; linarith
  obtain ⟨K, hKfin⟩ := hwpd epsPair heps.le
  let N := (pairStab G epsPair x ((a ^ K) • x)).ncard
  have hKcard : (pairStab G epsPair x ((a ^ K) • x)).ncard ≤ N := le_rfl
  obtain ⟨S₀, hS₀⟩ := exists_nat_gt (4 * (2 * Ka + 2 * Kb + C + Db) / la)
  let S : ℕ := S₀ + 1
  have hSpos : 0 < S := by dsimp [S]; omega
  have hSlaUniform : 4 * (2 * Ka + 2 * Kb + C + Db) < la * S := by
    rw [div_lt_iff₀ hla] at hS₀
    have hcast : (S₀ : ℝ) ≤ (S : ℝ) := by
      exact_mod_cast (show S₀ ≤ S by dsimp [S]; omega)
    nlinarith
  let E : ℕ := S * N + K
  let Ta : ℝ := ((E : ℝ) + 1) * Da + Ka + 2 * Db + Kb + 1
  let Tb : ℝ := Db * (((E : ℝ) * Da + 2 * Db + 2 * Bb) / lb + 1)
  let T : ℝ := Ta + Tb
  have hTa0 : 0 < Ta := by dsimp [Ta]; positivity
  have hTb0 : 0 ≤ Tb := by dsimp [Tb]; positivity
  have hT0 : 0 < T := by dsimp [T]; linarith
  refine ⟨T, hT0, ?_⟩
  intro b hlox_b hdisp_b
  have hKa' : ∀ (y : ℕ → X) (N' : ℕ),
      (∀ i, i < N' → dist (y i) (y (i + 1)) ≤ dist x (a • x)) →
      (∀ i j, i ≤ j → j ≤ N' →
        la * ((j - i : ℕ) : ℝ) - Ba ≤ dist (y i) (y j)) →
      ∀ L, 0 ≤ L → ∀ f, IsGeodesicSegment f 0 L → f 0 = y 0 →
        f L = y N' → ∀ j, j ≤ N' →
          ∃ t ∈ Set.Icc (0 : ℝ) L, dist (y j) (f t) ≤ Ka := by
    intro y N' hedge hprog
    exact hKa y N' (fun i hi => (hedge i hi).trans hdisp_a) hprog
  have hKb' : ∀ (y : ℕ → X) (N' : ℕ),
      (∀ i, i < N' → dist (y i) (y (i + 1)) ≤ dist x (b • x)) →
      (∀ i j, i ≤ j → j ≤ N' →
        lb * ((j - i : ℕ) : ℝ) - Bb ≤ dist (y i) (y j)) →
      ∀ L, 0 ≤ L → ∀ f, IsGeodesicSegment f 0 L → f 0 = y 0 →
        f L = y N' → ∀ j, j ≤ N' →
          ∃ t ∈ Set.Icc (0 : ℝ) L, dist (y j) (f t) ≤ Kb := by
    intro y N' hedge hprog
    exact hKb y N' (fun i hi => (hedge i hi).trans hdisp_b) hprog
  have hGa' : ∀ (y : ℕ → X) (N' : ℕ),
      (∀ i, i < N' → dist (y i) (y (i + 1)) ≤ dist x (a • x)) →
      (∀ i j, i ≤ j → j ≤ N' →
        la * ((j - i : ℕ) : ℝ) - Ba ≤ dist (y i) (y j)) →
      ∀ j, j ≤ N' → gromovProduct (y 0) (y N') (y j) ≤ Ga := by
    intro y N' hedge hprog
    exact hGa y N' (fun i hi => (hedge i hi).trans hdisp_a) hprog
  have hGb' : ∀ (y : ℕ → X) (N' : ℕ),
      (∀ i, i < N' → dist (y i) (y (i + 1)) ≤ dist x (b • x)) →
      (∀ i j, i ≤ j → j ≤ N' →
        lb * ((j - i : ℕ) : ℝ) - Bb ≤ dist (y i) (y j)) →
      ∀ j, j ≤ N' → gromovProduct (y 0) (y N') (y j) ≤ Gb := by
    intro y N' hedge hprog
    exact hGb y N' (fun i hi => (hedge i hi).trans hdisp_b) hprog
  have hPairRadius :
      (2 * Ka + 2 * Kb + C + dist x (b • x)) +
        (2 * Ka + 2 * Kb + C + 2 * Ga + 2 * Gb + 2 * dist x (b • x)) + 1
          ≤ epsPair := by
    dsimp [epsPair]
    linarith
  have hSla : 4 * (2 * Ka + 2 * Kb + C + dist x (b • x)) < la * S := by
    linarith
  have hTa : (((S * N + K : ℕ) : ℝ) + 1) * dist x (a • x) + Ka +
      2 * dist x (b • x) + Kb + 1 ≤ T := by
    dsimp [T, Ta, E]
    nlinarith [hTb0]
  have hActualInner :
      0 ≤ (((((S * N + K : ℕ) : ℝ)) * dist x (a • x) +
        2 * dist x (b • x) + 2 * Bb) / lb + 1) := by
    have hnumer : 0 ≤ ((S * N + K : ℕ) : ℝ) * dist x (a • x) +
        2 * dist x (b • x) + 2 * Bb := by positivity
    have hquot := div_nonneg hnumer hlb.le
    linarith
  have hInnerLe :
      (((((S * N + K : ℕ) : ℝ)) * dist x (a • x) +
        2 * dist x (b • x) + 2 * Bb) / lb + 1) ≤
      (((E : ℝ) * Da + 2 * Db + 2 * Bb) / lb + 1) := by
    dsimp [E]
    have hnum : ((S * N + K : ℕ) : ℝ) * dist x (a • x) +
        2 * dist x (b • x) + 2 * Bb ≤
        ((S * N + K : ℕ) : ℝ) * Da + 2 * Db + 2 * Bb := by
      nlinarith
    have hdiv := div_le_div_of_nonneg_right hnum hlb.le
    linarith
  have hTb : dist x (b • x) *
      (((((S * N + K : ℕ) : ℝ)) * dist x (a • x) +
        2 * dist x (b • x) + 2 * Bb) / lb + 1) ≤ T := by
    have hprod := mul_le_mul hdisp_b hInnerLe hActualInner (by positivity)
    dsimp [T, Tb]
    linarith [hTa0, hprod]
  exact ElementaryMorse.exists_common_zpow_of_forward_fellow_travel_of_pairStab_threshold
    hiso hC hla hlb hlox_a hlox_b hKa0 hKb0 hGa0 hGb0
      hKa' hKb' hGa' hGb' K N S hSpos hSla hPairRadius hKfin hKcard
      T hT0 hTa hTb

/-- Endpoint-close integer power segments for a fixed WPD first axis, uniformly
over all second axes with the displayed numerical bounds. -/
theorem exists_common_zpow_of_close_orbit_endpoints_fixed_wpd
    {δ E la Ba Da lb Bb Db : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (hgeo : IsGeodesicSpace X)
    (hiso : IsIsometricAction G X) (hE : 0 ≤ E)
    (hla : 0 < la) (hBa0 : 0 ≤ Ba) (hDa0 : 0 ≤ Da)
    (hlb : 0 < lb) (hBb0 : 0 ≤ Bb) (hDb0 : 0 ≤ Db)
    {a : G} {x : X}
    (hlox_a : ∀ n : ℕ, la * n - Ba ≤ dist x ((a ^ n) • x))
    (hdisp_a : dist x (a • x) ≤ Da) (hwpd : IsWPDAt a x) :
    ∃ T : ℝ, 0 < T ∧ ∀ (b : G),
      (∀ n : ℕ, lb * n - Bb ≤ dist x ((b ^ n) • x)) →
      dist x (b • x) ≤ Db →
      ∀ n m : ℤ,
        T ≤ dist x ((a ^ n) • x) → T ≤ dist x ((b ^ m) • x) →
        dist ((a ^ n) • x) ((b ^ m) • x) ≤ E →
        ∃ p r : ℤ, p ≠ 0 ∧ r ≠ 0 ∧ a ^ p = b ^ r := by
  let C : ℝ := 2 * (E + 6 * δ)
  have hC : 0 ≤ C := by dsimp [C]; linarith
  have hlox_ai : ∀ n : ℕ, la * n - Ba ≤ dist x (((a⁻¹) ^ n) • x) := by
    intro n
    rw [dist_inv_pow_smul_eq hiso]
    exact hlox_a n
  have hdisp_ai : dist x (a⁻¹ • x) ≤ Da := by
    simpa using (show dist x (((a⁻¹) ^ 1) • x) ≤ Da by
      rw [dist_inv_pow_smul_eq hiso]
      simpa using hdisp_a)
  obtain ⟨T₁, hT₁, hlong₁⟩ :=
    exists_common_zpow_of_forward_fellow_travel_fixed_wpd
      hδ hδ0 hgeo hiso hC hla hBa0 hDa0 hlb hBb0 hDb0
        hlox_a hdisp_a hwpd
  obtain ⟨T₂, hT₂, hlong₂⟩ :=
    exists_common_zpow_of_forward_fellow_travel_fixed_wpd
      hδ hδ0 hgeo hiso hC hla hBa0 hDa0 hlb hBb0 hDb0
        hlox_ai hdisp_ai (IsWPDAt.inv hiso hwpd)
  let T : ℝ := T₁ + T₂
  have hT : 0 < T := by dsimp [T]; linarith
  refine ⟨T, hT, ?_⟩
  intro b hlox_b hdisp_b
  have hlox_bi : ∀ n : ℕ, lb * n - Bb ≤ dist x (((b⁻¹) ^ n) • x) := by
    intro n
    rw [dist_inv_pow_smul_eq hiso]
    exact hlox_b n
  have hdisp_bi : dist x (b⁻¹ • x) ≤ Db := by
    simpa using (show dist x (((b⁻¹) ^ 1) • x) ≤ Db by
      rw [dist_inv_pow_smul_eq hiso]
      simpa using hdisp_b)
  have hnat : ∀ (c d : G) (T₀ : ℝ), T₀ ≤ T →
      (∀ (e : G),
        (∀ n : ℕ, lb * n - Bb ≤ dist x ((e ^ n) • x)) →
        dist x (e • x) ≤ Db →
        ∀ (n m : ℕ) (f q : ℝ → X),
          IsGeodesicSegment f 0 (dist x ((c ^ n) • x)) → f 0 = x →
          f (dist x ((c ^ n) • x)) = (c ^ n) • x →
          IsGeodesicSegment q 0 (dist x ((e ^ m) • x)) → q 0 = x →
          q (dist x ((e ^ m) • x)) = (e ^ m) • x →
          T₀ ≤ dist x ((c ^ n) • x) → T₀ ≤ dist x ((e ^ m) • x) →
          (∀ t : ℝ, 0 ≤ t → t ≤ T₀ → dist (f t) (q t) ≤ C) →
          ∃ p r : ℤ, p ≠ 0 ∧ r ≠ 0 ∧ c ^ p = e ^ r) →
      (∀ n : ℕ, lb * n - Bb ≤ dist x ((d ^ n) • x)) →
      dist x (d • x) ≤ Db →
      ∀ n m : ℕ,
        T ≤ dist x ((c ^ n) • x) → T ≤ dist x ((d ^ m) • x) →
        dist ((c ^ n) • x) ((d ^ m) • x) ≤ E →
        ∃ p r : ℤ, p ≠ 0 ∧ r ≠ 0 ∧ c ^ p = d ^ r := by
    intro c d T₀ hT₀T hlong hdlox hddisp n m hn hm hend
    obtain ⟨f, hf, hf0, hf1⟩ := hgeo x ((c ^ n) • x)
    obtain ⟨q, hq, hq0, hq1⟩ := hgeo x ((d ^ m) • x)
    refine hlong d hdlox hddisp n m f q hf hf0 hf1 hq hq0 hq1
      (hT₀T.trans hn) (hT₀T.trans hm) ?_
    intro t ht0 htT
    refine dist_same_parameter_le_of_geodesic_close_endpoints (E := E)
      hδ hδ0 hgeo hE hf dist_nonneg hq dist_nonneg ?_ ?_
        ⟨ht0, htT.trans (hT₀T.trans hn)⟩
        ⟨ht0, htT.trans (hT₀T.trans hm)⟩
    · rw [hf0, hq0]
    · rw [hf1, hq1]
      exact hend
  intro n m hn hm hend
  rcases ElementaryMorse.zpow_eq_pow_toNat_or_inv a n with ⟨-, hna⟩ | ⟨-, hna⟩ <;>
    rcases ElementaryMorse.zpow_eq_pow_toNat_or_inv b m with ⟨-, hmb⟩ | ⟨-, hmb⟩ <;>
      rw [hna] at hn hend <;> rw [hmb] at hm hend
  · exact hnat a b T₁ (by dsimp [T]; linarith) hlong₁
      hlox_b hdisp_b _ _ hn hm hend
  · exact common_zpow_of_inv_right
      (hnat a b⁻¹ T₁ (by dsimp [T]; linarith) hlong₁
        hlox_bi hdisp_bi _ _ hn hm hend)
  · exact common_zpow_of_inv_left
      (hnat a⁻¹ b T₂ (by dsimp [T]; linarith) hlong₂
        hlox_b hdisp_b _ _ hn hm hend)
  · exact common_zpow_of_inv_left (common_zpow_of_inv_right
      (hnat a⁻¹ b⁻¹ T₂ (by dsimp [T]; linarith) hlong₂
        hlox_bi hdisp_bi _ _ hn hm hend))

/-- **DGO Lemma 6.7 for the power orbit of one loxodromic WPD element.**

Normalize the first matched pair by `h⁻ⁱ`.  The resulting conjugator moves
the basepoint by at most `ε`, so its conjugate of `h` has the same loxodromy
data with additive and one-step errors enlarged uniformly by `2ε`.  The fixed
WPD endpoint theorem above therefore has a threshold independent of the
conjugator. -/
theorem powerOrbitDiameterForcesConjugatePowerAt_of_geodesic
    {Y : Type v} [PseudoMetricSpace Y] [MulAction G Y]
    {δ : ℝ} (hδ : IsHyperbolicSpace δ Y) (hδ0 : 0 ≤ δ)
    (hgeo : IsGeodesicSpace Y) (hiso : IsIsometricAction G Y)
    {h : G} {x : Y} (hlox : IsLoxodromic h x) (hwpd : IsWPDAt h x) :
    PowerOrbitDiameterForcesConjugatePowerAt h x := by
  obtain ⟨la, hla, Ba, hBa, hlin⟩ := hlox
  intro eps heps
  let Da : ℝ := dist x (h • x)
  have hDa : 0 ≤ Da := dist_nonneg
  let Bb : ℝ := Ba + 2 * eps
  let Db : ℝ := Da + 2 * eps
  have hBb : 0 ≤ Bb := by dsimp [Bb]; linarith
  have hDb : 0 ≤ Db := by dsimp [Db]; linarith
  obtain ⟨T, hT, hendpoint⟩ :=
    exists_common_zpow_of_close_orbit_endpoints_fixed_wpd
      hδ hδ0 hgeo hiso (E := 2 * eps) (by linarith)
      hla hBa hDa hla hBb hDb hlin le_rfl hwpd
  refine ⟨T + 4 * eps + 1, by linarith, ?_⟩
  intro g hoverlap
  obtain ⟨i, j, k, l, hij, hik, hjl⟩ :=
    hoverlap (T + 4 * eps) (by linarith)
  let c : G := h ^ (-i) * g * h ^ k
  let b : G := c * h * c⁻¹
  have hc : dist x (c • x) ≤ eps := by
    have hm := hiso (h ^ (-i)) ((h ^ i) • x) ((g * h ^ k) • x)
    have hleft : (h ^ (-i)) • ((h ^ i) • x) = x := by
      rw [← mul_smul]
      simp
    have hright : (h ^ (-i)) • ((g * h ^ k) • x) = c • x := by
      rw [← mul_smul]
      congr 1
      dsimp [c]
      group
    rw [hleft, hright] at hm
    exact hm.trans_le hik
  have hci : dist (c⁻¹ • x) x ≤ eps := by
    have hm := hiso c (c⁻¹ • x) x
    rw [smul_inv_smul] at hm
    rw [← hm]
    exact hc
  have hbpow (n : ℤ) : b ^ n = c * h ^ n * c⁻¹ := by
    dsimp [b]
    rw [conj_zpow]
  have hbclose (n : ℤ) :
      dist ((c * h ^ n) • x) ((b ^ n) • x) ≤ eps := by
    have hci' : dist x (c⁻¹ • x) ≤ eps := by
      rwa [dist_comm]
    calc
      dist ((c * h ^ n) • x) ((b ^ n) • x) =
          dist ((c * h ^ n) • x) ((c * h ^ n) • (c⁻¹ • x)) := by
            rw [hbpow]
            congr 1
            rw [mul_smul]
      _ = dist x (c⁻¹ • x) := hiso (c * h ^ n) x (c⁻¹ • x)
      _ ≤ eps := hci'
  have hblin : ∀ n : ℕ, la * n - Bb ≤ dist x ((b ^ n) • x) := by
    intro n
    have hmiddle : dist (c • x) ((c * h ^ n) • x) =
        dist x ((h ^ n) • x) := by
      rw [show (c * h ^ n) • x = c • ((h ^ n) • x) by
        rw [mul_smul], hiso]
    have htri := dist_triangle4 (c • x) x
      ((b ^ n) • x) ((c * h ^ n) • x)
    have hbc : dist ((c * h ^ n) • x) (b ^ n • x) ≤ eps := by
      simpa only [zpow_natCast] using hbclose (n : ℤ)
    have hcx : dist (c • x) x ≤ eps := by rwa [dist_comm]
    have hbc' : dist (b ^ n • x) ((c * h ^ n) • x) ≤ eps := by
      rwa [dist_comm]
    rw [hmiddle] at htri
    dsimp [Bb]
    linarith [hlin n, hcx, hbc']
  have hbdisp : dist x (b • x) ≤ Db := by
    have hmiddle : dist (c • x) ((c * h) • x) = Da := by
      rw [show (c * h) • x = c • (h • x) by rw [mul_smul], hiso]
    have hbc : dist ((c * h) • x) (b • x) ≤ eps := by
      simpa only [zpow_one] using hbclose 1
    have htri := dist_triangle4 x (c • x) ((c * h) • x) (b • x)
    dsimp [Db]
    linarith
  have hfirst : dist x ((h ^ (j - i)) • x) =
      dist ((h ^ i) • x) ((h ^ j) • x) := by
    have hm := hiso (h ^ (-i)) ((h ^ i) • x) ((h ^ j) • x)
    have hi0 : (h ^ (-i)) • ((h ^ i) • x) = x := by
      rw [← mul_smul]
      simp
    have hij' : (h ^ (-i)) • ((h ^ j) • x) = (h ^ (j - i)) • x := by
      rw [← mul_smul, ← zpow_add]
      congr 2
      ring
    rwa [hi0, hij'] at hm
  have htranslated :
      dist ((h ^ (j - i)) • x) ((c * h ^ (l - k)) • x) ≤ eps := by
    have hm := hiso (h ^ (-i)) ((h ^ j) • x) ((g * h ^ l) • x)
    have hleft : (h ^ (-i)) • ((h ^ j) • x) = (h ^ (j - i)) • x := by
      rw [← mul_smul, ← zpow_add]
      congr 2
      ring
    have hright : (h ^ (-i)) • ((g * h ^ l) • x) =
        (c * h ^ (l - k)) • x := by
      rw [← mul_smul]
      congr 1
      dsimp [c]
      group
    rw [hleft, hright] at hm
    exact hm.trans_le hjl
  have hend : dist ((h ^ (j - i)) • x) ((b ^ (l - k)) • x) ≤ 2 * eps := by
    exact (dist_triangle _ ((c * h ^ (l - k)) • x) _).trans
      (by linarith [htranslated, hbclose (l - k)])
  have hlongh : T ≤ dist x ((h ^ (j - i)) • x) := by
    rw [hfirst]
    linarith
  have hlongb : T ≤ dist x ((b ^ (l - k)) • x) := by
    have htri := dist_triangle x ((b ^ (l - k)) • x) ((h ^ (j - i)) • x)
    have hend' : dist ((b ^ (l - k)) • x) ((h ^ (j - i)) • x) ≤ 2 * eps := by
      rwa [dist_comm]
    linarith
  obtain ⟨p, q, hp, hq, hpq⟩ :=
    hendpoint b hblin hbdisp (j - i) (l - k) hlongh hlongb hend
  refine ⟨q, p, hq, hp, ?_⟩
  have hconj : c * h ^ q * c⁻¹ = h ^ p := by
    rw [← hbpow]
    exact hpq.symm
  dsimp [c] at hconj
  calc
    g * h ^ q * g⁻¹ = h ^ i * (h ^ (-i) * g * h ^ k * h ^ q *
        (h ^ (-i) * g * h ^ k)⁻¹) * h ^ (-i) := by group
    _ = h ^ i * h ^ p * h ^ (-i) := by rw [hconj]
    _ = h ^ p := by group

/-- The power-orbit form of DGO Lemma 6.7 is unconditional. -/
theorem dgoTheorem68PowerOverlap_unconditional :
    DGOTheorem68PowerOverlap.{u, v} := by
  intro G _inst D
  letI : PseudoMetricSpace D.Space := D.metricSpace
  letI : MulAction G D.Space := D.mulAction
  exact powerOrbitDiameterForcesConjugatePowerAt_of_geodesic
    D.hyperbolic (nonneg_of_isHyperbolicSpace D.hyperbolic D.base)
      D.geodesic D.isometric D.loxodromic D.wpd

/-- DGO Corollary 2.9 for geodesic witnesses now depends only on the projection
criterion DGO Theorem 4.42; Lemma 6.7 is proved above. -/
theorem dgoTheorem68_of_projection_unconditional
    (h442 : DGOTheorem442.{u, v}) : DGOTheorem68.{u, v} :=
  dgoTheorem68_of_geodesic_projection h442
    dgoTheorem68PowerOverlap_unconditional

/-- Osin's implication with the DGO Lemma 6.7 input removed. -/
theorem osinTheorem12_of_geodesic_projection_unconditional
    (h442 : DGOTheorem442.{u, v}) : OsinTheorem12.{u, v} :=
  osinTheorem12_of_geodesic_projection h442
    dgoTheorem68PowerOverlap_unconditional

end Elementary
end GGT
end GroupApproximation
