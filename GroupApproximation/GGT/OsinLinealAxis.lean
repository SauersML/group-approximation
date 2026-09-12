import GroupApproximation.GGT.OsinChainLemma
import GroupApproximation.GGT.PNaiveChain
import GroupApproximation.GGT.GromovSequentialBoundary

/-!
# Orbit sequences near the axis of a local gap

Infrastructure for the exclusion of the lineal case in Osin's Theorem 1.1
(Osin 2016, §3: "`|Λ(G)| = 2` … contains a loxodromic element and any two
loxodromic elements have the same limit points").

Let `h` have a local gap at `w`: its turn `(h w | h⁻¹ w)_w` is at most `C`, and
`2(C + 2δ) < d(w, h w)`.  Consider orbit sequences `xᵢ` that stay within `K` of
axis points `h^{mᵢ} w`.

* If `xᵢ` converges at infinity, then eventually all `mᵢ` are positive, or all
  are negative (`eventually_sign_of_near`).  Two axis points on opposite sides
  meet at `w` with product at most `C + 2δ`.
* Two convergent sequences whose exponents are eventually positive are
  equivalent at infinity (`equivAtInfinity_of_near_pos`), and likewise for
  negative exponents (`equivAtInfinity_of_near_neg`).  Two axis points on the same
  side are seen from `w` in a common direction for the smaller of the two
  displacements.

The vocabulary is `GGT/GromovSequentialBoundary`'s: `ConvergesAtInfinity` and
`EquivAtInfinity`.

## Manuscript status

Infrastructure for the limit-set spelling of acylindrical hyperbolicity used in
`sec:torsion-free`; certifies no printed sentence on its own.
-/

namespace GroupApproximation
namespace GGT
namespace OsinClassification

open GroupApproximation.HullGeometry
open GroupApproximation.GGT.SequentialBoundary

universe u v

section Space

variable {X : Type v} [PseudoMetricSpace X]

/-- **Moving both points moves a Gromov product by at most the two distances.** -/
theorem le_gromovProduct_of_close (p q p' q' w : X) :
    gromovProduct p' q' w - dist p p' - dist q q' ≤ gromovProduct p q w := by
  unfold gromovProduct
  have h1 := dist_triangle p' p w
  have h2 := dist_triangle q' q w
  have h3 := dist_triangle p p' q
  have h4 := dist_triangle p' q' q
  rw [dist_comm p' p] at h1
  rw [dist_comm q' q] at h2 h4
  linarith

end Space

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X] [MulAction G X]

/-- **Two positive axis points are seen from `w` in a common direction** for the
smaller displacement, up to `C + 2δ`. -/
theorem le_gromovProduct_pow_pow' {δ C : ℝ} (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ)
    (hiso : IsIsometricAction G X) {h : G} {w : X}
    (hloc : gromovProduct (h • w) (h⁻¹ • w) w ≤ C) (hC : 0 ≤ C)
    (hgap : 2 * (C + 2 * δ) < dist w (h • w)) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j) :
    (dist w (h • w) - 2 * (C + δ)) * (min i j : ℕ) - (C + 2 * δ) ≤
      gromovProduct ((h ^ i) • w) ((h ^ j) • w) w := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · have h1 := PNaive.le_gromovProduct_pow_pow hδ hδ0 hiso hloc hC hgap hi hij
    have h2 := PNaive.le_dist_pow_smul hδ hδ0 hiso hloc hC hgap i
    rw [min_eq_left hij.le]
    linarith
  · have h2 := PNaive.le_dist_pow_smul hδ hδ0 hiso hloc hC hgap i
    rw [min_self, gromovProduct_self, dist_comm ((h ^ i) • w) w]
    linarith
  · have h1 := PNaive.le_gromovProduct_pow_pow hδ hδ0 hiso hloc hC hgap hj hji
    have h2 := PNaive.le_dist_pow_smul hδ hδ0 hiso hloc hC hgap j
    rw [min_eq_right hji.le, gromovProduct_comm]
    linarith

/-- **The displacement of a power is at most the exponent times the step.** -/
theorem dist_pow_smul_le (hiso : IsIsometricAction G X) (h : G) (w : X) (n : ℕ) :
    dist w ((h ^ n) • w) ≤ n * dist w (h • w) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have htri := dist_triangle w ((h ^ n) • w) ((h ^ (n + 1)) • w)
      have hstep : dist ((h ^ n) • w) ((h ^ (n + 1)) • w) = dist w (h • w) := by
        rw [pow_succ, mul_smul, hiso]
      push_cast
      linarith

/-- A positive integer exponent is a natural one. -/
theorem zpow_eq_pow_toNat {h : G} {m : ℤ} (hm : 0 ≤ m) : h ^ m = h ^ m.toNat := by
  rw [← zpow_natCast, Int.toNat_of_nonneg hm]

/-- **A convergent sequence near the axis eventually keeps one side.** -/
theorem eventually_sign_of_near {δ C K : ℝ} (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ)
    (hiso : IsIsometricAction G X) {h : G} {w : X}
    (hloc : gromovProduct (h • w) (h⁻¹ • w) w ≤ C) (hC : 0 ≤ C)
    (hgap : 2 * (C + 2 * δ) < dist w (h • w)) {x : ℕ → X}
    (hconv : ConvergesAtInfinity x w) {m : ℕ → ℤ}
    (hnear : ∀ i, dist ((h ^ m i) • w) (x i) ≤ K) :
    ∃ N : ℕ, (∀ i, N ≤ i → 1 ≤ m i) ∨ (∀ i, N ≤ i → m i ≤ -1) := by
  obtain ⟨N, hN⟩ := hconv (C + 2 * δ + 2 * K + 1)
  have hbig : ∀ i j, N ≤ i → N ≤ j →
      C + 2 * δ < gromovProduct ((h ^ m i) • w) ((h ^ m j) • w) w := by
    intro i j hi hj
    have h1 := hN i j hi hj
    have h2 := le_gromovProduct_of_close ((h ^ m i) • w) ((h ^ m j) • w) (x i) (x j) w
    have h3 := hnear i
    have h4 := hnear j
    linarith
  have hne : ∀ i, N ≤ i → m i ≠ 0 := by
    intro i hi hmi
    have h1 := hbig i i hi hi
    rw [hmi, zpow_zero, one_smul, gromovProduct_self, dist_self] at h1
    linarith
  -- opposite sides meet with a bounded product
  have hopp : ∀ i j, N ≤ i → N ≤ j → 1 ≤ m i → m j ≤ -1 → False := by
    intro i j hi hj hmi hmj
    have h1 := hbig i j hi hj
    have hpos : h ^ m i = h ^ (m i).toNat := zpow_eq_pow_toNat (by omega)
    have hneg : h ^ m j = h⁻¹ ^ (-m j).toNat := by
      rw [← zpow_natCast, Int.toNat_of_nonneg (by omega), inv_zpow', neg_neg]
    rw [hpos, hneg, gromovProduct_comm] at h1
    have h2 := PNaive.gromovProduct_inv_pow_pow_le hδ hδ0 hiso hloc hC hgap
      (i := (-m j).toNat) (j := (m i).toNat) (by omega) (by omega)
    linarith
  refine ⟨N, ?_⟩
  by_cases hmN : 1 ≤ m N
  · left
    intro i hi
    by_contra hmi
    have hmi' : m i ≤ -1 := by
      have := hne i hi
      omega
    exact hopp N i le_rfl hi hmN hmi'
  · right
    intro i hi
    have hmN' : m N ≤ -1 := by
      have := hne N le_rfl
      omega
    by_contra hmi
    have hmi' : 1 ≤ m i := by
      have := hne i hi
      omega
    exact hopp i N hi le_rfl hmi' hmN'

/-- **Two convergent sequences near the positive half-axis are equivalent at
infinity.** -/
theorem equivAtInfinity_of_near_pos {δ C K : ℝ} (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ)
    (hiso : IsIsometricAction G X) {h : G} {w : X}
    (hloc : gromovProduct (h • w) (h⁻¹ • w) w ≤ C) (hC : 0 ≤ C)
    (hgap : 2 * (C + 2 * δ) < dist w (h • w)) {x x' : ℕ → X}
    (hconv : ConvergesAtInfinity x w) (hconv' : ConvergesAtInfinity x' w)
    {m m' : ℕ → ℤ} (hnear : ∀ i, dist ((h ^ m i) • w) (x i) ≤ K)
    (hnear' : ∀ i, dist ((h ^ m' i) • w) (x' i) ≤ K) {N N' : ℕ}
    (hpos : ∀ i, N ≤ i → 1 ≤ m i) (hpos' : ∀ i, N' ≤ i → 1 ≤ m' i) :
    EquivAtInfinity x x' w := by
  have hL : 0 < dist w (h • w) - 2 * (C + δ) := by linarith
  -- the exponents tend to infinity
  have hdiv : ∀ (y : ℕ → X) (p : ℕ → ℤ) (M₀ : ℕ), ConvergesAtInfinity y w →
      (∀ i, dist ((h ^ p i) • w) (y i) ≤ K) → (∀ i, M₀ ≤ i → 1 ≤ p i) →
      ∀ T : ℕ, ∃ M : ℕ, ∀ i, M ≤ i → T ≤ (p i).toNat ∧ 1 ≤ p i := by
    intro y p M₀ hy hyn hyp T
    obtain ⟨M, hM⟩ := hy (T * dist w (h • w) + K + 1)
    refine ⟨max M M₀, fun i hi => ⟨?_, hyp i (le_trans (le_max_right _ _) hi)⟩⟩
    have h1 := hM i i (le_trans (le_max_left _ _) hi) (le_trans (le_max_left _ _) hi)
    rw [gromovProduct_self] at h1
    have hpi := hyp i (le_trans (le_max_right _ _) hi)
    have h2 := dist_triangle w ((h ^ p i) • w) (y i)
    have h3 := hyn i
    rw [zpow_eq_pow_toNat (by omega)] at h2 h3
    have h4 := dist_pow_smul_le hiso h w (p i).toNat
    rw [dist_comm (y i) w] at h1
    by_contra hlt
    push Not at hlt
    have hle : ((p i).toNat : ℝ) ≤ T := by exact_mod_cast hlt.le
    have hmul : ((p i).toNat : ℝ) * dist w (h • w) ≤ T * dist w (h • w) :=
      mul_le_mul_of_nonneg_right hle dist_nonneg
    linarith
  intro M
  obtain ⟨T, hT⟩ := exists_nat_gt ((M + (C + 2 * δ) + 2 * K) /
    (dist w (h • w) - 2 * (C + δ)))
  obtain ⟨M₁, hM₁⟩ := hdiv x m N hconv hnear hpos T
  obtain ⟨M₂, hM₂⟩ := hdiv x' m' N' hconv' hnear' hpos' T
  refine ⟨max M₁ M₂, fun i j hi hj => ?_⟩
  obtain ⟨hTi, hmi⟩ := hM₁ i (le_trans (le_max_left _ _) hi)
  obtain ⟨hTj, hmj⟩ := hM₂ j (le_trans (le_max_right _ _) hj)
  have hprod := le_gromovProduct_pow_pow' hδ hδ0 hiso hloc hC hgap
    (i := (m i).toNat) (j := (m' j).toNat) (by omega) (by omega)
  have hclose := le_gromovProduct_of_close (x i) (x' j) ((h ^ (m i).toNat) • w)
    ((h ^ (m' j).toNat) • w) w
  have hn1 := hnear i
  have hn2 := hnear' j
  rw [zpow_eq_pow_toNat (by omega)] at hn1 hn2
  rw [dist_comm (x i), dist_comm (x' j)] at hclose
  have hmin : (T : ℝ) ≤ ((min (m i).toNat (m' j).toNat : ℕ) : ℝ) := by
    exact_mod_cast le_min hTi hTj
  rw [div_lt_iff₀ hL] at hT
  have hmul := mul_le_mul_of_nonneg_left hmin hL.le
  linarith

/-- **Two convergent sequences near the negative half-axis are equivalent at
infinity**: the positive case for `h⁻¹`. -/
theorem equivAtInfinity_of_near_neg {δ C K : ℝ} (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ)
    (hiso : IsIsometricAction G X) {h : G} {w : X}
    (hloc : gromovProduct (h • w) (h⁻¹ • w) w ≤ C) (hC : 0 ≤ C)
    (hgap : 2 * (C + 2 * δ) < dist w (h • w)) {x x' : ℕ → X}
    (hconv : ConvergesAtInfinity x w) (hconv' : ConvergesAtInfinity x' w)
    {m m' : ℕ → ℤ} (hnear : ∀ i, dist ((h ^ m i) • w) (x i) ≤ K)
    (hnear' : ∀ i, dist ((h ^ m' i) • w) (x' i) ≤ K) {N N' : ℕ}
    (hneg : ∀ i, N ≤ i → m i ≤ -1) (hneg' : ∀ i, N' ≤ i → m' i ≤ -1) :
    EquivAtInfinity x x' w := by
  have hloc' : gromovProduct (h⁻¹ • w) (h⁻¹⁻¹ • w) w ≤ C := by
    rw [PNaive.gromovProduct_inv_turn]
    exact hloc
  have hgap' : 2 * (C + 2 * δ) < dist w (h⁻¹ • w) := by
    rw [PNaive.dist_inv_smul hiso]
    exact hgap
  have hflip : ∀ p : ℤ, h ^ p = h⁻¹ ^ (-p) := fun p => by rw [inv_zpow', neg_neg]
  refine equivAtInfinity_of_near_pos hδ hδ0 hiso hloc' hC hgap' hconv hconv'
    (m := fun i => -m i) (m' := fun i => -m' i) (fun i => ?_) (fun i => ?_)
    (N := N) (N' := N') (fun i hi => ?_) (fun i hi => ?_)
  · show dist ((h⁻¹ ^ (-m i)) • w) (x i) ≤ K
    rw [← hflip]
    exact hnear i
  · show dist ((h⁻¹ ^ (-m' i)) • w) (x' i) ≤ K
    rw [← hflip]
    exact hnear' i
  · have := hneg i hi
    show 1 ≤ -m i
    omega
  · have := hneg' i hi
    show 1 ≤ -m' i
    omega

end OsinClassification
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.OsinClassification.le_gromovProduct_of_close
#audit_axioms GroupApproximation.GGT.OsinClassification.le_gromovProduct_pow_pow'
#audit_axioms GroupApproximation.GGT.OsinClassification.eventually_sign_of_near
#audit_axioms GroupApproximation.GGT.OsinClassification.equivAtInfinity_of_near_pos
#audit_axioms GroupApproximation.GGT.OsinClassification.equivAtInfinity_of_near_neg
