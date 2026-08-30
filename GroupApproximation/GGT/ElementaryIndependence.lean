import GroupApproximation.GGT.DGOLemma67Pigeonhole

/-!
# Two loxodromic elements without a common power are independent

`Elementary.IndependentOfNoCommonZpow` (Osin, Lemma 6.5 and Corollary 6.6) is
proved here in every geodesic hyperbolic space carrying an acylindrical
isometric action, and then at Hull's Cayley graph through the geodesic
realisation.  This is also `AxisDichotomyRoute.CommonPowerInGeodesicSpace`,
the residual of the axis dichotomy.

## The argument

Suppose `a` and `b` are loxodromic at `x` and not independent.
`exists_long_fellow_geodesics_of_not_independent` gives, for every `T`,
exponents `n, m ≠ 0` and geodesics `f` from `x` to `aⁿx` and `q` from `x` to
`bᵐx` that stay `4δ`-close for length `T`.  Replacing `a` or `b` by its inverse
makes `n, m > 0`.

**Parameters.**  Every forward orbit point `aⁱx` is within `K₂(a)` of `f`, at a
parameter that differs from `d(x, aⁱx)` by at most `K₂(a)`; likewise for `b`
and `q`.  Since `f` and `q` fellow-travel and `q` is a geodesic, two orbit
points `aⁱx` and `bʲx` whose parameters lie in the fellow-travel range are at
distance at most `2K₂(a) + 2K₂(b) + 4δ + |d(x, aⁱx) − d(x, bʲx)|`
(`dist_le_of_parameters`).  So closeness is controlled by distance from `x`.

**Partners.**  The distances `d(x, bʲx)` start at `0`, increase by at most
`d(x, bx)` per step and reach `d(x, bᵐx) ≥ T`, so for every target `ρ ≤ T` some
`j ≤ m` has `d(x, bʲx) ∈ [ρ, ρ + d(x, bx)]` (`exists_index_near_of_steps`).
Taking `ρ = d(x, aᵉx)` gives a partner `J e` with `aᵉx` and `b^{J e}x` within
`ε₁` of each other.

**Two basepoints.**  Acylindricity asks for exponent pairs matched at two
points `R` apart.  The second point is `y = aᴷx` with `d(x, y) ≥ R`.  For an
exponent `e`, `aᵉy = a^{e+K}x` and `b^{J e}y` is within `ε₁` of
`b^{J e + J K}x`.  The distances `d(x, a^{e+K}x)` and `d(x, b^{J e + J K}x)`
are each within `2K₂` of the sum of the two constituent distances, because an
orbit chain is within `K₂` of the chord joining its ends and so the Gromov
product of the ends at any vertex is at most `K₂`
(`gromovProduct_ends_le_of_chain`); and the constituent distances match up to
`d(x, bx)`.  So the two points are close by the parameter estimate, and every
pair is matched at both basepoints.

**Spacing.**  The `a`-exponents are the multiples of an `S` with
`τ(a)·S > 2ε₁`, so distinct exponents have distinct partners, and
`acylindrical_common_power_of_two_orbit_fellow_travel` produces a common
nonzero power.  The fellow-travel length `T` is chosen after all constants so
that every exponent used stays inside the chains and inside the fellow-travel
range.

## Status

**Not compiled**, written while builds were frozen.
-/

namespace GroupApproximation
namespace GGT
namespace ElementaryMorse

open GroupApproximation.HullGeometry

universe u v

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X] [MulAction G X]

/-! ## Forward orbit chains -/

/-- The forward orbit chain `i ↦ aⁱ x`. -/
def fwdChain (a : G) (x : X) (i : ℕ) : X := (a ^ i) • x

omit [PseudoMetricSpace X] in
theorem fwdChain_zero (a : G) (x : X) : fwdChain a x 0 = x := by
  unfold fwdChain
  rw [pow_zero, one_smul]

theorem fwdChain_dist (hiso : IsIsometricAction G X) (a : G) (x : X) {i j : ℕ}
    (hij : i ≤ j) :
    dist (fwdChain a x i) (fwdChain a x j) = dist x ((a ^ (j - i)) • x) := by
  unfold fwdChain
  have h : a ^ j = a ^ i * a ^ (j - i) := by
    rw [← pow_add, Nat.add_sub_of_le hij]
  rw [h, mul_smul, hiso]

theorem fwdChain_edge (hiso : IsIsometricAction G X) (a : G) (x : X) (i : ℕ) :
    dist (fwdChain a x i) (fwdChain a x (i + 1)) = dist x (a • x) := by
  rw [fwdChain_dist hiso a x (Nat.le_add_right i 1),
    Nat.add_sub_cancel_left, pow_one]

theorem fwdChain_prog (hiso : IsIsometricAction G X) {a : G} {x : X} {l B : ℝ}
    (hlox : ∀ n : ℕ, l * n - B ≤ dist x ((a ^ n) • x)) {i j : ℕ} (hij : i ≤ j) :
    l * ((j - i : ℕ) : ℝ) - B ≤ dist (fwdChain a x i) (fwdChain a x j) := by
  rw [fwdChain_dist hiso a x hij]
  exact hlox (j - i)

/-! ## The Gromov product of the ends of a chain at a vertex -/

/-- **A chain vertex sees the two ends with bounded Gromov product**: the vertex
is within `K₂` of the chord, where the product of the ends vanishes. -/
theorem gromovProduct_ends_le_of_chain {δ D l B : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (hD0 : 0 ≤ D) (hl : 0 < l)
    (hB0 : 0 ≤ B) (hgeo : IsGeodesicSpace X) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (y : ℕ → X) (N : ℕ),
      (∀ i, i < N → dist (y i) (y (i + 1)) ≤ D) →
      (∀ i j, i ≤ j → j ≤ N → l * ((j - i : ℕ) : ℝ) - B ≤ dist (y i) (y j)) →
      ∀ j, j ≤ N → gromovProduct (y 0) (y N) (y j) ≤ K := by
  obtain ⟨K₂, hK₂0, hK₂⟩ := exists_bound_chain_near_chord hδ hδ0 hD0 hl hB0
  refine ⟨K₂, hK₂0, ?_⟩
  intro y N hedge hprog j hjN
  obtain ⟨f, hf, hf0, hfL⟩ := hgeo (y 0) (y N)
  obtain ⟨t, ht, hd⟩ := hK₂ y N hedge hprog (dist (y 0) (y N)) dist_nonneg f hf hf0
    hfL j hjN
  have h0 : gromovProduct (y 0) (y N) (f t) ≤ 0 := by
    have h := gromovProduct_le_dist_of_mem_geodesic dist_nonneg ht hf (f t)
    rwa [hf0, hfL, dist_self] at h
  have h1 := dist_triangle (y 0) (f t) (y j)
  have h2 := dist_triangle (y N) (f t) (y j)
  have h3 : dist (f t) (y j) = dist (y j) (f t) := dist_comm _ _
  unfold gromovProduct at h0 ⊢
  linarith

/-! ## A discrete intermediate value lemma -/

/-- A real sequence starting at `0` with steps at most `D` that reaches `ρ`
passes within `D` above `ρ`. -/
theorem exists_index_near_of_steps {u : ℕ → ℝ} {D : ℝ} (hD : 0 ≤ D)
    (hu0 : u 0 = 0) (hstep : ∀ j, u (j + 1) ≤ u j + D) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∀ m : ℕ, ρ ≤ u m → ∃ j, j ≤ m ∧ ρ ≤ u j ∧ u j ≤ ρ + D := by
  intro m
  induction m with
  | zero =>
    intro h
    refine ⟨0, le_refl 0, h, ?_⟩
    rw [hu0]
    linarith
  | succ m ih =>
    intro h
    by_cases hm : ρ ≤ u m
    · obtain ⟨j, hj, h1, h2⟩ := ih hm
      exact ⟨j, Nat.le_succ_of_le hj, h1, h2⟩
    · push Not at hm
      refine ⟨m + 1, le_refl _, h, ?_⟩
      have := hstep m
      linarith

/-! ## The parameter estimate -/

/-- **Closeness along fellow-travelling chords is controlled by distance from
the basepoint.** -/
theorem dist_le_of_parameters {C Ka Kb T La Lb : ℝ} {x u v : X} {f q : ℝ → X}
    (hf : IsGeodesicSegment f 0 La) (hf0 : f 0 = x)
    (hq : IsGeodesicSegment q 0 Lb) (hq0 : q 0 = x)
    (hTb : T ≤ Lb)
    (hft : ∀ t : ℝ, 0 ≤ t → t ≤ T → dist (f t) (q t) ≤ C)
    {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ Set.Icc (0 : ℝ) La) (ht₂ : t₂ ∈ Set.Icc (0 : ℝ) Lb)
    (hu : dist u (f t₁) ≤ Ka) (hv : dist v (q t₂) ≤ Kb)
    (huT : dist x u + Ka ≤ T) :
    dist u v ≤ 2 * Ka + 2 * Kb + C + |dist x u - dist x v| := by
  have hp₁ : dist x (f t₁) = t₁ := by
    rw [← hf0, hf.dist_eq ⟨le_refl 0, ht₁.1.trans ht₁.2⟩ ht₁, zero_sub, abs_neg,
      abs_of_nonneg ht₁.1]
  have hp₂ : dist x (q t₂) = t₂ := by
    rw [← hq0, hq.dist_eq ⟨le_refl 0, ht₂.1.trans ht₂.2⟩ ht₂, zero_sub, abs_neg,
      abs_of_nonneg ht₂.1]
  have ht₁T : t₁ ≤ T := by
    have := dist_triangle x u (f t₁)
    linarith
  have ht₁b : t₁ ∈ Set.Icc (0 : ℝ) Lb := ⟨ht₁.1, ht₁T.trans hTb⟩
  have hfq : dist (f t₁) (q t₁) ≤ C := hft t₁ ht₁.1 ht₁T
  have hqq : dist (q t₁) (q t₂) = |t₁ - t₂| := hq.dist_eq ht₁b ht₂
  have h1 := dist_triangle u (f t₁) (q t₁)
  have h2 := dist_triangle u (q t₁) (q t₂)
  have h3 := dist_triangle u (q t₂) v
  have hv' : dist (q t₂) v = dist v (q t₂) := dist_comm _ _
  have hd₁ : |dist x u - t₁| ≤ Ka := by
    rw [abs_le]
    have e1 := dist_triangle x u (f t₁)
    have e2 := dist_triangle x (f t₁) u
    have e3 : dist (f t₁) u = dist u (f t₁) := dist_comm _ _
    constructor <;> linarith
  have hd₂ : |dist x v - t₂| ≤ Kb := by
    rw [abs_le]
    have e1 := dist_triangle x v (q t₂)
    have e2 := dist_triangle x (q t₂) v
    have e3 : dist (q t₂) v = dist v (q t₂) := dist_comm _ _
    constructor <;> linarith
  have habs : |t₁ - t₂| ≤ |dist x u - dist x v| + Ka + Kb := by
    rw [abs_le]
    have e1 := abs_le.mp hd₁
    have e2 := abs_le.mp hd₂
    have e3 := le_abs_self (dist x u - dist x v)
    have e4 := neg_abs_le (dist x u - dist x v)
    constructor <;> linarith
  linarith

/-! ## The core: a common power from forward fellow travel -/

/-- **Forward fellow travel of the two axes for a long enough time forces a
common nonzero power.**  The length `T` depends on `a`, `b`, `x` and the
acylindricity constants only. -/
theorem exists_common_zpow_of_forward_fellow_travel_of_pairStab {δ : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (hgeo : IsGeodesicSpace X)
    (hiso : IsIsometricAction G X) {C : ℝ} (hC : 0 ≤ C)
    {a b : G} {x : X} (ha : IsLoxodromic a x) (hb : IsLoxodromic b x)
    (hpair : ∀ ε : ℝ, 0 < ε → ∃ (K N : ℕ),
      (pairStab G ε x ((a ^ K) • x)).Finite ∧
        (pairStab G ε x ((a ^ K) • x)).ncard ≤ N) :
    ∃ T : ℝ, 0 < T ∧ ∀ (n m : ℕ) (f q : ℝ → X),
      IsGeodesicSegment f 0 (dist x ((a ^ n) • x)) → f 0 = x →
      f (dist x ((a ^ n) • x)) = (a ^ n) • x →
      IsGeodesicSegment q 0 (dist x ((b ^ m) • x)) → q 0 = x →
      q (dist x ((b ^ m) • x)) = (b ^ m) • x →
      T ≤ dist x ((a ^ n) • x) → T ≤ dist x ((b ^ m) • x) →
      (∀ t : ℝ, 0 ≤ t → t ≤ T → dist (f t) (q t) ≤ C) →
      ∃ p r : ℤ, p ≠ 0 ∧ r ≠ 0 ∧ a ^ p = b ^ r := by
  obtain ⟨la, hla, Ba, hBa, hlox_a⟩ := id ha
  obtain ⟨lb, hlb, Bb, hBb, hlox_b⟩ := id hb
  have hDa0 : 0 ≤ dist x (a • x) := dist_nonneg
  have hDb0 : 0 ≤ dist x (b • x) := dist_nonneg
  obtain ⟨Ka, hKa0, hKa⟩ :=
    exists_bound_chain_near_chord (D := dist x (a • x)) hδ hδ0 hDa0 hla hBa
  obtain ⟨Kb, hKb0, hKb⟩ :=
    exists_bound_chain_near_chord (D := dist x (b • x)) hδ hδ0 hDb0 hlb hBb
  obtain ⟨Ga, hGa0, hGa⟩ :=
    gromovProduct_ends_le_of_chain (D := dist x (a • x)) hδ hδ0 hDa0 hla hBa hgeo
  obtain ⟨Gb, hGb0, hGb⟩ :=
    gromovProduct_ends_le_of_chain (D := dist x (b • x)) hδ hδ0 hDb0 hlb hBb hgeo
  -- the closeness constants
  obtain ⟨ε₁, hε₁⟩ : ∃ e : ℝ, e = 2 * Ka + 2 * Kb + C + dist x (b • x) :=
    ⟨_, rfl⟩
  obtain ⟨ε₂, hε₂⟩ : ∃ e : ℝ,
      e = 2 * Ka + 2 * Kb + C + 2 * Ga + 2 * Gb + 2 * dist x (b • x) :=
    ⟨_, rfl⟩
  have hε₁0 : 0 ≤ ε₁ := by
    rw [hε₁]
    linarith
  have hε₂0 : 0 ≤ ε₂ := by
    rw [hε₂]
    linarith
  obtain ⟨ε, hε⟩ : ∃ e : ℝ, e = ε₁ + ε₂ + 1 := ⟨_, rfl⟩
  have hεpos : 0 < ε := by
    rw [hε]
    linarith
  obtain ⟨K, N, hKfin, hKcard⟩ := hpair ε hεpos
  -- spacing of the `a`-exponents
  have hτ : 0 < stableTranslation a x := stableTranslation_pos_of_isLoxodromic hiso ha
  obtain ⟨S, hS⟩ := exists_nat_gt (2 * ε₁ / stableTranslation a x)
  have hSτ : 2 * ε₁ < stableTranslation a x * S := by
    rw [div_lt_iff₀ hτ] at hS
    linarith
  have hSpos : 0 < S := by
    rcases Nat.eq_zero_or_pos S with h0 | h0
    · exfalso
      rw [h0, Nat.cast_zero, mul_zero] at hSτ
      linarith
    · exact h0
  -- the largest `a`-exponent used, and the fellow-travel length
  obtain ⟨E, hE⟩ : ∃ E : ℕ, E = S * N + K := ⟨_, rfl⟩
  have hEDa : 0 ≤ (E : ℝ) * dist x (a • x) := mul_nonneg (Nat.cast_nonneg _) hDa0
  have hJ0 : 0 ≤ ((E : ℝ) * dist x (a • x) + 2 * dist x (b • x) + 2 * Bb) / lb :=
    div_nonneg (by linarith) hlb.le
  obtain ⟨T, hT⟩ : ∃ T : ℝ,
      T = ((E : ℝ) + 1) * dist x (a • x) + Ka + 2 * dist x (b • x) + Kb + 1 +
        dist x (b • x) *
          (((E : ℝ) * dist x (a • x) + 2 * dist x (b • x) + 2 * Bb) / lb + 1) :=
    ⟨_, rfl⟩
  have hE1Da : 0 ≤ ((E : ℝ) + 1) * dist x (a • x) :=
    mul_nonneg (by positivity) hDa0
  have hE1 : ((E : ℝ) + 1) * dist x (a • x) =
      (E : ℝ) * dist x (a • x) + dist x (a • x) := by ring
  have hDbJ' : dist x (b • x) *
      (((E : ℝ) * dist x (a • x) + 2 * dist x (b • x) + 2 * Bb) / lb + 1) =
        dist x (b • x) *
          (((E : ℝ) * dist x (a • x) + 2 * dist x (b • x) + 2 * Bb) / lb) +
          dist x (b • x) := by ring
  have hDbJ : 0 ≤ dist x (b • x) *
      (((E : ℝ) * dist x (a • x) + 2 * dist x (b • x) + 2 * Bb) / lb + 1) :=
    mul_nonneg hDb0 (by linarith)
  have hT0 : 0 < T := by
    rw [hT]
    linarith
  have hTa : ((E : ℝ) + 1) * dist x (a • x) + Ka + 2 * dist x (b • x) + Kb + 1 ≤ T := by
    rw [hT]
    linarith
  have hTb : dist x (b • x) *
      (((E : ℝ) * dist x (a • x) + 2 * dist x (b • x) + 2 * Bb) / lb + 1) ≤ T := by
    rw [hT]
    linarith
  refine ⟨T, hT0, ?_⟩
  intro n m f q hf hf0 hfL hq hq0 hqL hTn hTm hft
  -- `n` and `m` are long
  have hDa_pos : 0 < dist x (a • x) := by
    have h := dist_pow_le hiso a x n
    by_contra hle
    push Not at hle
    have h0 : dist x (a • x) = 0 := le_antisymm hle hDa0
    rw [h0, mul_zero] at h
    linarith
  have hDb_pos : 0 < dist x (b • x) := by
    have h := dist_pow_le hiso b x m
    by_contra hle
    push Not at hle
    have h0 : dist x (b • x) = 0 := le_antisymm hle hDb0
    rw [h0, mul_zero] at h
    linarith
  have hnE : (E : ℝ) + 1 ≤ n := by
    have h := dist_pow_le hiso a x n
    have h2 : ((E : ℝ) + 1) * dist x (a • x) ≤ (n : ℝ) * dist x (a • x) := by
      linarith
    exact le_of_mul_le_mul_right h2 hDa_pos
  have hnE' : E + 1 ≤ n := by exact_mod_cast hnE
  have hmJ : ((E : ℝ) * dist x (a • x) + 2 * dist x (b • x) + 2 * Bb) / lb + 1 ≤ m := by
    have h := dist_pow_le hiso b x m
    have h2 : dist x (b • x) *
        (((E : ℝ) * dist x (a • x) + 2 * dist x (b • x) + 2 * Bb) / lb + 1) ≤
          dist x (b • x) * (m : ℝ) := by
      linarith
    exact le_of_mul_le_mul_left h2 hDb_pos
  -- the chains
  have hedge_a : ∀ N', ∀ i, i < N' →
      dist (fwdChain a x i) (fwdChain a x (i + 1)) ≤ dist x (a • x) :=
    fun _ i _ => le_of_eq (fwdChain_edge hiso a x i)
  have hprog_a : ∀ N', ∀ i j, i ≤ j → j ≤ N' →
      la * ((j - i : ℕ) : ℝ) - Ba ≤ dist (fwdChain a x i) (fwdChain a x j) :=
    fun _ i j hij _ => fwdChain_prog hiso hlox_a hij
  have hedge_b : ∀ N', ∀ i, i < N' →
      dist (fwdChain b x i) (fwdChain b x (i + 1)) ≤ dist x (b • x) :=
    fun _ i _ => le_of_eq (fwdChain_edge hiso b x i)
  have hprog_b : ∀ N', ∀ i j, i ≤ j → j ≤ N' →
      lb * ((j - i : ℕ) : ℝ) - Bb ≤ dist (fwdChain b x i) (fwdChain b x j) :=
    fun _ i j hij _ => fwdChain_prog hiso hlox_b hij
  have hf0' : f 0 = fwdChain a x 0 := by
    rw [fwdChain_zero]
    exact hf0
  have hq0' : q 0 = fwdChain b x 0 := by
    rw [fwdChain_zero]
    exact hq0
  -- parameters of the `a`-orbit points used stay in the fellow-travel range
  have hpa : ∀ e : ℕ, e ≤ E → dist x ((a ^ e) • x) + Ka ≤ T := by
    intro e he
    have h1 := dist_pow_le hiso a x e
    have h2 : (e : ℝ) ≤ E := by exact_mod_cast he
    have h3 := mul_le_mul_of_nonneg_right h2 hDa0
    linarith
  -- partners on the `b`-orbit
  have hstep : ∀ j : ℕ,
      dist x ((b ^ (j + 1)) • x) ≤ dist x ((b ^ j) • x) + dist x (b • x) := by
    intro j
    have h := dist_triangle x ((b ^ j) • x) ((b ^ (j + 1)) • x)
    have h2 : dist ((b ^ j) • x) ((b ^ (j + 1)) • x) = dist x (b • x) :=
      fwdChain_edge hiso b x j
    linarith
  have hu0 : dist x ((b ^ 0) • x) = 0 := by
    rw [pow_zero, one_smul, dist_self]
  have hpart : ∀ e : ℕ, ∃ j : ℕ, j ≤ m ∧ (e ≤ E →
      dist x ((a ^ e) • x) ≤ dist x ((b ^ j) • x) ∧
        dist x ((b ^ j) • x) ≤ dist x ((a ^ e) • x) + dist x (b • x)) := by
    intro e
    by_cases he : e ≤ E
    · have hρT : dist x ((a ^ e) • x) ≤ dist x ((b ^ m) • x) := by
        have h1 := dist_pow_le hiso a x e
        have h2 : (e : ℝ) ≤ E := by exact_mod_cast he
        have h3 := mul_le_mul_of_nonneg_right h2 hDa0
        linarith
      obtain ⟨j, hjm, h1, h2⟩ :=
        exists_index_near_of_steps (u := fun j => dist x ((b ^ j) • x)) hDb0 hu0
          hstep dist_nonneg m hρT
      exact ⟨j, hjm, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, Nat.zero_le m, fun h => absurd h he⟩
  choose J hJ using hpart
  -- matched at the first basepoint
  have hclose₁ : ∀ e : ℕ, e ≤ E → dist ((a ^ e) • x) ((b ^ (J e)) • x) ≤ ε₁ := by
    intro e he
    obtain ⟨hJm, hJe⟩ := hJ e
    obtain ⟨h1, h2⟩ := hJe he
    obtain ⟨t₁, ht₁, hd₁⟩ := hKa (fwdChain a x) n (hedge_a n) (hprog_a n)
      (dist x ((a ^ n) • x)) dist_nonneg f hf hf0' hfL e (by omega)
    obtain ⟨t₂, ht₂, hd₂⟩ := hKb (fwdChain b x) m (hedge_b m) (hprog_b m)
      (dist x ((b ^ m) • x)) dist_nonneg q hq hq0' hqL (J e) hJm
    have hd₁' : dist ((a ^ e) • x) (f t₁) ≤ Ka := hd₁
    have hd₂' : dist ((b ^ (J e)) • x) (q t₂) ≤ Kb := hd₂
    have hpl := dist_le_of_parameters hf hf0 hq hq0 hTm hft ht₁ ht₂ hd₁' hd₂'
      (hpa e he)
    have habs : |dist x ((a ^ e) • x) - dist x ((b ^ (J e)) • x)| ≤ dist x (b • x) := by
      rw [abs_le]
      constructor <;> linarith
    rw [hε₁]
    linarith
  -- the partner exponents are bounded
  have hJb : ∀ e', e' ≤ E →
      lb * (J e' : ℝ) - Bb ≤ (e' : ℝ) * dist x (a • x) + dist x (b • x) := by
    intro e' he'
    have h := hlox_b (J e')
    have h3 := (hJ e').2 he'
    have h4 := dist_pow_le hiso a x e'
    linarith [h3.2]
  -- matched at the second basepoint
  have hclose₂ : ∀ e : ℕ, e + K ≤ E →
      dist ((a ^ e) • ((a ^ K) • x)) ((b ^ (J e)) • ((a ^ K) • x)) ≤ ε := by
    intro e heK
    have heE : e ≤ E := by omega
    have hKE : K ≤ E := by omega
    have h1 : (a ^ e) • ((a ^ K) • x) = (a ^ (e + K)) • x := by
      rw [← mul_smul, ← pow_add]
    have h2 : dist ((b ^ (J e)) • ((a ^ K) • x)) ((b ^ (J e + J K)) • x) ≤ ε₁ := by
      rw [pow_add, mul_smul, hiso]
      exact hclose₁ K hKE
    have hsum : ((J e + J K : ℕ) : ℝ) ≤
        ((E : ℝ) * dist x (a • x) + 2 * dist x (b • x) + 2 * Bb) / lb := by
      rw [le_div_iff₀ hlb]
      have h5 := hJb e heE
      have h6 := hJb K hKE
      have h7 : (e : ℝ) * dist x (a • x) + (K : ℝ) * dist x (a • x) ≤
          (E : ℝ) * dist x (a • x) := by
        rw [← add_mul]
        have : ((e : ℝ) + K) ≤ E := by exact_mod_cast heK
        exact mul_le_mul_of_nonneg_right this hDa0
      push_cast
      rw [add_mul]
      linarith
    have hsum' : J e + J K ≤ m := by
      have : ((J e + J K : ℕ) : ℝ) ≤ m := by linarith
      exact_mod_cast this
    obtain ⟨t₁, ht₁, hd₁⟩ := hKa (fwdChain a x) n (hedge_a n) (hprog_a n)
      (dist x ((a ^ n) • x)) dist_nonneg f hf hf0' hfL (e + K) (by omega)
    obtain ⟨t₂, ht₂, hd₂⟩ := hKb (fwdChain b x) m (hedge_b m) (hprog_b m)
      (dist x ((b ^ m) • x)) dist_nonneg q hq hq0' hqL (J e + J K) hsum'
    have hd₁' : dist ((a ^ (e + K)) • x) (f t₁) ≤ Ka := hd₁
    have hd₂' : dist ((b ^ (J e + J K)) • x) (q t₂) ≤ Kb := hd₂
    have hpl := dist_le_of_parameters hf hf0 hq hq0 hTm hft ht₁ ht₂ hd₁' hd₂'
      (hpa (e + K) heK)
    -- the two-sided estimates
    have hga := hGa (fwdChain a x) (e + K) (hedge_a (e + K)) (hprog_a (e + K)) e
      (Nat.le_add_right e K)
    have hgb := hGb (fwdChain b x) (J e + J K) (hedge_b (J e + J K))
      (hprog_b (J e + J K)) (J e) (Nat.le_add_right _ _)
    have hda : dist (fwdChain a x e) (fwdChain a x (e + K)) = dist x ((a ^ K) • x) := by
      rw [fwdChain_dist hiso a x (Nat.le_add_right e K), Nat.add_sub_cancel_left]
    have hdb : dist (fwdChain b x (J e)) (fwdChain b x (J e + J K)) =
        dist x ((b ^ (J K)) • x) := by
      rw [fwdChain_dist hiso b x (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    rw [fwdChain_zero] at hga hgb
    unfold gromovProduct at hga hgb
    unfold fwdChain at hga hgb hda hdb
    rw [dist_comm ((a ^ (e + K)) • x) ((a ^ e) • x)] at hga
    rw [dist_comm ((b ^ (J e + J K)) • x) ((b ^ (J e)) • x)] at hgb
    have hta := dist_triangle x ((a ^ e) • x) ((a ^ (e + K)) • x)
    have htb := dist_triangle x ((b ^ (J e)) • x) ((b ^ (J e + J K)) • x)
    obtain ⟨hpe1, hpe2⟩ := (hJ e).2 heE
    obtain ⟨hpK1, hpK2⟩ := (hJ K).2 hKE
    have habs : |dist x ((a ^ (e + K)) • x) - dist x ((b ^ (J e + J K)) • x)| ≤
        2 * Ga + 2 * Gb + 2 * dist x (b • x) := by
      rw [abs_le]
      constructor <;> linarith
    have h3 : dist ((a ^ (e + K)) • x) ((b ^ (J e + J K)) • x) ≤ ε₂ := by
      rw [hε₂]
      linarith
    rw [h1]
    have h4 := dist_triangle ((a ^ (e + K)) • x) ((b ^ (J e + J K)) • x)
      ((b ^ (J e)) • ((a ^ K) • x))
    have h5 : dist ((b ^ (J e + J K)) • x) ((b ^ (J e)) • ((a ^ K) • x)) =
        dist ((b ^ (J e)) • ((a ^ K) • x)) ((b ^ (J e + J K)) • x) := dist_comm _ _
    rw [hε]
    linarith
  -- the spaced family of `a`-exponents
  obtain ⟨ef, hef⟩ : ∃ ef : Fin (N + 1) → ℕ, ∀ i, ef i = S * i.val := ⟨_, fun _ => rfl⟩
  have hefE : ∀ i, ef i ≤ S * N := by
    intro i
    rw [hef]
    exact Nat.mul_le_mul_left S (Nat.lt_succ_iff.mp i.isLt)
  have hinj₁ : Function.Injective (fun i : Fin (N + 1) => ((ef i : ℕ) : ℤ)) := by
    intro i j h
    have h' : ((ef i : ℕ) : ℤ) = ((ef j : ℕ) : ℤ) := h
    have h1 : ef i = ef j := by exact_mod_cast h'
    rw [hef, hef] at h1
    exact Fin.ext (Nat.eq_of_mul_eq_mul_left hSpos h1)
  have hinj₂ : Function.Injective (fun i : Fin (N + 1) => ((J (ef i) : ℕ) : ℤ)) := by
    intro i j h
    by_contra hne
    have hJeq : J (ef i) = J (ef j) := by
      have h' : ((J (ef i) : ℕ) : ℤ) = ((J (ef j) : ℕ) : ℤ) := h
      exact_mod_cast h'
    have hci := hclose₁ (ef i) (by have := hefE i; omega)
    have hcj := hclose₁ (ef j) (by have := hefE j; omega)
    rw [hJeq] at hci
    have htri := dist_triangle ((a ^ ef i) • x) ((b ^ (J (ef j))) • x) ((a ^ ef j) • x)
    have hcj' : dist ((b ^ (J (ef j))) • x) ((a ^ ef j) • x) =
        dist ((a ^ ef j) • x) ((b ^ (J (ef j))) • x) := dist_comm _ _
    have hne' : ((j.val : ℤ) - i.val) ≠ 0 := by
      intro h0
      exact hne (Fin.ext (by omega))
    have h1 : (S : ℤ) ≤ |((ef j : ℕ) : ℤ) - ((ef i : ℕ) : ℤ)| := by
      rw [hef, hef]
      push_cast
      rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (S : ℤ))]
      exact le_mul_of_one_le_right (by positivity) (Int.one_le_abs hne')
    have h2 : (S : ℝ) ≤ |((((ef j : ℕ) : ℤ) - ((ef i : ℕ) : ℤ) : ℤ) : ℝ)| := by
      exact_mod_cast h1
    have h3 := mul_le_dist_zpow hiso a x (((ef j : ℕ) : ℤ) - ((ef i : ℕ) : ℤ))
    have h4 := dist_zpow_orbit hiso a x ((ef i : ℕ) : ℤ) ((ef j : ℕ) : ℤ)
    rw [zpow_natCast, zpow_natCast] at h4
    have h5 := mul_le_mul_of_nonneg_left h2 hτ.le
    linarith
  have hpairs : ∀ i : Fin (N + 1),
      dist ((a ^ ((ef i : ℕ) : ℤ)) • x) ((b ^ ((J (ef i) : ℕ) : ℤ)) • x) ≤ ε ∧
        dist ((a ^ ((ef i : ℕ) : ℤ)) • ((a ^ K) • x))
          ((b ^ ((J (ef i) : ℕ) : ℤ)) • ((a ^ K) • x)) ≤ ε := by
    intro i
    have heE : ef i ≤ E := by
      have := hefE i
      omega
    have heKE : ef i + K ≤ E := by
      have := hefE i
      omega
    rw [zpow_natCast, zpow_natCast]
    refine ⟨?_, hclose₂ (ef i) heKE⟩
    have := hclose₁ (ef i) heE
    rw [hε]
    linarith
  obtain ⟨i, j, -, hp, hr, hpow⟩ :=
    exists_common_zpow_of_pairStab_finite hiso hKfin hKcard a b
      (fun i => ((ef i : ℕ) : ℤ)) (fun i => ((J (ef i) : ℕ) : ℤ))
      hinj₁ hinj₂ hpairs
  exact ⟨_, _, hp, hr, hpow⟩

/-- The existing acylindrical form, recovered from the finite-pair-stabilizer
core. -/
theorem exists_common_zpow_of_forward_fellow_travel {δ : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (hgeo : IsGeodesicSpace X)
    (hiso : IsIsometricAction G X) (hacy : IsAcylindrical G X)
    {a b : G} {x : X} (ha : IsLoxodromic a x) (hb : IsLoxodromic b x) :
    ∃ T : ℝ, 0 < T ∧ ∀ (n m : ℕ) (f q : ℝ → X),
      IsGeodesicSegment f 0 (dist x ((a ^ n) • x)) → f 0 = x →
      f (dist x ((a ^ n) • x)) = (a ^ n) • x →
      IsGeodesicSegment q 0 (dist x ((b ^ m) • x)) → q 0 = x →
      q (dist x ((b ^ m) • x)) = (b ^ m) • x →
      T ≤ dist x ((a ^ n) • x) → T ≤ dist x ((b ^ m) • x) →
      (∀ t : ℝ, 0 ≤ t → t ≤ T → dist (f t) (q t) ≤ 4 * δ) →
      ∃ p r : ℤ, p ≠ 0 ∧ r ≠ 0 ∧ a ^ p = b ^ r := by
  apply exists_common_zpow_of_forward_fellow_travel_of_pairStab
    hδ hδ0 hgeo hiso (C := 4 * δ) (mul_nonneg (by norm_num) hδ0) ha hb
  intro ε hε
  obtain ⟨R, N, hRN⟩ := hacy ε hε
  obtain ⟨la, hla, Ba, -, hlox_a⟩ := id ha
  obtain ⟨K, hK⟩ := exists_nat_gt ((R + Ba) / la)
  have hR : R ≤ dist x ((a ^ K) • x) := by
    rw [div_lt_iff₀ hla] at hK
    have hlow := hlox_a K
    linarith
  obtain ⟨hfin, hcard⟩ := hRN x ((a ^ K) • x) hR
  exact ⟨K, N, hfin, hcard⟩

/-- **The bounded WPD long-fellow-travel form used in DGO Lemma 6.7.**  Global
acylindricity is unnecessary: WPD for the first loxodromic element supplies
the one finite pair stabilizer consumed by the Morse/pigeonhole proof. -/
theorem exists_common_zpow_of_forward_fellow_travel_of_wpd_bound {δ : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (hgeo : IsGeodesicSpace X)
    (hiso : IsIsometricAction G X) {C : ℝ} (hC : 0 ≤ C)
    {a b : G} {x : X} (ha : IsLoxodromic a x) (hb : IsLoxodromic b x)
    (hwpd : IsWPDAt a x) :
    ∃ T : ℝ, 0 < T ∧ ∀ (n m : ℕ) (f q : ℝ → X),
      IsGeodesicSegment f 0 (dist x ((a ^ n) • x)) → f 0 = x →
      f (dist x ((a ^ n) • x)) = (a ^ n) • x →
      IsGeodesicSegment q 0 (dist x ((b ^ m) • x)) → q 0 = x →
      q (dist x ((b ^ m) • x)) = (b ^ m) • x →
      T ≤ dist x ((a ^ n) • x) → T ≤ dist x ((b ^ m) • x) →
      (∀ t : ℝ, 0 ≤ t → t ≤ T → dist (f t) (q t) ≤ C) →
      ∃ p r : ℤ, p ≠ 0 ∧ r ≠ 0 ∧ a ^ p = b ^ r := by
  apply exists_common_zpow_of_forward_fellow_travel_of_pairStab
    hδ hδ0 hgeo hiso hC ha hb
  intro ε hε
  obtain ⟨K, hKfin⟩ := hwpd ε hε.le
  exact ⟨K, (pairStab G ε x ((a ^ K) • x)).ncard, hKfin, le_rfl⟩

/-- The original `4δ` specialization of the WPD fellow-travel theorem. -/
theorem exists_common_zpow_of_forward_fellow_travel_of_wpd {δ : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (hgeo : IsGeodesicSpace X)
    (hiso : IsIsometricAction G X)
    {a b : G} {x : X} (ha : IsLoxodromic a x) (hb : IsLoxodromic b x)
    (hwpd : IsWPDAt a x) :
    ∃ T : ℝ, 0 < T ∧ ∀ (n m : ℕ) (f q : ℝ → X),
      IsGeodesicSegment f 0 (dist x ((a ^ n) • x)) → f 0 = x →
      f (dist x ((a ^ n) • x)) = (a ^ n) • x →
      IsGeodesicSegment q 0 (dist x ((b ^ m) • x)) → q 0 = x →
      q (dist x ((b ^ m) • x)) = (b ^ m) • x →
      T ≤ dist x ((a ^ n) • x) → T ≤ dist x ((b ^ m) • x) →
      (∀ t : ℝ, 0 ≤ t → t ≤ T → dist (f t) (q t) ≤ 4 * δ) →
      ∃ p r : ℤ, p ≠ 0 ∧ r ≠ 0 ∧ a ^ p = b ^ r :=
  exists_common_zpow_of_forward_fellow_travel_of_wpd_bound
    hδ hδ0 hgeo hiso (mul_nonneg (by norm_num) hδ0) ha hb hwpd

/-! ## Signs -/

/-- An integer power is a natural power of the element or of its inverse. -/
theorem zpow_eq_pow_toNat_or_inv (a : G) (n : ℤ) :
    (0 ≤ n ∧ a ^ n = a ^ n.toNat) ∨ (n < 0 ∧ a ^ n = a⁻¹ ^ (-n).toNat) := by
  rcases le_or_gt 0 n with h | h
  · left
    refine ⟨h, ?_⟩
    rw [← zpow_natCast, Int.toNat_of_nonneg h]
  · right
    refine ⟨h, ?_⟩
    rw [← zpow_natCast, Int.toNat_of_nonneg (by linarith), inv_zpow', neg_neg]

/-! ## The theorem -/

/-- **`IndependentOfNoCommonZpow` holds in every geodesic hyperbolic space with
an acylindrical isometric action** (Osin, Lemma 6.5 and Corollary 6.6). -/
theorem independentOfNoCommonZpow_of_geodesic {δ : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (hgeo : IsGeodesicSpace X)
    (hiso : IsIsometricAction G X) (hacy : IsAcylindrical G X) (x : X) :
    Elementary.IndependentOfNoCommonZpow G x := by
  intro a b ha hb hnp
  by_contra hnind
  have ha' := isLoxodromic_inv hiso ha
  have hb' := isLoxodromic_inv hiso hb
  obtain ⟨T₁, hT₁, hc₁⟩ :=
    exists_common_zpow_of_forward_fellow_travel hδ hδ0 hgeo hiso hacy ha hb
  obtain ⟨T₂, hT₂, hc₂⟩ :=
    exists_common_zpow_of_forward_fellow_travel hδ hδ0 hgeo hiso hacy ha' hb
  obtain ⟨T₃, hT₃, hc₃⟩ :=
    exists_common_zpow_of_forward_fellow_travel hδ hδ0 hgeo hiso hacy ha hb'
  obtain ⟨T₄, hT₄, hc₄⟩ :=
    exists_common_zpow_of_forward_fellow_travel hδ hδ0 hgeo hiso hacy ha' hb'
  obtain ⟨n, m, f, q, -, -, hf, hf0, hfL, hq, hq0, hqL, hTn, hTm, hft⟩ :=
    exists_long_fellow_geodesics_of_not_independent hδ hδ0 hgeo hnind
      (T₁ + T₂ + T₃ + T₄) (by linarith)
  rcases zpow_eq_pow_toNat_or_inv a n with ⟨-, hae⟩ | ⟨-, hae⟩ <;>
    rcases zpow_eq_pow_toNat_or_inv b m with ⟨-, hbe⟩ | ⟨-, hbe⟩ <;>
    rw [hae] at hf hfL hTn <;> rw [hbe] at hq hqL hTm
  · obtain ⟨p, r, hp, hr, hpow⟩ := hc₁ _ _ f q hf hf0 hfL hq hq0 hqL (by linarith)
      (by linarith) (fun t ht0 ht => hft t ht0 (by linarith))
    exact hnp p r hp hr hpow
  · obtain ⟨p, r, hp, hr, hpow⟩ := hc₃ _ _ f q hf hf0 hfL hq hq0 hqL (by linarith)
      (by linarith) (fun t ht0 ht => hft t ht0 (by linarith))
    rw [inv_zpow'] at hpow
    exact hnp p (-r) hp (neg_ne_zero.mpr hr) hpow
  · obtain ⟨p, r, hp, hr, hpow⟩ := hc₂ _ _ f q hf hf0 hfL hq hq0 hqL (by linarith)
      (by linarith) (fun t ht0 ht => hft t ht0 (by linarith))
    rw [inv_zpow'] at hpow
    exact hnp (-p) r (neg_ne_zero.mpr hp) hr hpow
  · obtain ⟨p, r, hp, hr, hpow⟩ := hc₄ _ _ f q hf hf0 hfL hq hq0 hqL (by linarith)
      (by linarith) (fun t ht0 ht => hft t ht0 (by linarith))
    rw [inv_zpow', inv_zpow'] at hpow
    exact hnp (-p) (-r) (neg_ne_zero.mpr hp) (neg_ne_zero.mpr hr) hpow

/-- **`CommonPowerInGeodesicSpace`**, the residual of the axis dichotomy, is a
theorem. -/
theorem commonPowerInGeodesicSpace :
    Manuscript.NonMF.AxisDichotomyRoute.CommonPowerInGeodesicSpace.{u, v} := by
  intro G _ Y _ _ δ hδ hδ0 hgeo hiso hacy g h y hg hh hnind
  by_contra hnp
  push Not at hnp
  exact hnind (independentOfNoCommonZpow_of_geodesic hδ hδ0 hgeo hiso hacy y g h hg hh
    hnp)

/-! ## At Hull's Cayley graph -/

section Cayley

open GroupApproximation.Manuscript.NonMF.TorsionFree

/-- **The common-power residual of Osin's Lemma 7.1 is discharged at
`Γ(G,A)`.** -/
theorem independentOfNoCommonZpow_cayley {G : Type u} [Group G]
    (A : HullGeneratingSet G) :
    Elementary.IndependentOfNoCommonZpow G (Cayley.base A.alphabet) := by
  obtain ⟨M⟩ := CayleyGeodesicModel.hasGeodesicModel_of_hullGeneratingSet A
  have hacyW : IsAcylindrical G M.W :=
    isAcylindrical_of_additiveDistortion_of_dense M.distortion_nonneg
      M.hasAdditiveDistortion M.hasDenseImage M.equivariant M.isometric
      A.acylindrical
  exact Elementary.independentOfNoCommonZpow_of_map M.distortion_nonneg
    M.hasAdditiveDistortion M.equivariant
    (independentOfNoCommonZpow_of_geodesic M.hyperbolic M.delta_nonneg M.geodesic
      M.isometric hacyW _)

end Cayley

end ElementaryMorse
end GGT
end GroupApproximation
