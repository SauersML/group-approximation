import GroupApproximation.GGT.ElementaryIndependence

/-!
# Bowditch's dichotomy: an acylindrical action has no parabolic elements

`Elementary.EscapingIsLoxodromic` --- an element whose positive power orbit
escapes every bounded set is loxodromic --- is proved here for every geodesic
hyperbolic space carrying an acylindrical isometric action, and then transported
to Hull's Cayley graph through the geodesic realisation, exactly as
`GGT.ElementaryIndependence` transports the common-power theorem.

This is Osin, *Acylindrically hyperbolic groups*, Theorem 1.1, over Bowditch,
*Tight geodesics in the curve complex*, Lemma 2.2.

## The argument

Suppose `c` escapes at `x` and is not loxodromic.  Write `dₙ = d(x, cⁿ x)`.
Loxodromy is equivalent to a positive stable translation length
(`isLoxodromic_iff_stableTranslation_pos`), so `τ(c) = 0`, and by Fekete
(`tendsto_stableTranslation`) `dₙ / n → 0`.  Escape says `dₙ → ∞`.  Both are
used, and so is acylindricity: without it the statement is false, a parabolic
isometry of the hyperbolic plane being the counterexample recorded in the
docstring of `GGT.ElementaryBowditch`.

**The geometric step.**  Let `z` be the midpoint of a geodesic `[x, cᵐ x]` and
let `k = cʲ`.  Then `k` moves `z` by at most `8δ` plus `|dₘ − d_{m+j}|`:

* a geodesic `[x, cᵐ x]` and a geodesic `[x, c^{m+j} x]` leave `x` together, so
  their points at distance `dₘ/2` from `x` are `4δ`-close;
* the two geodesics `[c^{m+j} x, x]` and `[c^{m+j} x, cʲ x]` leave `c^{m+j} x`
  together, and `cʲ z` is the point of the second at distance `dₘ/2` from
  `c^{m+j} x`, so it is `4δ`-close to the point of `[x, c^{m+j} x]` at distance
  `d_{m+j} − dₘ/2` from `x`;
* those two points of `[x, c^{m+j} x]` are `|dₘ − d_{m+j}|` apart.

Both fellow-travelling steps need `dⱼ ≤ d_{m+j}`, which holds once `m` is far
enough out.  This is `dist_smul_midpoint_le`, and it is the only place
hyperbolicity and geodesicity are used.

**The counting step.**  Fix `ε = 8δ + 1` and let `R, N` be the acylindricity
constants for `ε`.  Because `dₙ/n → 0` there is, for every `η > 0`, a constant
`M` with `dₙ ≤ M + η n` (`exists_sublinear_dist_bound`).  Take
`η ≤ 1 / (4(N+1))` and a window length `V > 2(2M+1)(N+1)`.  Inside any window
`Q, …, Q+V` the numbers `dₙ` vary by at most `S = M + ηV`, so they fall into at
most `2S + 1` unit boxes; since `(2S+1)(N+1) < V`, some box holds `N + 2` of the
`V` indices (`exists_large_fiber`).  Writing `i₀` for the least of them,
`m = Q + i₀` and the exponents `j = i − i₀`, we get `N + 2` distinct powers `cʲ`
with `|dₘ − d_{m+j}| ≤ 1`, hence `N + 2` distinct elements moving the midpoint
`z` of `[x, cᵐ x]` by at most `ε`.

**The second point.**  Powers of `c` commute, so `cʲ` moves `c^A z` exactly as
far as it moves `z`, for every `A`; and `d(z, c^A z) ≥ d_A − dₘ`, which exceeds
`R` once `d_A` is large enough --- escape again.  So `N + 2` distinct elements
move two points at distance at least `R` by at most `ε`, and acylindricity
allows at most `N`.

Choosing `Q` after `V` --- large enough that `dₙ ≥ S + 3` on the window --- is
what makes the argument non-circular: the exponents `j` are bounded by `V`,
which is fixed before `Q`, so `dⱼ ≤ S` is beaten by `dₘ` with room to spare.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.HullGeometry

universe u v

/-! ## A finite pigeonhole -/

/-- **Finite pigeonhole.**  If every fibre of a map `Finset.range V → Finset.range K`
has at most `n` elements, then `V ≤ K * n`.  Contrapositively, `K * n < V`
produces a fibre with more than `n` elements. -/
theorem exists_large_fiber {V K n : ℕ} (f : ℕ → ℕ)
    (hf : ∀ i, i < V → f i < K) (hlt : K * n < V) :
    ∃ y : ℕ, n < (Finset.filter (fun i => f i = y) (Finset.range V)).card := by
  by_contra hcon
  push_neg at hcon
  have hmaps : ∀ i ∈ Finset.range V, f i ∈ Finset.range K := fun i hi =>
    Finset.mem_range.mpr (hf i (Finset.mem_range.mp hi))
  have hsum := Finset.card_eq_sum_card_fiberwise hmaps
  rw [Finset.card_range] at hsum
  have hbound : ∑ y ∈ Finset.range K,
      (Finset.filter (fun i => f i = y) (Finset.range V)).card
        ≤ ∑ _y ∈ Finset.range K, n :=
    Finset.sum_le_sum fun y _ => hcon y
  have hconst : ∑ _y ∈ Finset.range K, n = (Finset.range K).card * n :=
    Finset.sum_const_nat (fun _ _ => rfl)
  rw [hconst, Finset.card_range] at hbound
  have hle : V ≤ K * n := by rw [hsum]; exact hbound
  exact absurd hle (not_le.mpr hlt)

section Action

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X] [MulAction G X]

/-! ## Two consequences of zero translation length -/

/-- **Sublinear displacement.**  An element of zero stable translation length
satisfies `d(x, cⁿ x) ≤ M + η n` for every `η > 0`, with `M` depending on `η`.
Fekete's theorem gives the bound beyond a threshold, and subadditivity of the
displacement gives a constant below it. -/
theorem exists_sublinear_dist_bound (hiso : IsIsometricAction G X) {c : G} {x : X}
    (hτ : stableTranslation c x = 0) {η : ℝ} (hη : 0 < η) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, dist x ((c ^ n) • x) ≤ M + η * n := by
  have htend := tendsto_stableTranslation hiso c x
  rw [hτ] at htend
  have hev := htend.eventually_lt_const hη
  rw [Filter.eventually_atTop] at hev
  obtain ⟨J, hJ⟩ := hev
  refine ⟨(J : ℝ) * dist x (c • x), mul_nonneg (Nat.cast_nonneg J) dist_nonneg, ?_⟩
  intro n
  have hM : (0:ℝ) ≤ (J : ℝ) * dist x (c • x) :=
    mul_nonneg (Nat.cast_nonneg J) dist_nonneg
  rcases Nat.eq_zero_or_pos n with rfl | hnpos
  · have h0 : dist x ((c ^ (0:ℕ)) • x) = 0 := by
      rw [pow_zero, one_smul, dist_self]
    rw [h0]
    simp only [Nat.cast_zero, mul_zero]
    linarith
  · by_cases hnJ : J ≤ n
    · have hnR : (0:ℝ) < (n : ℝ) := by exact_mod_cast hnpos
      have h : dist x ((c ^ n) • x) / (n : ℝ) < η := hJ n hnJ
      rw [div_lt_iff₀ hnR] at h
      linarith
    · push_neg at hnJ
      have hle := dist_pow_le hiso c x n
      have hnJ' : (n : ℝ) ≤ (J : ℝ) := by exact_mod_cast hnJ.le
      have hd1 : (0:ℝ) ≤ dist x (c • x) := dist_nonneg
      have hηn : (0:ℝ) ≤ η * (n : ℝ) := mul_nonneg hη.le (Nat.cast_nonneg n)
      have hmono : (n : ℝ) * dist x (c • x) ≤ (J : ℝ) * dist x (c • x) :=
        mul_le_mul_of_nonneg_right hnJ' hd1
      linarith

/-- An escaping element has infinite order: a finite order would return its
orbit to the basepoint at arbitrarily large exponents. -/
theorem not_isOfFinOrder_of_isEscaping {c : G} {x : X} (hc : IsEscaping c x) :
    ¬ IsOfFinOrder c := by
  intro hfin
  obtain ⟨q, hq, hqpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
  have hev := hc.eventually_ge_atTop (1:ℝ)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨K, hK⟩ := hev
  have hK1 : K ≤ q * (K + 1) :=
    calc K ≤ K + 1 := Nat.le_succ K
      _ = 1 * (K + 1) := (one_mul _).symm
      _ ≤ q * (K + 1) := Nat.mul_le_mul hq (Nat.le_refl (K + 1))
  have hzero : dist x ((c ^ (q * (K + 1))) • x) = 0 := by
    rw [pow_mul, hqpow, one_pow, one_smul, dist_self]
  have hge : (1:ℝ) ≤ dist x ((c ^ (q * (K + 1))) • x) := hK (q * (K + 1)) hK1
  rw [hzero] at hge
  linarith

/-! ## The geometric estimate -/

/-- **The midpoint of an orbit segment moves by `8δ` plus the change in the
distance to the basepoint.**

Let `C` be a point, `p` a geodesic from `x` to `C` and `k` an isometry.  Under
the three comparisons below, `k` moves the midpoint of `p` by at most
`8δ + |d(x,C) − d(x, k C)|`.

Two applications of the fellow-travelling lemma
`dist_le_four_delta_of_le_gromovProduct`: one at `x`, comparing `[x, C]` with
`[x, k C]`, and one at `k C`, comparing `[k C, x]` with `[k C, k x]`.  The
midpoint of `[x, C]` lands within `4δ` of the point of `[x, k C]` at parameter
`d(x,C)/2`, and `k` of that midpoint lands within `4δ` of the point of
`[x, k C]` at parameter `d(x, k C) − d(x,C)/2`; the two parameters differ by
`|d(x,C) − d(x, k C)|`. -/
theorem dist_smul_midpoint_le {δ : ℝ} (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ)
    (hgeo : IsGeodesicSpace X) (hiso : IsIsometricAction G X) (k : G) {x C : X}
    {p : ℝ → X} (hp : IsGeodesicSegment p 0 (dist x C)) (hp0 : p 0 = x)
    (hp1 : p (dist x C) = C)
    (h1 : dist C (k • C) ≤ dist x (k • C))
    (h2 : dist x (k • x) ≤ dist x (k • C))
    (h3 : dist x C / 2 ≤ dist x (k • C)) :
    dist (p (dist x C / 2)) (k • p (dist x C / 2))
      ≤ 8 * δ + |dist x C - dist x (k • C)| := by
  obtain ⟨r, hr, hr0, hr1⟩ := hgeo x (k • C)
  have ha0 : (0:ℝ) ≤ dist x C := dist_nonneg
  have hb0 : (0:ℝ) ≤ dist x (k • C) := dist_nonneg
  -- the first comparison, at `x`
  have hstep1 : dist (p (dist x C / 2)) (r (dist x C / 2)) ≤ 4 * δ := by
    refine dist_le_four_delta_of_le_gromovProduct hδ hδ0 hp hp0 hp1 hr hr0 hr1
      ?_ ?_ ?_ ?_
    · linarith
    · linarith
    · exact h3
    · have hCx : dist C x = dist x C := dist_comm _ _
      have hDx : dist (k • C) x = dist x (k • C) := dist_comm _ _
      simp only [gromovProduct, hCx, hDx]
      linarith
  -- the reversed geodesics out of `k • C`
  have hDx : dist (k • C) x = dist x (k • C) := dist_comm _ _
  have hDB : dist (k • C) (k • x) = dist x C := by
    rw [hiso k C x, dist_comm C x]
  have hr'geo : IsGeodesicSegment (fun t => r (dist x (k • C) - t)) 0
      (dist (k • C) x) := by
    rw [hDx]
    exact hr.reverse
  have hr'0 : (fun t => r (dist x (k • C) - t)) 0 = k • C := by
    show r (dist x (k • C) - 0) = k • C
    rw [sub_zero, hr1]
  have hr'1 : (fun t => r (dist x (k • C) - t)) (dist (k • C) x) = x := by
    show r (dist x (k • C) - dist (k • C) x) = x
    rw [hDx, sub_self, hr0]
  have hkp : IsGeodesicSegment (fun t => k • p t) 0 (dist x C) := hp.smul hiso k
  have hq'geo : IsGeodesicSegment (fun t => k • p (dist x C - t)) 0
      (dist (k • C) (k • x)) := by
    rw [hDB]
    exact hkp.reverse
  have hq'0 : (fun t => k • p (dist x C - t)) 0 = k • C := by
    show k • p (dist x C - 0) = k • C
    rw [sub_zero, hp1]
  have hq'1 : (fun t => k • p (dist x C - t)) (dist (k • C) (k • x)) = k • x := by
    show k • p (dist x C - dist (k • C) (k • x)) = k • x
    rw [hDB, sub_self, hp0]
  -- the second comparison, at `k • C`
  have hstep2 : dist (r (dist x (k • C) - dist x C / 2))
      (k • p (dist x C - dist x C / 2)) ≤ 4 * δ := by
    refine dist_le_four_delta_of_le_gromovProduct hδ hδ0 hr'geo hr'0 hr'1
      hq'geo hq'0 hq'1 ?_ ?_ ?_ ?_
    · linarith
    · rw [hDx]; linarith
    · rw [hDB]; linarith
    · have hBD : dist (k • x) (k • C) = dist x C := hiso k x C
      simp only [gromovProduct, hBD]
      linarith
  have harg : dist x C - dist x C / 2 = dist x C / 2 := by ring
  rw [harg] at hstep2
  -- the two parameters on the geodesic from `x` to `k • C`
  have hmid : dist (r (dist x C / 2)) (r (dist x (k • C) - dist x C / 2))
      = |dist x C / 2 - (dist x (k • C) - dist x C / 2)| :=
    hr (dist x C / 2) ⟨by linarith, by linarith⟩
      (dist x (k • C) - dist x C / 2) ⟨by linarith, by linarith⟩
  have habs : |dist x C / 2 - (dist x (k • C) - dist x C / 2)|
      = |dist x C - dist x (k • C)| := by
    congr 1
    ring
  rw [habs] at hmid
  have htri1 := dist_triangle (p (dist x C / 2)) (r (dist x C / 2))
    (r (dist x (k • C) - dist x C / 2))
  have htri2 := dist_triangle (p (dist x C / 2))
    (r (dist x (k • C) - dist x C / 2)) (k • p (dist x C / 2))
  linarith

/-! ## Bowditch's dichotomy -/

/-- **Bowditch's dichotomy** (Osin, Theorem 1.1, over Bowditch, Lemma 2.2).
Under an acylindrical isometric action on a geodesic hyperbolic space, an
element whose orbit escapes every bounded set is loxodromic: there are no
parabolics.  The argument is the one described in the module docstring. -/
theorem escapingIsLoxodromic_of_geodesic {δ : ℝ} (hδ : IsHyperbolicSpace δ X)
    (hδ0 : 0 ≤ δ) (hgeo : IsGeodesicSpace X) (hiso : IsIsometricAction G X)
    (hacy : IsAcylindrical G X) (x : X) :
    Elementary.EscapingIsLoxodromic G x := by
  intro c hc
  by_contra hnlox
  -- zero stable translation length
  have hτ : stableTranslation c x = 0 := by
    by_contra hne
    exact hnlox (isLoxodromic_of_pos_stableTranslation c x
      (lt_of_le_of_ne (stableTranslation_nonneg c x) (Ne.symm hne)))
  -- the acylindricity constants for `ε = 8δ + 1`
  obtain ⟨R, N, hRN⟩ := hacy (8 * δ + 1) (by linarith)
  -- a sublinear displacement bound with a small enough slope
  obtain ⟨η, hη0, hηN⟩ : ∃ η : ℝ, 0 < η ∧ 4 * η * ((N : ℝ) + 1) ≤ 1 := by
    have hpos : (0:ℝ) < 4 * ((N : ℝ) + 1) := by positivity
    refine ⟨(4 * ((N : ℝ) + 1))⁻¹, by positivity, le_of_eq ?_⟩
    have heq : 4 * (4 * ((N : ℝ) + 1))⁻¹ * ((N : ℝ) + 1)
        = (4 * ((N : ℝ) + 1)) * (4 * ((N : ℝ) + 1))⁻¹ := by ring
    rw [heq, mul_inv_cancel₀ (ne_of_gt hpos)]
  obtain ⟨M, hM0, hMb⟩ := exists_sublinear_dist_bound hiso hτ hη0
  -- the window length, the spread on a window, and the number of boxes
  obtain ⟨V, hV⟩ := exists_nat_gt (2 * (2 * M + 1) * ((N : ℝ) + 1))
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = M + η * (V : ℝ) := ⟨_, rfl⟩
  have hVnn : (0:ℝ) ≤ (V : ℝ) := Nat.cast_nonneg V
  have hS0 : (0:ℝ) ≤ S := by
    rw [hSdef]
    have : (0:ℝ) ≤ η * (V : ℝ) := mul_nonneg hη0.le hVnn
    linarith
  obtain ⟨K, hKdef⟩ : ∃ K : ℕ, K = Nat.floor (2 * S) + 1 := ⟨_, rfl⟩
  have hK2S : 2 * S < (K : ℝ) := by
    rw [hKdef]
    push_cast
    exact Nat.lt_floor_add_one (2 * S)
  have hKle : (K : ℝ) ≤ 2 * S + 1 := by
    rw [hKdef]
    push_cast
    have := Nat.floor_le (by linarith : (0:ℝ) ≤ 2 * S)
    linarith
  have hNpos : (0:ℝ) < (N : ℝ) + 1 := by positivity
  have hKV : K * (N + 1) < V := by
    have hstep : 2 * η * ((N : ℝ) + 1) * (V : ℝ) ≤ (V : ℝ) / 2 := by
      nlinarith [hηN, hVnn]
    have hprod : (2 * S + 1) * ((N : ℝ) + 1)
        = (2 * M + 1) * ((N : ℝ) + 1) + 2 * η * ((N : ℝ) + 1) * (V : ℝ) := by
      rw [hSdef]; ring
    have hcmp : (K : ℝ) * ((N : ℝ) + 1) ≤ (2 * S + 1) * ((N : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right hKle (le_of_lt hNpos)
    rw [hprod] at hcmp
    have hfin : ((K * (N + 1) : ℕ) : ℝ) < ((V : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hfin
  -- the window base, chosen after the window length
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, ∀ n : ℕ, Q ≤ n → S + 3 ≤ dist x ((c ^ n) • x) := by
    have hev := hc.eventually_ge_atTop (S + 3)
    rw [Filter.eventually_atTop] at hev
    exact hev
  -- the displacement of a small exponent is at most the spread
  have hdi : ∀ i : ℕ, i ≤ V → dist x ((c ^ i) • x) ≤ S := by
    intro i hi
    have hb := hMb i
    have hmono : η * (i : ℝ) ≤ η * (V : ℝ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hi) hη0.le
    rw [hSdef]
    linarith
  have hupper : ∀ i : ℕ, dist x ((c ^ (Q + i)) • x)
      ≤ dist x ((c ^ Q) • x) + dist x ((c ^ i) • x) := by
    intro i
    have hsplit : (c ^ (Q + i)) • x = (c ^ Q) • ((c ^ i) • x) := by
      rw [pow_add, mul_smul]
    rw [hsplit]
    refine le_trans (dist_triangle x ((c ^ Q) • x) ((c ^ Q) • ((c ^ i) • x))) ?_
    rw [hiso (c ^ Q) x ((c ^ i) • x)]
  have hlower : ∀ i : ℕ, dist x ((c ^ Q) • x)
      ≤ dist x ((c ^ (Q + i)) • x) + dist x ((c ^ i) • x) := by
    intro i
    have hswap : dist ((c ^ (Q + i)) • x) ((c ^ Q) • x) = dist x ((c ^ i) • x) := by
      have hcalc := hiso (c ^ Q) ((c ^ i) • x) x
      rw [← mul_smul, ← pow_add] at hcalc
      rw [hcalc]
      exact dist_comm _ _
    calc dist x ((c ^ Q) • x)
        ≤ dist x ((c ^ (Q + i)) • x) + dist ((c ^ (Q + i)) • x) ((c ^ Q) • x) :=
          dist_triangle _ _ _
      _ = dist x ((c ^ (Q + i)) • x) + dist x ((c ^ i) • x) := by rw [hswap]
  -- the box of an index in the window
  obtain ⟨bx, hbxdef⟩ : ∃ bx : ℕ → ℕ, ∀ i, bx i
      = Nat.floor (dist x ((c ^ (Q + i)) • x) - dist x ((c ^ Q) • x) + S) :=
    ⟨_, fun _ => rfl⟩
  have hboxnn : ∀ i : ℕ, i ≤ V →
      (0:ℝ) ≤ dist x ((c ^ (Q + i)) • x) - dist x ((c ^ Q) • x) + S := by
    intro i hi
    have hl := hlower i
    have hs := hdi i hi
    linarith
  have hboxle : ∀ i : ℕ, i ≤ V →
      dist x ((c ^ (Q + i)) • x) - dist x ((c ^ Q) • x) + S ≤ 2 * S := by
    intro i hi
    have hu := hupper i
    have hs := hdi i hi
    linarith
  have hbox : ∀ i, i < V → bx i < K := by
    intro i hi
    have hiV : i ≤ V := le_of_lt hi
    have hfl := Nat.floor_le (hboxnn i hiV)
    have hup := hboxle i hiV
    have hcast : ((Nat.floor (dist x ((c ^ (Q + i)) • x)
        - dist x ((c ^ Q) • x) + S) : ℕ) : ℝ) < (K : ℝ) := by
      linarith
    rw [hbxdef]
    exact_mod_cast hcast
  -- the pigeonhole
  obtain ⟨y, hy⟩ := exists_large_fiber bx hbox hKV
  obtain ⟨F, hFcard, hFmem⟩ : ∃ F : Finset ℕ, N + 1 < F.card ∧
      ∀ i ∈ F, i < V ∧ bx i = y := by
    refine ⟨Finset.filter (fun i => bx i = y) (Finset.range V), hy, ?_⟩
    intro i hi
    rw [Finset.mem_filter, Finset.mem_range] at hi
    exact hi
  have hFne : F.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨i₀, hi₀F, hi₀min⟩ : ∃ i₀ ∈ F, ∀ i ∈ F, i₀ ≤ i :=
    ⟨F.min' hFne, F.min'_mem hFne, fun i hi => F.min'_le i hi⟩
  -- indices in one box have nearly equal displacements
  have hclose : ∀ i ∈ F,
      |dist x ((c ^ (Q + i)) • x) - dist x ((c ^ (Q + i₀)) • x)| ≤ 1 := by
    intro i hi
    have hiV : i ≤ V := le_of_lt (hFmem i hi).1
    have hi₀V : i₀ ≤ V := le_of_lt (hFmem i₀ hi₀F).1
    have hfeq : Nat.floor (dist x ((c ^ (Q + i)) • x) - dist x ((c ^ Q) • x) + S)
        = Nat.floor (dist x ((c ^ (Q + i₀)) • x) - dist x ((c ^ Q) • x) + S) := by
      rw [← hbxdef, ← hbxdef, (hFmem i hi).2, (hFmem i₀ hi₀F).2]
    have hA1 := Nat.floor_le (hboxnn i hiV)
    have hA2 := Nat.lt_floor_add_one
      (dist x ((c ^ (Q + i)) • x) - dist x ((c ^ Q) • x) + S)
    have hB1 := Nat.floor_le (hboxnn i₀ hi₀V)
    have hB2 := Nat.lt_floor_add_one
      (dist x ((c ^ (Q + i₀)) • x) - dist x ((c ^ Q) • x) + S)
    rw [hfeq] at hA1 hA2
    rw [abs_le]
    constructor <;> linarith
  -- the geodesic and its midpoint
  obtain ⟨p, hp, hp0, hp1⟩ := hgeo x ((c ^ (Q + i₀)) • x)
  have hdm0 : (0:ℝ) ≤ dist x ((c ^ (Q + i₀)) • x) := dist_nonneg
  have hdmS : S + 3 ≤ dist x ((c ^ (Q + i₀)) • x) := hQ _ (Nat.le_add_right Q i₀)
  have hxz : dist x (p (dist x ((c ^ (Q + i₀)) • x) / 2))
      = dist x ((c ^ (Q + i₀)) • x) / 2 := by
    have hg := hp 0 ⟨le_refl 0, hdm0⟩ (dist x ((c ^ (Q + i₀)) • x) / 2)
      ⟨by linarith, by linarith⟩
    rw [hp0] at hg
    rw [hg, abs_of_nonpos
      (by linarith : (0:ℝ) - dist x ((c ^ (Q + i₀)) • x) / 2 ≤ 0)]
    ring
  -- every exponent from the box moves the midpoint by at most `ε`
  have hmove : ∀ i ∈ F, dist (p (dist x ((c ^ (Q + i₀)) • x) / 2))
      ((c ^ (i - i₀)) • p (dist x ((c ^ (Q + i₀)) • x) / 2)) ≤ 8 * δ + 1 := by
    intro i hi
    have hii₀ : i₀ ≤ i := hi₀min i hi
    have hiV : i < V := (hFmem i hi).1
    have hexp : (i - i₀) + (Q + i₀) = Q + i := by omega
    have hkC : (c ^ (i - i₀)) • ((c ^ (Q + i₀)) • x) = (c ^ (Q + i)) • x := by
      rw [← mul_smul, ← pow_add, hexp]
    have hexp2 : (Q + i₀) + (i - i₀) = Q + i := by omega
    have hseg := hiso (c ^ (Q + i₀)) x ((c ^ (i - i₀)) • x)
    rw [← mul_smul, ← pow_add, hexp2] at hseg
    have hdij : dist x ((c ^ (i - i₀)) • x) ≤ S := hdi (i - i₀) (by omega)
    have hdiS : S + 3 ≤ dist x ((c ^ (Q + i)) • x) := hQ _ (Nat.le_add_right Q i)
    have hd := hclose i hi
    rw [abs_le] at hd
    obtain ⟨hd1, hd2⟩ := hd
    have hA1 : dist ((c ^ (Q + i₀)) • x)
        ((c ^ (i - i₀)) • ((c ^ (Q + i₀)) • x))
        ≤ dist x ((c ^ (i - i₀)) • ((c ^ (Q + i₀)) • x)) := by
      rw [hkC, hseg]
      linarith
    have hA2 : dist x ((c ^ (i - i₀)) • x)
        ≤ dist x ((c ^ (i - i₀)) • ((c ^ (Q + i₀)) • x)) := by
      rw [hkC]
      linarith
    have hA3 : dist x ((c ^ (Q + i₀)) • x) / 2
        ≤ dist x ((c ^ (i - i₀)) • ((c ^ (Q + i₀)) • x)) := by
      rw [hkC]
      linarith
    have hmain := dist_smul_midpoint_le hδ hδ0 hgeo hiso (c ^ (i - i₀)) hp hp0 hp1
      hA1 hA2 hA3
    rw [hkC] at hmain
    have habs : |dist x ((c ^ (Q + i₀)) • x) - dist x ((c ^ (Q + i)) • x)| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    linarith
  -- the second point, far away and moved by exactly as much
  obtain ⟨A, hA⟩ : ∃ A : ℕ, dist x ((c ^ (Q + i₀)) • x) + max R 0
      ≤ dist x ((c ^ A) • x) := by
    have hev := hc.eventually_ge_atTop (dist x ((c ^ (Q + i₀)) • x) + max R 0)
    rw [Filter.eventually_atTop] at hev
    obtain ⟨A, hAge⟩ := hev
    exact ⟨A, hAge A (le_refl A)⟩
  have hfar : R ≤ dist (p (dist x ((c ^ (Q + i₀)) • x) / 2))
      ((c ^ A) • p (dist x ((c ^ (Q + i₀)) • x) / 2)) := by
    have ht1 := dist_triangle x (p (dist x ((c ^ (Q + i₀)) • x) / 2)) ((c ^ A) • x)
    have ht2 := dist_triangle (p (dist x ((c ^ (Q + i₀)) • x) / 2))
      ((c ^ A) • p (dist x ((c ^ (Q + i₀)) • x) / 2)) ((c ^ A) • x)
    have heq : dist ((c ^ A) • p (dist x ((c ^ (Q + i₀)) • x) / 2)) ((c ^ A) • x)
        = dist (p (dist x ((c ^ (Q + i₀)) • x) / 2)) x :=
      hiso (c ^ A) (p (dist x ((c ^ (Q + i₀)) • x) / 2)) x
    have hzx : dist (p (dist x ((c ^ (Q + i₀)) • x) / 2)) x
        = dist x ((c ^ (Q + i₀)) • x) / 2 := by rw [dist_comm]; exact hxz
    have hR0 : R ≤ max R 0 := le_max_left _ _
    linarith
  obtain ⟨hfin, hcard⟩ := hRN (p (dist x ((c ^ (Q + i₀)) • x) / 2))
    ((c ^ A) • p (dist x ((c ^ (Q + i₀)) • x) / 2)) hfar
  -- the box gives more elements than acylindricity allows
  have hmaps : ∀ i ∈ (F : Set ℕ), c ^ (i - i₀) ∈
      {g : G | dist (p (dist x ((c ^ (Q + i₀)) • x) / 2))
            (g • p (dist x ((c ^ (Q + i₀)) • x) / 2)) ≤ 8 * δ + 1 ∧
          dist ((c ^ A) • p (dist x ((c ^ (Q + i₀)) • x) / 2))
            (g • ((c ^ A) • p (dist x ((c ^ (Q + i₀)) • x) / 2)))
              ≤ 8 * δ + 1} := by
    intro i hi
    have hiF : i ∈ F := Finset.mem_coe.mp hi
    refine ⟨hmove i hiF, ?_⟩
    have hcomm : (c ^ (i - i₀)) • ((c ^ A) • p (dist x ((c ^ (Q + i₀)) • x) / 2))
        = (c ^ A) • ((c ^ (i - i₀)) • p (dist x ((c ^ (Q + i₀)) • x) / 2)) := by
      simp only [← mul_smul, ← pow_add]
      rw [Nat.add_comm (i - i₀) A]
    rw [hcomm, hiso (c ^ A) (p (dist x ((c ^ (Q + i₀)) • x) / 2))
      ((c ^ (i - i₀)) • p (dist x ((c ^ (Q + i₀)) • x) / 2))]
    exact hmove i hiF
  have hninj : Function.Injective (fun n : ℕ => c ^ n) := by
    have hzinj : Function.Injective (fun n : ℤ => c ^ n) :=
      injective_zpow_iff_not_isOfFinOrder.mpr (not_isOfFinOrder_of_isEscaping hc)
    intro a b hab
    have hz : c ^ (a : ℤ) = c ^ (b : ℤ) := by
      rw [zpow_natCast, zpow_natCast]
      exact hab
    have := hzinj hz
    exact_mod_cast this
  have hinj : Set.InjOn (fun i : ℕ => c ^ (i - i₀)) (F : Set ℕ) := by
    intro i hi j hj hij
    have hiF : i₀ ≤ i := hi₀min i (Finset.mem_coe.mp hi)
    have hjF : i₀ ≤ j := hi₀min j (Finset.mem_coe.mp hj)
    have hsub' : i - i₀ = j - i₀ := hninj hij
    omega
  have hcount := Set.ncard_le_ncard_of_injOn (fun i : ℕ => c ^ (i - i₀)) hmaps
    hinj hfin
  rw [Set.ncard_coe_Finset] at hcount
  have hle : F.card ≤ N := le_trans hcount hcard
  omega

end Action

/-! ## At Hull's Cayley graph -/

section Cayley

open GroupApproximation.Manuscript.NonMF.TorsionFree

/-- **Bowditch's dichotomy is discharged at `Γ(G,A)`.**  The estimate is proved
in the metric realisation, which is geodesic, and pulled back along the vertex
inclusion, which has bounded additive distortion and dense image. -/
theorem escapingIsLoxodromic_cayley {G : Type u} [Group G]
    (A : HullGeneratingSet G) :
    Elementary.EscapingIsLoxodromic G (Cayley.base A.alphabet) := by
  obtain ⟨M⟩ := CayleyGeodesicModel.hasGeodesicModel_of_hullGeneratingSet A
  have hacyW : IsAcylindrical G M.W :=
    isAcylindrical_of_additiveDistortion_of_dense M.distortion_nonneg
      M.hasAdditiveDistortion M.hasDenseImage M.equivariant M.isometric
      A.acylindrical
  exact Elementary.escapingIsLoxodromic_of_map M.distortion_nonneg
    M.hasAdditiveDistortion M.equivariant
    (escapingIsLoxodromic_of_geodesic M.hyperbolic M.delta_nonneg M.geodesic
      M.isometric hacyW _)

end Cayley

end GGT
end GroupApproximation
