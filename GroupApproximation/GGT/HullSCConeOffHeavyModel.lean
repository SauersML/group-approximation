import GroupApproximation.Algebra.MorseLemma
import GroupApproximation.GGT.CayleyGeodesicRealisation
import GroupApproximation.GGT.ElementaryMorseChord
import GroupApproximation.GGT.HullSCConeOffHeavyHyperbolic
import GroupApproximation.GGT.HyperbolicFreeGroupAH

/-!
# Quasiconvexity without the Morse lemma, through the geodesic model

`GGT/HullSCConeOffHeavyQuasiconvex.lean` proves `IsWordQuasiconvex` for `⟨g⟩`
from `Hyperbolic.MorseLemma`, which nothing in the tree proves.  This module
proves the same thing **unconditionally**, and the reason it can is that both
halves of the Morse lemma are already theorems here — for a *geodesic* space —
and Hull's Cayley graph now has a geodesic model.

## Why this was not available before

`GGT.ElementaryMorse.exists_bound_chord_near_chain` and
`exists_bound_chain_near_chord` hold in any `PseudoMetricSpace` satisfying
`IsHyperbolicSpace`, but each needs a genuine `f : ℝ → X` with
`IsGeodesicSegment f 0 L` joining the chain's endpoints, and `Cayley A` has
none: every distance in it is a natural number
(`Manuscript.NonMF.AxisDichotomyRoute.not_isGeodesicSpace_cayley`).  That is why
the Morse route was recorded as closed.

It is no longer closed.  `GGT.CayleyGeodesicModel.hasGeodesicModel_of_hullGeneratingSet`
is unconditional: `IsGeodesicSpace (Point A)` is indeed false — the doubled
edges put distinct points at distance zero — but `PointQuot A`, the metric
identification, is geodesic, and `HasGeodesicModel` quantifies the model space
existentially.  So a `GeodesicModel` of `Γ(G,A)` exists: a hyperbolic geodesic
space `W` with a map `iota` of bounded additive distortion.

## The argument

Both chains are compared against **one** chord, which is what makes the
four-point condition unnecessary.

* The power orbit `i ↦ iota (g ^ i)` is a chain in `W` with step
  `|g|_A + C` and progress `l·k − (B + C)`, by additive distortion and
  loxodromy.
* The prefixes of an `A`-geodesic word for `g ^ N` are a chain in `W` with step
  `1 + C` and progress `k − C`, by
  `Hyperbolic.isQuasiGeodesic_of_isGeodesicWord`.
* The two chains have the *same endpoints*, `iota 1` and `iota (g ^ N)`, so one
  geodesic of `W` serves as the chord for both.
* `exists_bound_chain_near_chord` puts each prefix within `K₂` of a chord point;
  `exists_bound_chord_near_chain` puts that chord point within `K₁` of a power
  `iota (g ^ m)`; additive distortion brings the bound back to the word metric.

The constant `K₁ + K₂ + C` depends only on `δ`, `|g|_A`, `l`, `B` and `C`, and
in particular not on `N` or on the chosen word, which is exactly the uniformity
`IsWordQuasiconvex` asks for.

## What this retires

The `Hyperbolic.MorseLemma` hypothesis of `GGT/HullSCConeOffHeavyQuasiconvex.lean`
and `GGT/HullSCConeOffHeavyClauseA.lean`.  With
`exists_isWordQuasiconvex_zpowers` below, clause (a) of the cone-off leaf is
unconditional except for the bounded Hausdorff distance between `⟨g⟩` and
`E(g)` — Dahmani--Guirardel--Osin's Lemma 6.5, whose leaf is
`GGT.Elementary.ElementaryClosureCoarseTranslation`.

The Morse-conditional route is kept rather than deleted: it is stated at an
abstract four-point-hyperbolic alphabet, where no geodesic model is available,
and this one is not.

## Duplication declared

The integer-exponent bookkeeping of `exists_isWordQuasiconvex_zpowers` repeats
that of `exists_isWordQuasiconvex_zpowers_of_morse`.  The two differ only in
which nonnegative-power bound they consume, and they should be unified once the
Morse-conditional route is confirmed unwanted.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Manuscript.NonMF.AxisDichotomyRoute

universe u

/-! ## Prefixes of a geodesic word to a nonnegative power -/

/-- **Every prefix of an `A`-geodesic word for `h ^ N` is uniformly near
`⟨h⟩`**, unconditionally.

See the module header: two chains, one chord, and the two halves of the Morse
lemma applied in the geodesic model. -/
theorem exists_bound_prefix_pow {G : Type u} [Group G] (A : HullGeneratingSet G)
    {h : G} (hlox : IsLoxodromic h (Cayley.base A.alphabet)) :
    ∃ R : ℕ, ∀ (N : ℕ) (w : List G), (∀ x ∈ w, x ∈ A.alphabet.carrier) →
      w.prod = h ^ N → w.length = wordDist A.alphabet.carrier 1 (h ^ N) →
        ∀ i ≤ w.length, ∃ e ∈ Subgroup.zpowers h,
          wordDist A.alphabet.carrier (w.take i).prod e ≤ R := by
  classical
  obtain ⟨M⟩ := GGT.CayleyGeodesicModel.hasGeodesicModel_of_hullGeneratingSet A
  obtain ⟨l, hl, B, hB, hlin⟩ := hlox
  set S : Set G := A.alphabet.carrier with hS_def
  have hS : IsSymmetricGeneratingSet S := A.alphabet.symmetricGenerating
  set C : ℝ := M.distortion with hC_def
  have hC0 : 0 ≤ C := M.distortion_nonneg
  -- distances in the model, above and below
  have hup : ∀ x y : G, dist (M.iota (Cayley.of A.alphabet x))
      (M.iota (Cayley.of A.alphabet y)) ≤ ((wordDist S x y : ℕ) : ℝ) + C := by
    intro x y
    have habs := M.hasAdditiveDistortion (Cayley.of A.alphabet x)
      (Cayley.of A.alphabet y)
    have hd : dist (Cayley.of A.alphabet x) (Cayley.of A.alphabet y)
        = ((wordDist S x y : ℕ) : ℝ) := Cayley.dist_eq _ _
    rw [hd] at habs
    have := (abs_le.mp habs).2
    linarith
  have hlow : ∀ x y : G, ((wordDist S x y : ℕ) : ℝ) - C
      ≤ dist (M.iota (Cayley.of A.alphabet x))
        (M.iota (Cayley.of A.alphabet y)) := by
    intro x y
    have habs := M.hasAdditiveDistortion (Cayley.of A.alphabet x)
      (Cayley.of A.alphabet y)
    have hd : dist (Cayley.of A.alphabet x) (Cayley.of A.alphabet y)
        = ((wordDist S x y : ℕ) : ℝ) := Cayley.dist_eq _ _
    rw [hd] at habs
    have := (abs_le.mp habs).1
    linarith
  -- the two Morse constants
  obtain ⟨K₁, hK₁0, hK₁⟩ := GGT.ElementaryMorse.exists_bound_chord_near_chain
    (X := M.W) M.hyperbolic M.delta_nonneg
    (D := ((wordNorm S h : ℕ) : ℝ) + C) (by positivity) hl
    (B := B + C) (by linarith)
  obtain ⟨K₂, hK₂0, hK₂⟩ := GGT.ElementaryMorse.exists_bound_chain_near_chord
    (X := M.W) M.hyperbolic M.delta_nonneg (D := 1 + C) (by linarith)
    (l := 1) one_pos (B := C) hC0
  refine ⟨⌈K₁ + K₂ + C⌉₊, ?_⟩
  intro N w hlet hprod hlen i hi
  -- the two chains
  set y : ℕ → M.W := fun k => M.iota (Cayley.of A.alphabet (h ^ k)) with hy_def
  set c : ℕ → M.W := fun k => M.iota (Cayley.of A.alphabet ((w.take k).prod))
    with hc_def
  have hpowdist : ∀ a b : ℕ, a ≤ b →
      wordDist S (h ^ a) (h ^ b) = wordNorm S (h ^ (b - a)) := by
    intro a b hab
    obtain ⟨k, rfl⟩ : ∃ k, b = a + k := ⟨b - a, by omega⟩
    have hsub : a + k - a = k := by omega
    rw [hsub]
    show wordNorm S ((h ^ a)⁻¹ * h ^ (a + k)) = wordNorm S (h ^ k)
    rw [pow_add, inv_mul_cancel_left]
  -- the power chain
  have hystep : ∀ k, k < N → dist (y k) (y (k + 1)) ≤ ((wordNorm S h : ℕ) : ℝ) + C := by
    intro k _hk
    have hd := hup (h ^ k) (h ^ (k + 1))
    have he : wordDist S (h ^ k) (h ^ (k + 1)) = wordNorm S h := by
      rw [hpowdist k (k + 1) (by omega)]
      have : k + 1 - k = 1 := by omega
      rw [this, pow_one]
    rw [he] at hd
    exact hd
  have hyprog : ∀ a b : ℕ, a ≤ b → b ≤ N →
      l * ((b - a : ℕ) : ℝ) - (B + C) ≤ dist (y a) (y b) := by
    intro a b hab _hb
    have hd := hlow (h ^ a) (h ^ b)
    rw [hpowdist a b hab] at hd
    have hlk := hlin (b - a)
    have hbs : dist (Cayley.base A.alphabet) ((h ^ (b - a)) • Cayley.base A.alphabet)
        = ((wordNorm S (h ^ (b - a)) : ℕ) : ℝ) := GGT.dist_base_smul A.alphabet _
    rw [hbs] at hlk
    linarith
  -- the prefix chain
  have hgw : IsGeodesicWord S w w.prod := by
    refine ⟨⟨hlet, rfl⟩, ?_⟩
    rw [hprod, hlen, wordDist_one_left]
  have hqg := Hyperbolic.isQuasiGeodesic_of_isGeodesicWord hS hgw
  have hcstep : ∀ k, k < w.length → dist (c k) (c (k + 1)) ≤ 1 + C := by
    intro k hk
    have hd := hup ((w.take k).prod) ((w.take (k + 1)).prod)
    have hq : wordDist S ((w.take k).prod) ((w.take (k + 1)).prod)
        ≤ 1 * (k + 1 - k) + 0 :=
      (hqg k (by omega) (k + 1) (by omega) (by omega)).1
    have hsub : k + 1 - k = 1 := by omega
    rw [hsub] at hq
    have hqr : ((wordDist S ((w.take k).prod) ((w.take (k + 1)).prod) : ℕ) : ℝ)
        ≤ 1 := by exact_mod_cast (by omega : wordDist S ((w.take k).prod)
          ((w.take (k + 1)).prod) ≤ 1)
    linarith
  have hcprog : ∀ a b : ℕ, a ≤ b → b ≤ w.length →
      (1 : ℝ) * ((b - a : ℕ) : ℝ) - C ≤ dist (c a) (c b) := by
    intro a b hab hb
    have hd := hlow ((w.take a).prod) ((w.take b).prod)
    have hq : b - a
        ≤ 1 * (wordDist S ((w.take a).prod) ((w.take b).prod) + 0) :=
      (hqg a (by omega) b hb hab).2
    have hqr : ((b - a : ℕ) : ℝ)
        ≤ ((wordDist S ((w.take a).prod) ((w.take b).prod) : ℕ) : ℝ) := by
      exact_mod_cast (by omega : b - a ≤ wordDist S ((w.take a).prod)
        ((w.take b).prod))
    linarith
  -- the shared endpoints
  have hc0 : c 0 = y 0 := by
    show M.iota (Cayley.of A.alphabet ((w.take 0).prod))
      = M.iota (Cayley.of A.alphabet (h ^ 0))
    rw [List.take_zero, List.prod_nil, pow_zero]
  have hcN : c w.length = y N := by
    show M.iota (Cayley.of A.alphabet ((w.take w.length).prod))
      = M.iota (Cayley.of A.alphabet (h ^ N))
    rw [List.take_length, hprod]
  -- the chord
  obtain ⟨f, hf, hf0, hfL⟩ := M.geodesic (c 0) (c w.length)
  have hL0 : (0 : ℝ) ≤ dist (c 0) (c w.length) := dist_nonneg
  obtain ⟨t, ht, hct⟩ := hK₂ c w.length hcstep hcprog (dist (c 0) (c w.length))
    hL0 f hf hf0 hfL i hi
  obtain ⟨m, hmN, hym⟩ := hK₁ y N hystep hyprog (dist (c 0) (c w.length)) hL0 f hf
    (by rw [hf0, hc0]) (by rw [hfL, hcN]) t ht
  refine ⟨h ^ m, Subgroup.mem_zpowers_iff.mpr ⟨(m : ℤ), by rw [zpow_natCast]⟩, ?_⟩
  have htri : dist (c i) (y m) ≤ dist (c i) (f t) + dist (f t) (y m) :=
    dist_triangle _ _ _
  have hsym : dist (f t) (y m) = dist (y m) (f t) := dist_comm _ _
  have hlowim := hlow ((w.take i).prod) (h ^ m)
  have hfinal : ((wordDist S ((w.take i).prod) (h ^ m) : ℕ) : ℝ) ≤ K₁ + K₂ + C := by
    have hci : dist (c i) (y m) = dist (M.iota (Cayley.of A.alphabet ((w.take i).prod)))
        (M.iota (Cayley.of A.alphabet (h ^ m))) := rfl
    rw [hci] at htri
    linarith
  have hceil : K₁ + K₂ + C ≤ ((⌈K₁ + K₂ + C⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have : ((wordDist S ((w.take i).prod) (h ^ m) : ℕ) : ℝ)
      ≤ ((⌈K₁ + K₂ + C⌉₊ : ℕ) : ℝ) := by linarith
  exact_mod_cast this

/-! ## Quasiconvexity of the cyclic subgroup, unconditionally -/

/-- **The cyclic subgroup of a loxodromic element is quasiconvex in `Γ(G,A)`**,
with no hypothesis beyond `A` being a Hull generating set.

The two signs are handled separately and their constants merged, exactly as in
the Morse-conditional route; `Subgroup.zpowers_inv` identifies the two
subgroups. -/
theorem exists_isWordQuasiconvex_zpowers {G : Type u} [Group G]
    (A : HullGeneratingSet G) {g : G}
    (hlox : IsLoxodromic g (Cayley.base A.alphabet)) :
    ∃ sigma : ℕ, IsWordQuasiconvex A.alphabet (Subgroup.zpowers g) sigma := by
  have hloxinv : IsLoxodromic g⁻¹ (Cayley.base A.alphabet) :=
    isLoxodromic_inv (isIsometricAction_cayley A.alphabet) hlox
  obtain ⟨R₁, hR₁⟩ := exists_bound_prefix_pow A hlox
  obtain ⟨R₂, hR₂⟩ := exists_bound_prefix_pow A hloxinv
  refine ⟨max R₁ R₂, ?_⟩
  intro b hb w hlet hprod hlen i hi
  obtain ⟨t, ht⟩ := Subgroup.mem_zpowers_iff.mp hb
  rcases Int.natAbs_eq t with hcase | hcase
  · have hbpow : b = g ^ t.natAbs := by
      have hz : g ^ ((t.natAbs : ℤ)) = b := by
        rw [← hcase]
        exact ht
      rw [← hz, zpow_natCast]
    subst hbpow
    obtain ⟨e, he, hle⟩ := hR₁ t.natAbs w hlet hprod hlen i hi
    exact ⟨e, he, le_trans hle (le_max_left _ _)⟩
  · have hbpow : b = g⁻¹ ^ t.natAbs := by
      have hz : g ^ (-(t.natAbs : ℤ)) = b := by
        rw [← hcase]
        exact ht
      rw [← hz, zpow_neg, zpow_natCast, inv_pow]
    subst hbpow
    obtain ⟨e, he, hle⟩ := hR₂ t.natAbs w hlet hprod hlen i hi
    refine ⟨e, ?_, le_trans hle (le_max_right _ _)⟩
    rwa [Subgroup.zpowers_inv] at he

end HullSC
end GroupApproximation
