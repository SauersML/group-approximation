import GroupApproximation.Sofic.HullSuitabilityGeometry

/-!
# The common-power theorem in a geodesic space, and the consumer its two ends
were waiting for

`Manuscript.NonMF.AxisDichotomyRoute.CommonPowerInGeodesicSpace` is the residual
of the geometric half of `AxisDichotomy`: in a geodesic `δ`-hyperbolic space
carrying an acylindrical isometric action, two loxodromic elements that are not
independent have a common nonzero power.  Its two ends are landed in
`Sofic.HullSuitabilityGeometry`:

* `exists_long_fellow_geodesics_of_not_independent` — non-independence gives, for
  every `T`, two nonzero exponents `n, m` and geodesics from `x` to `gⁿx` and to
  `hᵐx` that stay `4δ`-close for a length `T`;
* `acylindrical_common_power_of_two_orbit_fellow_travel` — `N + 1` exponent
  pairs, with both exponent families injective, whose orbit points are `ε`-close
  at two points `R` apart, force a common nonzero power.

This module supplies the second end's consumer in full, and names exactly what
is missing between the two.

## What is proved

`exists_common_zpow_of_fellowTravelMatching` runs the pigeonhole end: from
`FellowTravelMatching g h y` — for one fixed `ε`, and for every demanded `R` and
`n`, two points at least `R` apart carrying `n` matched exponent pairs — it
produces `g^p = h^q` with `p, q ≠ 0`.  The quantifier order is the one the
pigeonhole forces and is worth stating plainly: `ε` is chosen first, by the
geometry; `R` and `N` come back from acylindricity at that `ε`; and only then
must the geometry produce `N + 1` pairs.  A residue stated in any other order
would not compose.

`injective_of_separated_of_matched` is the second half of the iteration the
lead sketched, and it removes an obligation from whoever discharges the residue.
The pigeonhole demands that *both* exponent families be injective, but the
geometry naturally produces only the first: one matches `k` against some `m k`
and has no control on `k ↦ m k`.  Injectivity of the second family is free once
the first is spaced out, because `g` is loxodromic:

    m k = m k'  ⟹  d(gᵏx, gᵏ'x) ≤ 2ε  ⟹  τ(g)·|k − k'| ≤ 2ε,

so any two `k`'s separated by more than `2ε / τ(g)` have distinct partners.  So
the residue only has to produce a *spaced* family of `g`-exponents, and
`mul_le_dist_zpow` with `stableTranslation_pos_of_isLoxodromic` does the rest.

## What is missing, precisely

`FellowTravelMatching` is the residue.  Two things separate it from
`exists_long_fellow_geodesics_of_not_independent`:

1. **From the geodesic to the orbit.**  The fellow-travelling statement is about
   two *geodesics* `[x, gⁿx]` and `[x, hᵐx]`; the pigeonhole is about *orbit
   points* `gᵏx` and `hᵐᵏx`.  Passing between them needs each intermediate orbit
   point to lie within a bounded distance of the geodesic joining the ends of
   its own axis, which is stability of quasi-geodesics — the Morse lemma.  It is
   not in `Sofic.HullSuitabilityGeometry` as a statement about orbits; the
   material around `radius_le_of_chain_avoids_ball`,
   `linear_length_le_of_excursion_chain` and `exists_bound_excursion_chain_length`
   is a chain-level development of it and is the place to build it.
2. **The second basepoint.**  The pigeonhole wants the *same* `N + 1` difference
   elements `g^{-aᵢ}h^{bᵢ}` to nearly fix two points `R` apart, not one.  Along a
   fellow-travelling stretch this is what one expects — the difference elements
   translate the common stretch by a bounded amount — but it is a statement about
   the whole stretch, not about the basepoint, and it too rests on 1.

Neither is bookkeeping, and neither is attempted here.  What this module does is
make the residue a single named proposition with the right quantifier order, and
discharge everything on the pigeonhole side of it.

## Superseded, in one lemma

`injective_of_separated_of_matched` is
`GGT.Elementary.exists_injective_separated_family` in
`GGT/ElementaryCentralizerAxis.lean`, arrived at independently and wired there;
prefer that name.  The rest of this module is not duplicated: the pigeonhole
assembly `exists_common_zpow_of_fellowTravelMatching` is stated for a general
non-independent pair, where the two-basepoint condition is *not* free, and so it
is not subsumed by the commuting-case results of that file.

## Status

**Not compiled**, written while builds were frozen, and unwired for that reason.
-/

namespace GroupApproximation
namespace GGT
namespace ElementaryCommonPower

open GroupApproximation.HullGeometry

universe u v

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X] [MulAction G X]

/-! ## Matched exponent pairs -/

/-- **`n` matched exponent pairs at two basepoints.**  This is the hypothesis
`acylindrical_common_power_of_two_orbit_fellow_travel` consumes, packaged. -/
def MatchedPairs (g h : G) (y₁ y₂ : X) (ε : ℝ) (n : ℕ) : Prop :=
  ∃ a b : Fin n → ℤ, Function.Injective a ∧ Function.Injective b ∧
    ∀ i, dist ((g ^ (a i)) • y₁) ((h ^ (b i)) • y₁) ≤ ε ∧
      dist ((g ^ (a i)) • y₂) ((h ^ (b i)) • y₂) ≤ ε

/-- **The residue.**  For one fixed closeness constant, matched pairs in any
demanded number, at two points at least any demanded distance apart.

The order of the quantifiers is forced by the pigeonhole: `ε` is fixed by the
geometry, `R` and `N` are returned by acylindricity at that `ε`, and the pairs
are produced last. -/
def FellowTravelMatching (g h : G) (_y : X) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ (R : ℝ) (n : ℕ), ∃ y₁ y₂ : X,
    R ≤ dist y₁ y₂ ∧ MatchedPairs g h y₁ y₂ ε n

/-! ## Injectivity of the second family is free -/

/-- **A spaced family of `g`-exponents has distinct partners.**

The pigeonhole needs both exponent families injective; the geometry supplies
only the first.  If two matched pairs shared a partner `b i = b j`, their
`g`-orbit points would be `2ε`-close, so `τ(g)·|aⱼ − aᵢ| ≤ 2ε`.  Separating the
`g`-exponents by more than `2ε / τ(g)` therefore forces the partners apart, and
`stableTranslation_pos_of_isLoxodromic` makes that separation achievable. -/
theorem injective_of_separated_of_matched (hiso : IsIsometricAction G X)
    {g h : G} {y : X} {n : ℕ} {a b : Fin n → ℤ} {ε : ℝ}
    (hclose : ∀ i, dist ((g ^ (a i)) • y) ((h ^ (b i)) • y) ≤ ε)
    (hsep : ∀ i j : Fin n, i ≠ j →
      2 * ε < stableTranslation g y * |((a j - a i : ℤ) : ℝ)|) :
    Function.Injective b := by
  intro i j hij
  by_contra hne
  -- the two `g`-orbit points share a partner, so they are `2ε`-close
  have htri := dist_triangle ((g ^ (a i)) • y) ((h ^ (b i)) • y) ((g ^ (a j)) • y)
  have hswap : dist ((h ^ (b i)) • y) ((g ^ (a j)) • y)
      = dist ((g ^ (a j)) • y) ((h ^ (b j)) • y) := by
    rw [dist_comm, hij]
  have hclose2 : dist ((g ^ (a i)) • y) ((g ^ (a j)) • y) ≤ 2 * ε := by
    rw [hswap] at htri
    have h1 := hclose i
    have h2 := hclose j
    linarith
  -- but loxodromy makes them far apart
  have horbit := dist_zpow_orbit hiso g y (a i) (a j)
  have hlow := mul_le_dist_zpow hiso g y (a j - a i)
  rw [← horbit] at hlow
  exact lt_irrefl _ (lt_of_lt_of_le (hsep i j hne) (le_trans hlow hclose2))

/-! ## The pigeonhole end, discharged -/

/-- **A common nonzero power, from the matching residue.**  Acylindricity is
used once, through `acylindrical_common_power_of_two_orbit_fellow_travel`; the
residue is used once, at the `R` and `N` that acylindricity returns. -/
theorem exists_common_zpow_of_fellowTravelMatching
    (hiso : IsIsometricAction G X) (hacy : IsAcylindrical G X)
    {g h : G} {y : X} (hM : FellowTravelMatching g h y) :
    ∃ p q : ℤ, p ≠ 0 ∧ q ≠ 0 ∧ g ^ p = h ^ q := by
  obtain ⟨ε, hε, hmatch⟩ := hM
  obtain ⟨R, N, hRN⟩ :=
    acylindrical_common_power_of_two_orbit_fellow_travel hiso hacy hε
  obtain ⟨y₁, y₂, hfar, hmp⟩ := hmatch R (N + 1)
  obtain ⟨a, b, ha, hb, hclose⟩ := hmp
  obtain ⟨i, j, -, hpne, hqne, hpow⟩ := hRN y₁ y₂ hfar g h a b ha hb hclose
  exact ⟨a i - a j, b i - b j, hpne, hqne, hpow⟩

/-! ## The named residual, in the shape the route consumes -/

/-- **`CommonPowerInGeodesicSpace`, from the matching residue.**

The conclusion is
`Manuscript.NonMF.AxisDichotomyRoute.CommonPowerInGeodesicSpace` written out;
that module is not imported here, so that this development stays below the
manuscript layer.

Hyperbolicity, the sign of `δ` and geodesicity are carried but unused on this
side of the argument: they are what the *residue* needs, through
`exists_long_fellow_geodesics_of_not_independent`, and they are kept in the
statement so that the two halves compose without reshaping. -/
theorem commonPowerInGeodesicSpace_of_fellowTravelMatching
    (hFTM : ∀ {G' : Type u} [Group G'] {Y : Type v} [PseudoMetricSpace Y]
      [MulAction G' Y] {δ : ℝ}, IsHyperbolicSpace δ Y → 0 ≤ δ →
      IsGeodesicSpace Y → IsIsometricAction G' Y → IsAcylindrical G' Y →
        ∀ {g h : G'} {y : Y}, IsLoxodromic g y → IsLoxodromic h y →
          ¬ Independent g h y → FellowTravelMatching g h y) :
    ∀ {G' : Type u} [Group G'] {Y : Type v} [PseudoMetricSpace Y]
      [MulAction G' Y] {δ : ℝ}, IsHyperbolicSpace δ Y → 0 ≤ δ →
      IsGeodesicSpace Y → IsIsometricAction G' Y → IsAcylindrical G' Y →
        ∀ {g h : G'} {y : Y}, IsLoxodromic g y → IsLoxodromic h y →
          ¬ Independent g h y → ∃ p q : ℤ, p ≠ 0 ∧ q ≠ 0 ∧ g ^ p = h ^ q := by
  intro G' _ Y _ _ δ hδ hδ0 hgeo hiso hacy g h y hg hh hnind
  exact exists_common_zpow_of_fellowTravelMatching hiso hacy
    (hFTM hδ hδ0 hgeo hiso hacy hg hh hnind)

end ElementaryCommonPower
end GGT
end GroupApproximation
