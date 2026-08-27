import GroupApproximation.Sofic.HullSuitabilityGeometry

/-!
# `LoxodromicOfCommute`, reduced to one fellow-travelling hypothesis

`Manuscript.NonMF.OsinNormalReduction.LoxodromicOfCommute` asks that an element
of infinite order commuting with a loxodromic element be loxodromic.  For an
acylindrical action this is Osin's centralizer statement, and
`Sofic.HullSuitabilityGeometry` already carries the half of it that acylindricity
alone gives:

* `finite_centralizer_ball` — every ball meets the centralizer of a loxodromic
  element in a finite set;
* `isEscaping_of_commutes_of_not_isOfFinOrder` — so an infinite-order element of
  that centralizer has an escaping orbit.

Escaping is weaker than loxodromic: it is `d(x, cⁿx) → ∞` with no rate, and the
docstring of `exists_loxodromic_mem_of_common_zpow` records that the missing
step is the linear rate.  This module supplies that step from one hypothesis,
and the hypothesis is the Morse statement rather than the conclusion.

## The argument

Write `A` for an exponent of `c` and `B` for an exponent of `g`.  Because `c`
commutes with `g`, the difference element `c⁻ᴬ gᴮ` displaces the two points `x`
and `gᴹ x` by the *same* amount — that is `dist_zpow_smul_of_commute` below, and
it is the only place the commuting hypothesis is used.  So a single closeness
bound

    d(cᴬ x, gᴮ x) ≤ ε

feeds both halves of the acylindricity condition at once, and `g` loxodromic
puts `gᴹ x` as far from `x` as the condition asks.  With `N + 1` distinct
exponent pairs meeting that bound, `acylindrical_common_power_pigeonhole` forces
two of the difference elements to coincide, and cancelling gives a genuine
common power

    c^A = g^B,  A ≠ 0,  B ≠ 0,

from which `isLoxodromic_of_common_zpow` makes `c` loxodromic.

Infinite order of `c` is not needed: the common power carries it.  What the
hypothesis `OrbitFellowTravels` says is that the `c`-orbit of `x` returns
infinitely often to a fixed neighbourhood of the `g`-orbit, which is what
stability of quasi-geodesics gives — the `c`-orbit and the `g`-orbit are
quasi-geodesic lines with the *same* quasi-geodesic constants, since
`d(cᴬx, gⁿ cᴬ x) = d(x, gⁿ x)` exactly, and they have the same pair of
endpoints because `c` commutes with `g`.

## Status

**Not compiled**, written while builds were frozen, and unwired for that reason.
-/

namespace GroupApproximation
namespace GGT
namespace ElementaryFill

open GroupApproximation.HullGeometry

universe u v

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X] [MulAction G X]

/-! ## The commuting displacement identity -/

/-- **A centralizing element displaces the whole `g`-orbit uniformly.**

If `c` commutes with `g` then translating the basepoint by `gᴹ` changes neither
`cᴬ x` nor `gᴮ x` relative to one another.  This is what lets one closeness
bound serve both basepoints of the acylindricity condition, and it is the only
use of the commuting hypothesis in this module. -/
theorem dist_zpow_smul_of_commute (hiso : IsIsometricAction G X) {g c : G}
    (hcg : Commute c g) (A B M : ℤ) (x : X) :
    dist ((c ^ A) • ((g ^ M) • x)) ((g ^ B) • ((g ^ M) • x))
      = dist ((c ^ A) • x) ((g ^ B) • x) := by
  have h1 : (c ^ A) • ((g ^ M) • x) = (g ^ M) • ((c ^ A) • x) := by
    rw [← mul_smul, ← mul_smul, (hcg.zpow_zpow A M).eq]
  have h2 : (g ^ B) • ((g ^ M) • x) = (g ^ M) • ((g ^ B) • x) := by
    rw [← mul_smul, ← mul_smul, ((Commute.refl g).zpow_zpow B M).eq]
  rw [h1, h2]
  exact hiso (g ^ M) ((c ^ A) • x) ((g ^ B) • x)

/-! ## The fellow-travelling hypothesis -/

/-- **The `c`-orbit returns to a fixed neighbourhood of the `g`-orbit
arbitrarily often.**

For every `n` there are `n` distinct `c`-exponents and `n` distinct
`g`-exponents matched so that the corresponding orbit points are `ε`-close.
This is the Morse-stability input: two quasi-geodesic lines with the same
endpoints and the same quasi-geodesic constants stay at bounded Hausdorff
distance, so every `cᴬ x` is uniformly close to the `g`-orbit, and the two
exponent families may then be thinned to be injective because both orbits
escape. -/
def OrbitFellowTravels (g c : G) (x : X) (ε : ℝ) : Prop :=
  ∀ n : ℕ, ∃ a b : Fin n → ℤ, Function.Injective a ∧ Function.Injective b ∧
    ∀ i, dist ((c ^ (a i)) • x) ((g ^ (b i)) • x) ≤ ε

/-! ## The common power, and loxodromy -/

/-- **A common nonzero power of `c` and `g`**, from acylindricity and the
fellow-travelling hypothesis.  Acylindricity enters once, through
`acylindrical_common_power_pigeonhole`; the commuting hypothesis enters once,
through `dist_zpow_smul_of_commute`. -/
theorem exists_common_zpow_of_orbitFellowTravels
    (hiso : IsIsometricAction G X) (hacy : IsAcylindrical G X)
    {g c : G} {x : X} (hg : IsLoxodromic g x) (hcg : Commute c g)
    {ε : ℝ} (hε : 0 < ε) (hft : OrbitFellowTravels g c x ε) :
    ∃ A B : ℤ, A ≠ 0 ∧ B ≠ 0 ∧ c ^ A = g ^ B := by
  obtain ⟨R, N, hRN⟩ := acylindrical_common_power_pigeonhole hacy hε
  -- `g` is loxodromic, so some point of its orbit is at least `R` from `x`.
  have hev := hg.isEscaping.eventually_ge_atTop R
  rw [Filter.eventually_atTop] at hev
  obtain ⟨M, hM⟩ := hev
  have hfar : R ≤ dist x ((g ^ (M : ℤ)) • x) := by
    rw [zpow_natCast]
    exact hM M le_rfl
  -- The two exponent families the hypothesis supplies.
  obtain ⟨a, b, ha, hb, hclose⟩ := hft (N + 1)
  -- Each difference element displaces both basepoints by at most `ε`.
  have hmove : ∀ i : Fin (N + 1),
      dist x ((c ^ (-a i) * g ^ (b i)) • x) ≤ ε ∧
        dist ((g ^ (M : ℤ)) • x)
          ((c ^ (-a i) * g ^ (b i)) • ((g ^ (M : ℤ)) • x)) ≤ ε := by
    intro i
    constructor
    · rw [dist_zpow_difference hiso]
      exact hclose i
    · rw [dist_zpow_difference hiso,
        dist_zpow_smul_of_commute hiso hcg (a i) (b i) (M : ℤ) x]
      exact hclose i
  obtain ⟨i, j, -, hAne, hBne, hpow⟩ :=
    hRN x ((g ^ (M : ℤ)) • x) hfar c g a b ha hb hmove
  exact ⟨a i - a j, b i - b j, hAne, hBne, hpow⟩

/-- **An element commuting with a loxodromic element is loxodromic**, once its
orbit fellow-travels the axis.  This is
`Manuscript.NonMF.OsinNormalReduction.LoxodromicOfCommute` at the pair `(g, c)`,
with the Morse input named rather than assumed in the conclusion. -/
theorem isLoxodromic_of_commute_of_orbitFellowTravels
    (hiso : IsIsometricAction G X) (hacy : IsAcylindrical G X)
    {g c : G} {x : X} (hg : IsLoxodromic g x) (hcg : Commute c g)
    {ε : ℝ} (hε : 0 < ε) (hft : OrbitFellowTravels g c x ε) :
    IsLoxodromic c x := by
  obtain ⟨A, B, hA, hB, hpow⟩ :=
    exists_common_zpow_of_orbitFellowTravels hiso hacy hg hcg hε hft
  exact isLoxodromic_of_common_zpow hiso hg hB hA hpow.symm

/-- **The named fact, from the Morse input, uniformly.**  The conclusion is
`Manuscript.NonMF.OsinNormalReduction.LoxodromicOfCommute G x` written out; that
module is not imported here, so that this development stays below the
manuscript layer. -/
theorem loxodromicOfCommute_of_orbitFellowTravels
    (hiso : IsIsometricAction G X) (hacy : IsAcylindrical G X) {x : X}
    (hMorse : ∀ g c : G, IsLoxodromic g x → Commute c g → ¬ IsOfFinOrder c →
      ∃ ε : ℝ, 0 < ε ∧ OrbitFellowTravels g c x ε) :
    ∀ g c : G, IsLoxodromic g x → Commute c g → ¬ IsOfFinOrder c →
      IsLoxodromic c x := by
  intro g c hg hcg hc
  obtain ⟨ε, hε, hft⟩ := hMorse g c hg hcg hc
  exact isLoxodromic_of_commute_of_orbitFellowTravels hiso hacy hg hcg hε hft

end ElementaryFill
end GGT
end GroupApproximation
