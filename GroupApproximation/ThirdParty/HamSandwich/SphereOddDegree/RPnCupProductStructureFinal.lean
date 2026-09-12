import Mathlib
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnCupProductNonvanishing
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnCupProductStructureConstruction
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnActualAlphaPowersGenerate
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnGeneratorCupNoCup

/-!
# Branch 3 Prompt 74 — Unconditional assembly of `RPnCupProductStructure`

This file closes the work originally scoped for Prompt 44: it constructs the full
cellular cup-product structure `RPnCupProductStructure c` for **every** additive
cellular cochain comparison `c : RPnCellularCochainStructure n`, taking **no**
extra hypotheses beyond `n` and `c`.

The genuine (Mathlib-absent) RPⁿ cup-product computation
`H^*(RPⁿ; F₂) = F₂[α]/(αⁿ⁺¹)` is now supplied — with no cup-product structure
assumption — by Prompt 73's `branch3_rp_generator_cup_ne_zero_no_cup`
(for `1 ≤ n`; the degree-zero-only case `n = 0` is handled directly via right
unitality of the cohomology cup product). Feeding that nonvanishing fact into the
minimal constructor `branch3_construct_RPnCupProductStructure_of_cup_nonzero`
produces the structure unconditionally.

No `sorry`, no new axioms.
-/

noncomputable section

open CategoryTheory AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- **Generator cup nonvanishing, for all `n` (no cup-product structure).** For
`p + q ≤ n` the cup product of the canonical generators is nonzero. For `1 ≤ n`
this is Prompt 73's `branch3_rp_generator_cup_ne_zero_no_cup`; for `n = 0` only the
degree-zero case survives (`p = q = 0`), and it follows from right unitality of the
cohomology cup product together with `1 = gen₀` and `gen₀ ≠ 0`. -/
theorem branch3_rp_generator_cup_ne_zero_all
    (n : ℕ) (c : RPnCellularCochainStructure n)
    {p q : ℕ} (hp : p ≤ n) (hq : q ≤ n) (hpq : p + q ≤ n) :
    cupZMod2 (rpCohomologyGenerator c p hp) (rpCohomologyGenerator c q hq) ≠ 0 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hp0 : p = 0 := Nat.le_zero.mp (le_trans (Nat.le_add_right p q) hpq)
    have hq0 : q = 0 := Nat.le_zero.mp (le_trans (Nat.le_add_left q p) hpq)
    subst hp0; subst hq0
    rw [← branch3_one_eq_generator_zero c, cupZMod2_oneZMod2_right]
    exact oneZMod2_ne_zero_RP c
  · exact branch3_rp_generator_cup_ne_zero_no_cup n hn c hp hq hpq

/-- **Unconditional construction of `RPnCupProductStructure`.** The full cellular
cup-product structure `RPnCupProductStructure c` is constructed for *every*
additive cellular comparison `c : RPnCellularCochainStructure n`, taking no
hypotheses beyond `n` and `c`. The required cup-nonvanishing input is supplied by
`branch3_rp_generator_cup_ne_zero_all` (Prompt 73's no-cup generator theorem, with
the `n = 0` case handled by right unitality), fed into the minimal constructor
`branch3_construct_RPnCupProductStructure_of_cup_nonzero`. -/
theorem construct_RPnCupProductStructure
    (n : ℕ) (c : RPnCellularCochainStructure n) :
    RPnCupProductStructure c :=
  branch3_construct_RPnCupProductStructure_of_cup_nonzero c
    (fun _ _ hp hq hpq => branch3_rp_generator_cup_ne_zero_all n c hp hq hpq)

/-! ## Downstream unconditional wrappers

The following wrappers restate load-bearing downstream results with the **free**
`cup : RPnCupProductStructure c` hypothesis removed: the cup-product structure is
now produced internally by `construct_RPnCupProductStructure`, with no extra
hypotheses. -/

/-- Sub-truncation nonvanishing `(actualRPAlpha n) ^⌣ k ≠ 0` (`k ≤ n`),
unconditionally. -/
theorem actualRPAlpha_power_ne_zero_unconditional_cup
    (n : ℕ) (hn : 1 ≤ n) (c : RPnCellularCochainStructure n) {k : ℕ} (hk : k ≤ n) :
    cupPowZMod2 (actualRPAlpha n) k ≠ 0 :=
  actualRPAlpha_power_ne_zero n hn c (construct_RPnCupProductStructure n c) hk

/-- The load-bearing top-power nonvanishing `(actualRPAlpha n) ^⌣ n ≠ 0`,
unconditionally. -/
theorem actualRPAlpha_topPower_ne_zero_unconditional_cup
    (n : ℕ) (hn : 1 ≤ n) (c : RPnCellularCochainStructure n) :
    cupPowZMod2 (actualRPAlpha n) n ≠ 0 :=
  actualRPAlpha_topPower_ne_zero n hn c (construct_RPnCupProductStructure n c)

/-- The actual top class is nonzero, unconditionally. -/
theorem rpTopClass_actual_ne_zero_unconditional_cup
    (n : ℕ) (hn : 1 ≤ n) (c : RPnCellularCochainStructure n) :
    rpTopClass n (monodromyFunctional n) ≠ 0 :=
  rpTopClass_actual_ne_zero n hn c (construct_RPnCupProductStructure n c)

/-- The actual powers generate the cohomology groups (`k ≤ n`), unconditionally. -/
theorem actualRPAlpha_power_generates_unconditional_cup
    (n : ℕ) (hn : 1 ≤ n) (c : RPnCellularCochainStructure n) {k : ℕ} (hk : k ≤ n)
    (w : rpCohomology n k) :
    ∃ d : ZMod 2, d • cupPowZMod2 (actualRPAlpha n) k = w :=
  actualRPAlpha_power_generates n hn c (construct_RPnCupProductStructure n c) hk w

/-- The actual powers span the cohomology groups (`k ≤ n`), unconditionally. -/
theorem actualRPAlpha_power_span_eq_top_unconditional_cup
    (n : ℕ) (hn : 1 ≤ n) (c : RPnCellularCochainStructure n) {k : ℕ} (hk : k ≤ n) :
    Submodule.span (ZMod 2) {cupPowZMod2 (actualRPAlpha n) k} = ⊤ :=
  actualRPAlpha_power_span_eq_top n hn c (construct_RPnCupProductStructure n c) hk

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

