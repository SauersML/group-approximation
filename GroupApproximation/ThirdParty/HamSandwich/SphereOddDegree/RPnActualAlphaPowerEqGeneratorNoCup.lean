import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnActualAlphaPowerNoCup
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnCupProductStructureConstruction

/-!
# Identifying the actual α-powers with the canonical additive generator (no cup)

Building on Prompt 71's unconditional nonvanishing of the cup powers of the
canonical double-cover class `α = actualRPAlpha n`, this file identifies each such
power with the project's canonical additive cohomology generator
`rpCohomologyGenerator c k hk`, using **only** additive one-dimensionality of
`Hᵏ(RPⁿ; F₂)`.

## Proof

`Hᵏ(RPⁿ; F₂)` is one-dimensional over `F₂` (`rpModTwoCohomology_dim`), so any two
nonzero elements coincide (`eq_of_finrank_one_of_ne_zero`).

* For `k = 0`, `cupPowZMod2 α 0 = 1` is the unit class, which is the degree-zero
  generator by `branch3_one_eq_generator_zero`.
* For `1 ≤ k ≤ n`, both `cupPowZMod2 α k` (Prompt 71
  `actualRPAlpha_power_ne_zero_no_cup`) and `rpCohomologyGenerator c k hk`
  (`rpCohomologyGenerator_ne_zero`) are nonzero, hence equal.

No cup-product / generator-identification structure (`RPnCupProductStructure`,
`RPnGeneratorIdentification`, …) is used to identify the powers.
-/

noncomputable section

open CategoryTheory AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- **Each actual α-power is the canonical additive generator (no cup assumptions).**
For `1 ≤ n` and `k ≤ n`, the `k`-th cup power of the canonical double-cover class
`actualRPAlpha n` equals the canonical additive cohomology generator
`rpCohomologyGenerator c k hk` of the one-dimensional `Hᵏ(RPⁿ; F₂)`. -/
theorem actualRPAlpha_power_eq_rpCohomologyGenerator_no_cup
    (n : ℕ) (hn : 1 ≤ n) (c : RPnCellularCochainStructure n)
    {k : ℕ} (hk : k ≤ n) :
    cupPowZMod2 (actualRPAlpha n) k = rpCohomologyGenerator c k hk := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk1
  · subst hk0
    rw [cupPowZMod2_zero]
    exact branch3_one_eq_generator_zero c
  · exact eq_of_finrank_one_of_ne_zero (rpModTwoCohomology_dim c k hk)
      (actualRPAlpha_power_ne_zero_no_cup n hn hk1 hk)
      (rpCohomologyGenerator_ne_zero c k hk)

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

