import Mathlib
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnSingularCellularCupComparison
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnCupProductNonvanishingTarget
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnDegreeOneGenerator
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPAlphaEqualsModelGenerator
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.ActualRPAlpha

/-!
# Branch 3 Prompt 45 — generator cup nonvanishing and actual α-power nonvanishing

This file derives, from the generator-level singular ⌣ cellular cup comparison of
Prompt 44, the precise nonvanishing witnesses and the α-power theorem for `RPⁿ`
over `F₂`.

## Reconciliation with the prompt's stated signatures

The prompt was written assuming Prompt 44 delivered the generator cup equality

```text
gen_p ⌣ gen_q = gen_{p+q}      (p + q ≤ n)
```

as an *unconditional* statement about the purely additive datum
`c : RPnCellularCochainStructure n`. In reality — as documented in
`RPnSingularCellularCupComparison.lean` — the additive datum carries no
Alexander–Whitney / cup-product information, so the equality was proved from the
honest **multiplicative** input

```lean
mc : RPnMultiplicativeCellularCochainStructure n
```

(the Mathlib-absent computation `H^*(RPⁿ;F₂) = F₂[α]/(αⁿ⁺¹)`, bundled with the
additive cellular identification), via
`rpCohomologyGenerator_cup_eq_generator n mc hp hq hpq`.

Accordingly every theorem here that needs the multiplicative content is
parameterized by `mc`; the results are otherwise exactly those requested. The
guardrails are respected: nothing here consumes an `RPnCupProductStructure c`
(the multiplicative content is consumed only through Prompt 44's `mc`), and
`RPnActualAlphaPowersGenerate.lean` is not imported.

## Contents

* `rpCohomologyGenerator_eq` — the canonical generators are independent of the
  chosen additive datum (over `F₂` a one-dimensional space has a unique nonzero
  element).
* `branch3_rp_generator_cup_ne_zero` — the generator cup product is nonzero.
* `branch3_rp_generator_cup_nonzero_witness` — the cup-nonvanishing witness
  `RPnGeneratorCupNonzeroWitness n` built from the multiplicative datum.
* `rpDegreeOneGenerator_cupPow_eq_generator_of_mult` — `αᵏ = gen_k` for the
  cellular degree-one generator.
* `actualRPAlpha_cupPow_eq_generator_from_prompt44` /
  `actualRPAlpha_power_ne_zero_from_prompt44` — the same for the actual
  double-cover / `w₁` class `actualRPAlpha n`, and its nonvanishing.

No `sorry`, no new axioms.
-/

noncomputable section

open CategoryTheory AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

variable {n : ℕ}

/-! ## 0. The canonical generators do not depend on the additive datum -/

/-- **The canonical generator is independent of `c`.** For `k ≤ n` the group
`Hᵏ(RPⁿ; F₂)` is one-dimensional over `F₂`, hence has a unique nonzero element;
both `rpCohomologyGenerator c k hk` and `rpCohomologyGenerator c' k hk` are nonzero,
so they coincide. -/
theorem rpCohomologyGenerator_eq
    (c c' : RPnCellularCochainStructure n) (k : ℕ) (hk : k ≤ n) :
    rpCohomologyGenerator c k hk = rpCohomologyGenerator c' k hk :=
  eq_of_finrank_one_of_ne_zero (rpModTwoCohomology_dim c k hk)
    (rpCohomologyGenerator_ne_zero c k hk) (rpCohomologyGenerator_ne_zero c' k hk)

/-! ## 1. Generator cup nonvanishing -/

/-- **Generator cup nonvanishing.** The singular cohomology cup product of the
canonical degree-`p` and degree-`q` generators is nonzero whenever `p + q ≤ n`.
By Prompt 44 it equals the canonical degree-`(p+q)` generator, which is nonzero. -/
theorem branch3_rp_generator_cup_ne_zero
    (n : ℕ) (mc : RPnMultiplicativeCellularCochainStructure n)
    {p q : ℕ} (hp : p ≤ n) (hq : q ≤ n) (hpq : p + q ≤ n) :
    cupZMod2
      (rpCohomologyGenerator mc.toRPnCellularCochainStructure p hp)
      (rpCohomologyGenerator mc.toRPnCellularCochainStructure q hq) ≠ 0 := by
  rw [rpCohomologyGenerator_cup_eq_generator n mc hp hq hpq]
  exact rpCohomologyGenerator_ne_zero mc.toRPnCellularCochainStructure (p + q) hpq

/-! ## 2. The cup-nonvanishing witness -/

/-- **The cup-nonvanishing witness.** From the multiplicative datum `mc`, build the
`RPnGeneratorCupNonzeroWitness n` required by the existing reduction. The witness
quantifies over an arbitrary additive datum `c`, which is harmless because the
canonical generators are `c`-independent (`rpCohomologyGenerator_eq`). -/
def branch3_rp_generator_cup_nonzero_witness
    (mc : RPnMultiplicativeCellularCochainStructure n) :
    RPnGeneratorCupNonzeroWitness n where
  nonzero := fun c p q hp hq hpq => by
    rw [rpCohomologyGenerator_eq c mc.toRPnCellularCochainStructure p hp,
        rpCohomologyGenerator_eq c mc.toRPnCellularCochainStructure q hq]
    exact branch3_rp_generator_cup_ne_zero n mc hp hq hpq

/-! ## 3. Powers of the cellular degree-one generator -/

/-- **`αᵏ = gen_k` for the cellular degree-one generator.** For `k ≤ n`, the `k`-th
cup power of the cellular degree-one generator equals the canonical degree-`k`
generator. Proved by induction on `k` using Prompt 44's generator cup equality;
the multiplicative content is consumed only through `mc`. -/
theorem rpDegreeOneGenerator_cupPow_eq_generator_of_mult
    (n : ℕ) (mc : RPnMultiplicativeCellularCochainStructure n)
    {k : ℕ} (hk : k ≤ n) :
    cupPowZMod2 (rpDegreeOneGenerator mc.toRPnCellularCochainStructure) k
      = rpCohomologyGenerator mc.toRPnCellularCochainStructure k hk := by
  induction k with
  | zero =>
      rw [cupPowZMod2_zero]
      exact branch3_one_eq_generator_zero mc.toRPnCellularCochainStructure
  | succ k ih =>
      have hk' : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      have h1 : 1 ≤ n := Nat.le_trans (Nat.le_add_left 1 k) hk
      have hα : rpDegreeOneGenerator mc.toRPnCellularCochainStructure
          = rpCohomologyGenerator mc.toRPnCellularCochainStructure 1 h1 := by
        rw [rpDegreeOneGenerator, rpCanonicalAlpha, dif_pos h1]
      rw [cupPowZMod2_succ, ih hk', hα]
      exact rpCohomologyGenerator_cup_eq_generator n mc hk' h1 hk

/-! ## 4. Powers of the actual double-cover / `w₁` class -/

/-- **Actual α-powers equal the generators.** For `n ≥ 1` and `k ≤ n`, the `k`-th
cup power of the actual double-cover / `w₁` class `actualRPAlpha n` equals the
canonical degree-`k` generator. The class is identified with the cellular
degree-one generator (`actualRPAlpha_eq_rpDegreeOneGenerator`) and the power
theorem is applied; the RHS is `c`-independent. -/
theorem actualRPAlpha_cupPow_eq_generator_from_prompt44
    (n : ℕ) (hn : 1 ≤ n) (mc : RPnMultiplicativeCellularCochainStructure n)
    (c : RPnCellularCochainStructure n)
    {k : ℕ} (hk : k ≤ n) :
    cupPowZMod2 (actualRPAlpha n) k
      = rpCohomologyGenerator c k hk := by
  rw [rpCohomologyGenerator_eq c mc.toRPnCellularCochainStructure k hk,
      actualRPAlpha_eq_rpDegreeOneGenerator n hn mc.toRPnCellularCochainStructure]
  exact rpDegreeOneGenerator_cupPow_eq_generator_of_mult n mc hk

/-- **Actual α-power nonvanishing.** For `n ≥ 1` and `k ≤ n`, the `k`-th cup power
of `actualRPAlpha n` is nonzero, being the nonzero canonical degree-`k` generator.
In particular the top power `αⁿ ≠ 0`. -/
theorem actualRPAlpha_power_ne_zero_from_prompt44
    (n : ℕ) (hn : 1 ≤ n) (mc : RPnMultiplicativeCellularCochainStructure n)
    {k : ℕ} (hk : k ≤ n) :
    cupPowZMod2 (actualRPAlpha n) k ≠ 0 := by
  rw [actualRPAlpha_cupPow_eq_generator_from_prompt44 n hn mc
      mc.toRPnCellularCochainStructure hk]
  exact rpCohomologyGenerator_ne_zero mc.toRPnCellularCochainStructure k hk

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

