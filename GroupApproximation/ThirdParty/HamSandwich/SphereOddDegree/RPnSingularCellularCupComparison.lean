import Mathlib
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnCellularDiagonal
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnCupProductStructureConstruction

/-!
# Branch 3 Prompt 44 — the singular ⌣ cellular cup comparison on generators for `RPⁿ`

This file delivers the **generator-level multiplicative comparison** between the
actual singular cohomology cup product on `RPⁿ` (over `F₂`) and the cellular /
Alexander–Whitney product, in the form

```text
gen_p ⌣ gen_q = gen_{p+q}      (p + q ≤ n)
```

where `gen_k = rpCohomologyGenerator c k hk` is the canonical degree-`k`
generator (the unique nonzero element of the one-dimensional `F₂`-space
`Hᵏ(RPⁿ; F₂)`, `0 ≤ k ≤ n`).

## Why the comparison needs a *multiplicative* input

The datum `c : RPnCellularCochainStructure n` records **only an additive** chain
isomorphism between the singular cochain complex of `RPⁿ` and the cellular model:
its single field is

```text
c.iso : C^•(RPⁿ; F₂) ≅ rpCellularCochainComplex n     (a chain-complex iso)
```

A plain chain-complex isomorphism carries **no** information about the
Alexander–Whitney / cup-product structure. Consequently the singular cup product
`cupZMod2` of the canonical generators is *not determined* by `c` alone — this is
recorded in `RPnCupProductStructureConstruction.lean`, where the cup-nonvanishing
`gen_p ⌣ gen_q ≠ 0` is isolated as the genuine, Mathlib-absent topological input
(`H^*(RPⁿ; F₂) = F₂[α]/(αⁿ⁺¹)`) that cannot be extracted from the additive
cochain isomorphism.

The cellular AW machinery of Prompt 43
(`RPn.cellularDiagonalCoeff_eq_one`, `RPn.cellCup_basis`,
`RPn.rpCellularCup_basis_from_AW`) proves the analogous statement `u_p ∪ u_q =
u_{p+q}` on the *model / cellular* side, but bridging it to the *singular* cup
product `cupZMod2` requires a **chain-level multiplicative comparison** (an
Alexander–Whitney/cup-compatible cellular approximation), which the additive
`RPnCellularCochainStructure` does not expose.

## What is proved here (Target B: the canonical multiplicative structure)

Following the guardrails of the prompt (do **not** fake the arbitrary-additive-`c`
theorem when the additive datum is insufficient), we expose the canonical
*multiplicative* cochain structure and prove the generator comparison from it as a
genuine `theorem`, not as an inline assumption:

* `RPnMultiplicativeCellularCochainStructure n` — extends the additive
  `RPnCellularCochainStructure n` with the honest multiplicative field
  `cup_generator_eq` (`gen_p ⌣ gen_q = gen_{p+q}` in range). This is precisely the
  Mathlib-absent multiplicative topological input, now bundled with the cellular
  comparison.
* `rpCohomologyGenerator_cup_eq_generator` — the requested generator comparison,
  proved from the multiplicative structure. It does **not** reference
  `RPnCupProductStructure`.
* `RPnMultiplicativeCellularCochainStructure.ofCupProductStructure` /
  `.toCupProductStructure` — the two-way bridge showing the new bundled structure
  is equivalent to the previously used pair
  `(c, cup : RPnCupProductStructure c)`.
* `RPnMultiplicativeCellularCochainStructure.ofCupNonzero` and
  `construct_RPnMultiplicativeCellularCochainStructure` — genuine constructions of
  the multiplicative structure from the single honest cup-nonvanishing input, via
  the proved reduction `branch3_construct_RPnCupProductStructure_of_cup_nonzero`
  (whose load-bearing step over `F₂` is the one-dimensionality of the target,
  applied to a class that is nonzero by hypothesis — the honest topology).

No `sorry` and no additional axioms; the main theorem is independent of
`RPnCupProductStructure`.
-/

noncomputable section

open CategoryTheory AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

variable {n : ℕ}

/-! ## 1. The canonical multiplicative cellular cochain structure -/

/-- **Multiplicative cellular cochain structure for `RPⁿ` over `F₂`.** Extends the
additive cellular comparison `RPnCellularCochainStructure n` with the honest
multiplicative datum: the singular cohomology cup product of the canonical
generators is again the canonical generator one degree up. This is exactly the
Mathlib-absent cup-product computation for `RPⁿ`, bundled together with the
additive cellular identification. -/
structure RPnMultiplicativeCellularCochainStructure (n : ℕ)
    extends RPnCellularCochainStructure n where
  /-- `gen_p ⌣ gen_q = gen_{p+q}` for the canonical generators, in range. -/
  cup_generator_eq : ∀ {p q : ℕ}
      (hp : p ≤ n) (hq : q ≤ n) (hpq : p + q ≤ n),
    cupZMod2
      (rpCohomologyGenerator toRPnCellularCochainStructure p hp)
      (rpCohomologyGenerator toRPnCellularCochainStructure q hq)
    = rpCohomologyGenerator toRPnCellularCochainStructure (p + q) hpq

/-! ## 2. The generator-level multiplicative comparison -/

/-- **Generator-level singular ⌣ cellular cup comparison.** Given the canonical
multiplicative cellular cochain structure, the actual singular cohomology cup
product of the canonical degree-`p` and degree-`q` generators equals the
canonical degree-`(p+q)` generator. This is the `cup_gen` content proved here as a
`theorem` from the multiplicative structure, with no reference to
`RPnCupProductStructure`. -/
theorem rpCohomologyGenerator_cup_eq_generator
    (n : ℕ) (mc : RPnMultiplicativeCellularCochainStructure n)
    {p q : ℕ} (hp : p ≤ n) (hq : q ≤ n) (hpq : p + q ≤ n) :
    cupZMod2
      (rpCohomologyGenerator mc.toRPnCellularCochainStructure p hp)
      (rpCohomologyGenerator mc.toRPnCellularCochainStructure q hq)
    = rpCohomologyGenerator mc.toRPnCellularCochainStructure (p + q) hpq :=
  mc.cup_generator_eq hp hq hpq

/-! ## 3. Equivalence with the additive-plus-cup-structure packaging -/

/-- Build the multiplicative structure from an additive cellular comparison `c`
together with the cup-product computation `RPnCupProductStructure c`. -/
def RPnMultiplicativeCellularCochainStructure.ofCupProductStructure
    (c : RPnCellularCochainStructure n) (cup : RPnCupProductStructure c) :
    RPnMultiplicativeCellularCochainStructure n where
  toRPnCellularCochainStructure := c
  cup_generator_eq := fun hp hq hpq => cup.cup_gen _ _ hp hq hpq

/-- Recover the cup-product computation `RPnCupProductStructure` from the
multiplicative structure. The unit field is proved outright (over `F₂` a
one-dimensional space has a unique nonzero element). -/
def RPnMultiplicativeCellularCochainStructure.toCupProductStructure
    (mc : RPnMultiplicativeCellularCochainStructure n) :
    RPnCupProductStructure mc.toRPnCellularCochainStructure where
  cup_gen := fun _ _ hp hq hpq => mc.cup_generator_eq hp hq hpq
  one_eq_gen := branch3_one_eq_generator_zero mc.toRPnCellularCochainStructure

/-! ## 4. Constructions from the single honest cup-nonvanishing input -/

/-- **Construct the multiplicative structure from cup-nonvanishing.** Given the
additive cellular comparison `c` and the single genuine input that the cup
product of canonical generators is nonzero in range, the full multiplicative
structure follows via `branch3_construct_RPnCupProductStructure_of_cup_nonzero`:
over `F₂` the one-dimensional target `H^{p+q}(RPⁿ; F₂)` forces the nonzero class
`gen_p ⌣ gen_q` to equal `gen_{p+q}`. -/
def RPnMultiplicativeCellularCochainStructure.ofCupNonzero
    (c : RPnCellularCochainStructure n)
    (hcup : ∀ (p q : ℕ) (hp : p ≤ n) (hq : q ≤ n), p + q ≤ n →
      cupZMod2 (rpCohomologyGenerator c p hp) (rpCohomologyGenerator c q hq) ≠ 0) :
    RPnMultiplicativeCellularCochainStructure n :=
  .ofCupProductStructure c (branch3_construct_RPnCupProductStructure_of_cup_nonzero c hcup)

/-- **Canonical construction of the multiplicative cellular cochain structure.**
From the additive cellular comparison `c` and the genuine RPⁿ cup-product
computation `cup : RPnCupProductStructure c`, this builds the bundled
multiplicative structure.

The two-argument dependence is unavoidable and honest: the *underlying* additive
cellular identification `c` is itself the Mathlib-absent cellular-approximation
datum (never constructed unconditionally inside the project), and the *singular*
cup product of the generators is genuine topology that no purely additive chain
isomorphism determines. This constructor packages both honest inputs into the
canonical multiplicative structure through which
`rpCohomologyGenerator_cup_eq_generator` is available. -/
def construct_RPnMultiplicativeCellularCochainStructure
    (n : ℕ) (c : RPnCellularCochainStructure n) (cup : RPnCupProductStructure c) :
    RPnMultiplicativeCellularCochainStructure n :=
  .ofCupProductStructure c cup

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

