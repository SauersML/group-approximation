import Mathlib
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPAlphaEqualsModelGenerator
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnCupProductModelCompatibility
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnActualAlphaPowerNonvanishing

/-!
# The actual `actualRPAlpha` powers generate and are nonzero (Prompt 30)

This file delivers the **actual top-power theorem** for the canonical
double-cover / first Stiefel–Whitney class `actualRPAlpha n ∈ H¹(RPⁿ; F₂)`
(`ActualRPAlpha.lean`):

```text
(actualRPAlpha n) ^⌣ n ≠ 0      in  Hⁿ(RPⁿ; F₂),
```

together with the stronger **generation** statement that each cup power
`(actualRPAlpha n) ^⌣ k` generates the one-dimensional group `Hᵏ(RPⁿ; F₂)` for
`k ≤ n`.

## Where the nonvanishing comes from (no fake model-only power theorem)

Everything is phrased on the **actual singular cup powers**
`cupPowZMod2 (actualRPAlpha n) k`. The mathematical route is exactly the one
requested:

1. `actualRPAlpha n = rpAlpha n (monodromyFunctional n)` (definitionally), so the
   actual class is genuinely the monodromy class; and the honest cellular/cup
   inputs `c : RPnCellularCochainStructure n`, `cup : RPnCupProductStructure c`
   supply the model bridge `rpCohomologyToModelHom c cup` with
   `toModel (actualRPAlpha n) = modelAlpha n` (Prompt 29,
   `toModel_actualRPAlpha_eq_modelAlpha`);
2. multiplicativity / cup-power compatibility of the bridge
   (`rpAlpha_cupPow_eq_modelPow`) sends `(actualRPAlpha n)^⌣ k` to `modelAlpha n^k`;
3. `modelAlpha n ^ k ≠ 0` for `k ≤ n` (`modelAlpha_pow_ne_zero`).

The decisive new packaging is that the branch-closing
`rpNGeneratorIdentification_of_cellular_cup` (Prompt 29) lets us instantiate the
existing power lemmas of `RPnCupProductGenerator.lean` **at the actual class**,
with no `RPnGeneratorIdentification n` left as a hypothesis: the only inputs are
the honest cellular data `c`, the cup-product data `cup`, and `1 ≤ n`.

All declarations are honest restatements/transports of already-proved facts; no
new model-only power theorem is asserted without the singular-cohomology transport.

Porting changes for Mathlib v4.32:

* add the missing `import ... RPnActualAlphaPowerNonvanishing`. That module
  defines `rpTopClass`, which `rpTopClass_actual_ne_zero` below already
  mentions; without the import `autoImplicit` silently bound `rpTopClass` as a
  variable of unknown type instead of reporting an unresolved name, and the
  file failed only at the point where that variable was applied to `n`. No
  statement changes; the import creates no import cycle.
-/

noncomputable section

open CategoryTheory AlgebraicTopology Module

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-! ## 1. The generator identification carried by the actual class -/

/-- The multiplicative generator identification built from the honest cellular and
cup-product inputs, whose monodromy datum is the **actual** monodromy functional
(so its degree-one class is `actualRPAlpha n`). -/
def actualRPAlphaIdentification (n : ℕ) (hn : 1 ≤ n)
    (c : RPnCellularCochainStructure n) (cup : RPnCupProductStructure c) :
    RPnGeneratorIdentification n :=
  rpNGeneratorIdentification_of_cellular_cup n hn c cup

@[simp] theorem actualRPAlphaIdentification_monodromy (n : ℕ) (hn : 1 ≤ n)
    (c : RPnCellularCochainStructure n) (cup : RPnCupProductStructure c) :
    (actualRPAlphaIdentification n hn c cup).monodromy = monodromyFunctional n := rfl

@[simp] theorem actualRPAlphaIdentification_toModel (n : ℕ) (hn : 1 ≤ n)
    (c : RPnCellularCochainStructure n) (cup : RPnCupProductStructure c) :
    (actualRPAlphaIdentification n hn c cup).toModel = rpCohomologyToModelHom c cup := rfl

/-- The actual class is the degree-one class of `actualRPAlphaIdentification`. -/
theorem rpAlpha_actualRPAlphaIdentification_monodromy (n : ℕ) (hn : 1 ≤ n)
    (c : RPnCellularCochainStructure n) (cup : RPnCupProductStructure c) :
    rpAlpha n (actualRPAlphaIdentification n hn c cup).monodromy = actualRPAlpha n := rfl

/-! ## 2. Cup-power compatibility with the model -/

/-- **Cup-power compatibility for the actual class.** The model bridge carries the
`k`-th singular cup power of `actualRPAlpha n` to `modelAlpha n ^ k`. -/
theorem actualRPAlpha_cupPow_eq_modelPow (n : ℕ) (hn : 1 ≤ n)
    (c : RPnCellularCochainStructure n) (cup : RPnCupProductStructure c) (k : ℕ) :
    (rpCohomologyToModelHom c cup).toFun k (cupPowZMod2 (actualRPAlpha n) k)
      = modelAlpha n ^ k :=
  rpAlpha_cupPow_eq_modelPow (actualRPAlphaIdentification n hn c cup) k

/-! ## 3. Nonvanishing of the actual powers -/

/-- **Sub-truncation nonvanishing for the actual class.** For `k ≤ n` the actual
singular cup power `(actualRPAlpha n) ^⌣ k = cupPowZMod2 (actualRPAlpha n) k` is
nonzero in `Hᵏ(RPⁿ; F₂)`. No `RPnGeneratorIdentification n` is assumed: the inputs
are the honest cellular data `c`, the cup-product data `cup`, and `1 ≤ n`. -/
theorem actualRPAlpha_power_ne_zero (n : ℕ) (hn : 1 ≤ n)
    (c : RPnCellularCochainStructure n) (cup : RPnCupProductStructure c)
    {k : ℕ} (hk : k ≤ n) :
    cupPowZMod2 (actualRPAlpha n) k ≠ 0 :=
  rpAlpha_actual_power_ne_zero (actualRPAlphaIdentification n hn c cup) hk

/-- **The actual top-power nonvanishing** — the load-bearing `αⁿ ≠ 0` for the
genuine class:

```text
cupPowZMod2 (actualRPAlpha n) n ≠ 0   in   Hⁿ(RPⁿ; F₂).
```

This is the key theorem the final odd-degree assembly needs, now available
**without assuming `RPnGeneratorIdentification n`** (only the honest `c`, `cup`,
`1 ≤ n`). -/
theorem actualRPAlpha_topPower_ne_zero (n : ℕ) (hn : 1 ≤ n)
    (c : RPnCellularCochainStructure n) (cup : RPnCupProductStructure c) :
    cupPowZMod2 (actualRPAlpha n) n ≠ 0 :=
  actualRPAlpha_power_ne_zero n hn c cup le_rfl

/-- Restatement in terms of the project's top-class abbreviation
`rpTopClass n m = cupPowZMod2 (rpAlpha n m) n`: the actual top class is nonzero. -/
theorem rpTopClass_actual_ne_zero (n : ℕ) (hn : 1 ≤ n)
    (c : RPnCellularCochainStructure n) (cup : RPnCupProductStructure c) :
    rpTopClass n (monodromyFunctional n) ≠ 0 :=
  actualRPAlpha_topPower_ne_zero n hn c cup

/-! ## 4. The actual powers generate the cohomology groups -/

/-- The bundled additive + multiplicative datum for the actual class: its
generator identification together with the cellular computation `c`. -/
def actualRPAlphaWithAdditive (n : ℕ) (hn : 1 ≤ n)
    (c : RPnCellularCochainStructure n) (cup : RPnCupProductStructure c) :
    RPnGeneratorIdentificationWithAdditive n where
  identification := actualRPAlphaIdentification n hn c cup
  cochain := c

@[simp] theorem actualRPAlphaWithAdditive_identification (n : ℕ) (hn : 1 ≤ n)
    (c : RPnCellularCochainStructure n) (cup : RPnCupProductStructure c) :
    (actualRPAlphaWithAdditive n hn c cup).identification
      = actualRPAlphaIdentification n hn c cup := rfl

/-- **The actual powers generate the cohomology groups.** For `k ≤ n`, every class
in `Hᵏ(RPⁿ; F₂)` is an `F₂`-multiple of the single actual cup power
`(actualRPAlpha n) ^⌣ k`:

```text
∀ w ∈ Hᵏ(RPⁿ; F₂), ∃ d : F₂, d • (actualRPAlpha n) ^⌣ k = w.
```
-/
theorem actualRPAlpha_power_generates (n : ℕ) (hn : 1 ≤ n)
    (c : RPnCellularCochainStructure n) (cup : RPnCupProductStructure c)
    {k : ℕ} (hk : k ≤ n) (w : rpCohomology n k) :
    ∃ d : ZMod 2, d • cupPowZMod2 (actualRPAlpha n) k = w :=
  rpAlpha_power_generates (actualRPAlphaWithAdditive n hn c cup) hk w

/-- **The actual powers span the cohomology groups.** For `k ≤ n`, the singleton
`{(actualRPAlpha n) ^⌣ k}` spans `Hᵏ(RPⁿ; F₂)` over `F₂`. -/
theorem actualRPAlpha_power_span_eq_top (n : ℕ) (hn : 1 ≤ n)
    (c : RPnCellularCochainStructure n) (cup : RPnCupProductStructure c)
    {k : ℕ} (hk : k ≤ n) :
    Submodule.span (ZMod 2) {cupPowZMod2 (actualRPAlpha n) k} = ⊤ :=
  rpAlpha_power_span_eq_top (actualRPAlphaWithAdditive n hn c cup) hk

/-- **The actual powers form a basis.** For `k ≤ n`, the single actual cup power
`(actualRPAlpha n) ^⌣ k` is an `F₂`-basis of the one-dimensional group
`Hᵏ(RPⁿ; F₂)`. -/
noncomputable def actualRPAlpha_power_basis (n : ℕ) (hn : 1 ≤ n)
    (c : RPnCellularCochainStructure n) (cup : RPnCupProductStructure c)
    {k : ℕ} (hk : k ≤ n) : Module.Basis (Fin 1) (ZMod 2) (rpCohomology n k) :=
  rpAlpha_power_basis (actualRPAlphaWithAdditive n hn c cup) hk

@[simp] theorem actualRPAlpha_power_basis_apply (n : ℕ) (hn : 1 ≤ n)
    (c : RPnCellularCochainStructure n) (cup : RPnCupProductStructure c)
    {k : ℕ} (hk : k ≤ n) (i : Fin 1) :
    actualRPAlpha_power_basis n hn c cup hk i = cupPowZMod2 (actualRPAlpha n) k :=
  rpAlpha_power_basis_apply (actualRPAlphaWithAdditive n hn c cup) hk i

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

