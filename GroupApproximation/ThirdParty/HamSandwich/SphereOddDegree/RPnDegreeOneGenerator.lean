import Mathlib
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnCupProductModelCompatibility

/-!
# The model-identified degree-one generator of `RPⁿ` (Prompt 28)

This file identifies the **actual** degree-one cohomology generator of `RPⁿ` over
`F₂` with the degree-one generator `modelAlpha n` of the algebraic model ring
`RPnCohomologyRingModel n = F₂[α]/(αⁿ⁺¹)`.

The additive computation of `RPnSingularToCellularComparison.lean` (Prompt 26)
shows `Hᵏ(RPⁿ; F₂)` is one-dimensional for `k ≤ n` and provides the canonical
generator together with the additive comparison `rpCohomologyToModelToFun c`. The
cup-product compatibility of `RPnCupProductModelCompatibility.lean` (Prompt 27)
upgrades this to a ring bridge `rpCohomologyToModelHom c cup` and computes the
powers in the model ring.

Here we name the unique nonzero degree-one class — the cellular degree-one
generator — as

```text
rpDegreeOneGenerator c : rpCohomology n 1
```

and record:

* `toModel_rpDegreeOneGenerator` : its model image is `modelAlpha n`;
* `rpDegreeOneGenerator_ne_zero` : it is nonzero (for `n ≥ 1`);
* `toModel_rpDegreeOneGenerator_pow` : its `k`-th cup power maps to `modelAlpha n ^ k`.

This is the model-side preparation that prompt 29 will connect to the actual
double-cover class `rpAlpha`/`actualRPAlpha`.

All declarations are conditional on the honest cellular-cochain input
`c : RPnCellularCochainStructure n` (and, for the power theorem, the cup-product
input `cup : RPnCupProductStructure c`); no fake class, ring, or isomorphism is
introduced.
-/

noncomputable section

open CategoryTheory AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

variable {n : ℕ}

/-- **The actual degree-one cohomology generator of `RPⁿ`.** It is the canonical
cellular degree-one generator `rpCohomologyGenerator c 1` when `n ≥ 1` (the unique
nonzero class of the one-dimensional group `H¹(RPⁿ; F₂)`), and `0` in the
degenerate case `n = 0`. It lives in the genuine singular cohomology
`rpCohomology n 1 = H¹(RPⁿ; F₂)`. -/
def rpDegreeOneGenerator (c : RPnCellularCochainStructure n) : rpCohomology n 1 :=
  rpCanonicalAlpha c

/-- **Model image of the degree-one generator.** The additive comparison carries
the actual degree-one generator to the model degree-one generator:
`toModel (rpDegreeOneGenerator c) = modelAlpha n`. -/
theorem toModel_rpDegreeOneGenerator (c : RPnCellularCochainStructure n) :
    rpCohomologyToModelToFun c 1 (rpDegreeOneGenerator c) = modelAlpha n :=
  rpCanonicalAlpha_spec c

/-- The same model-image statement, stated through the ring bridge
`rpCohomologyToModelHom c cup`. -/
theorem toModel_rpDegreeOneGenerator_hom (c : RPnCellularCochainStructure n)
    (cup : RPnCupProductStructure c) :
    (rpCohomologyToModelHom c cup).toFun 1 (rpDegreeOneGenerator c) = modelAlpha n :=
  rpCanonicalAlpha_spec c

/-- The bridge's chosen degree-one class is exactly `rpDegreeOneGenerator c`. -/
theorem rpCohomologyToModelHom_alpha_eq (c : RPnCellularCochainStructure n)
    (cup : RPnCupProductStructure c) :
    (rpCohomologyToModelHom c cup).alpha = rpDegreeOneGenerator c := rfl

/-- **The degree-one generator is nonzero** (for `n ≥ 1`): it is the unique
nonzero class of the one-dimensional group `H¹(RPⁿ; F₂)`. -/
theorem rpDegreeOneGenerator_ne_zero (c : RPnCellularCochainStructure n) (hn : 1 ≤ n) :
    rpDegreeOneGenerator c ≠ 0 := by
  rw [rpDegreeOneGenerator, rpCanonicalAlpha, dif_pos hn]
  exact rpCohomologyGenerator_ne_zero c 1 hn

/-- **Power theorem for the degree-one generator.** The ring bridge carries the
`k`-th cup power of the actual degree-one generator to `modelAlpha n ^ k`:
`toModel ((rpDegreeOneGenerator c)ᵏ) = modelAlpha n ^ k`. -/
theorem toModel_rpDegreeOneGenerator_pow (c : RPnCellularCochainStructure n)
    (cup : RPnCupProductStructure c) (k : ℕ) :
    (rpCohomologyToModelHom c cup).toFun k
        (cupPowZMod2 (rpDegreeOneGenerator c) k)
      = modelAlpha n ^ k :=
  rpCohomologyToModel_cupPow c cup k

/-- **Sub-truncation nonvanishing of the generator's powers.** For `k ≤ n`, the
`k`-th cup power of the degree-one generator is nonzero in `Hᵏ(RPⁿ; F₂)`. -/
theorem rpDegreeOneGenerator_pow_ne_zero (c : RPnCellularCochainStructure n)
    (cup : RPnCupProductStructure c) {k : ℕ} (hk : k ≤ n) :
    cupPowZMod2 (rpDegreeOneGenerator c) k ≠ 0 :=
  rpCanonicalAlpha_cupPow_ne_zero c cup hk

/-- **Top-class nonvanishing of the generator's power:** `αⁿ ≠ 0` in
`Hⁿ(RPⁿ; F₂)`. -/
theorem rpDegreeOneGenerator_pow_top_ne_zero (c : RPnCellularCochainStructure n)
    (cup : RPnCupProductStructure c) :
    cupPowZMod2 (rpDegreeOneGenerator c) n ≠ 0 :=
  rpCanonicalAlpha_cupPow_top_ne_zero c cup

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
