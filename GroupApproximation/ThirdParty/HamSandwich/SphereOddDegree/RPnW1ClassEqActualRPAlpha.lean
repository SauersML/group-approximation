import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.ActualRPAlpha

/-!
# Identifying the Gysin/Smith degree-one class with `actualRPAlpha`

The Smith/Gysin construction uses the degree-one class `rpW1Class n ∈ H¹(RPⁿ; F₂)`,
the cohomology class of the explicit first Stiefel–Whitney cochain `w1Cochain n`
(see `RPnW1Cochain.lean`). The project's canonical class is

```text
actualRPAlpha n : rpCohomology n 1
```

built from the genuine monodromy functional (see `ActualRPAlpha.lean`). This file
proves these two are literally the same cohomology class.

Both classes live in `rpCohomology n 1 = cohomologyZMod2 (TopCat.of (RP n)) 1`
(definitionally), so the identity is a genuine equality of degree-one classes,
not merely an equality of "being nonzero".

The proof is the uniqueness half of the universal coefficient theorem over `F₂`
(`kroneckerMap_injective`): both classes have the *same* Kronecker functional.
Indeed, by definition
`w1Functional n = (kroneckerMap _ 1).hom (rpW1Class n)`, while
`actualRPAlpha_kroneckerMap` gives `(kroneckerMap _ 1).hom (actualRPAlpha n) = w1Functional n`.

## Main declarations

* `rpW1Class_eq_actualRPAlpha` — `rpW1Class n = actualRPAlpha n`.
* `cocycleClass_w1Cochain_eq_actualRPAlpha` — the same identity written with the
  underlying cochain representative used by the Gysin construction.
-/

open CategoryTheory AlgebraicTopology

noncomputable section

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- **Identification of the Gysin/Smith degree-one class with the canonical class.**
The first-Stiefel–Whitney class `rpW1Class n` used by the Smith/Gysin sequence
equals the project's canonical class `actualRPAlpha n`. Both are elements of
`rpCohomology n 1`; equality holds because they share the same Kronecker
functional and the Kronecker classifier over `F₂` is injective (UCT). -/
theorem rpW1Class_eq_actualRPAlpha (n : ℕ) :
    rpW1Class n = actualRPAlpha n := by
  apply kroneckerMap_injective (TopCat.of (RP n)) 1
  rw [actualRPAlpha_kroneckerMap]
  rfl

/-- The same identity, phrased with the explicit cochain representative
`w1Cochain n` used by the Gysin construction (`rpW1Class n` is by definition the
cohomology class `cocycleClass _ 1 (w1Cochain n) (w1Cochain_cocycle n)`). -/
theorem cocycleClass_w1Cochain_eq_actualRPAlpha (n : ℕ) :
    cocycleClass (TopCat.of (RP n)) 1 (w1Cochain n) (w1Cochain_cocycle n)
      = actualRPAlpha n :=
  rpW1Class_eq_actualRPAlpha n

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

