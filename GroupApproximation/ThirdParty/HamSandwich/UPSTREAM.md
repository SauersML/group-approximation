# HamSandwich vendoring record

This directory contains a namespace-isolated Lean 4.32 port of the smallest
transitive source slice needed for the Borsuk--Ulam endpoint from
[`akopjan/HamSandwich`](https://github.com/akopjan/HamSandwich).

- Upstream commit: `76202dbbb6610ffcebbccfbf7a56f833a4c2a376`
- Upstream Lean/mathlib: `v4.28.0`, mathlib commit
  `8f9d9cff6bd728b17a24e163c9402775d9e6a365`
- Local target: Lean/mathlib `v4.32.0`
- Upstream license: Apache License 2.0
- Local namespace: `GroupApproximation.ThirdParty.HamSandwich`

The repository root [`LICENSE`](../../../../LICENSE) contains the same Apache
License 2.0 text. Porting changes are recorded in each source file. No theorem
is weakened and no placeholder or additional axiom is permitted in this tree.

## Audited dependency inventory

The upstream static import closure of
`HamSandwich.SphereOddDegree.BorsukUlam` contains 175 project modules, 31,437
lines, and 1,543,822 bytes at the pinned commit. A comment/string-aware scan of
that exact closure found no active occurrence of `sorry`, `admit`, `axiom`,
`constant`, `opaque`, `unsafe`, `implemented_by`, or `extern`.

The upstream kernel audit reports:

```text
'SphereOddDegree.borsuk_ulam' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

## Port status

The first v4.32 incompatibility layer is being ported before importing the
remaining closure. The following modules are green on v4.32:

- `RPnCohomologyRingModel`: its model type is now an `abbrev`, allowing v4.32
  to reuse the quotient ring's canonical instances.
- `AffineBarycentricSubdivision`: its final dependent barycenter rewrite is an
  explicit equality calculation compatible with v4.32.
- `HomotopyToChainHomotopy`: its conclusion is changed directly to the
  `homologyMap` expression before applying the chain-homotopy theorem, avoiding
  a v4.32 functor-whiskering definitional-equality mismatch.
- `Basic`, `Antipodal`, and `RealProjectiveSpace`: namespace-only ports.
- `Covering`: replaces brittle `fin_cases` reductions of the order-two deck
  action by an explicit zero/nonzero split and the already-proved `proj_neg`.
- `AffineLastFaceIdentity`: replaces proof-term generalization and a dependent
  `convert` with an explicit map-composition calculation.
- `Monodromy`: makes the induced multiplicative action transparent to typeclass
  synthesis and spells out the final projection/lift equality.

The old local `SimplicialObjectHomotopy` backport is intentionally not
vendored: Mathlib v4.32 now contains the stronger upstream module
`Mathlib.AlgebraicTopology.SimplicialObject.Homotopy`.

Likewise, Mathlib v4.32 now proves that a `TopCat.Homotopy` induces a chain
homotopy on singular chains. `SingularHomologyHomotopyInvariance` preserves the
upstream public API while discharging `SingularPrismOperator` directly from
`TopCat.Homotopy.singularChainComplexFunctorObjMap`; the old custom prism and
its backports are excluded from the local dependency slice.

The same v4.32 theorem works over arbitrary coefficient modules. The vendored
cohomology homotopy-invariance layer therefore uses Mathlib's `Homotopy.op` and
`TopCat.Homotopy.singularChainComplexFunctorObjMap`, excluding the old
`PrismSimplicialHomotopy` backport. `CupProductScaffolding` reuses Mathlib's
current tensor-additivity instances and enables the same compatibility options
used by Mathlib for downward-complex tensor signs.

`Degree` now unfolds the categorical endomorphism multiplication explicitly,
and `AlexanderWhitney` applies naturality through
`ConcreteCategory.congr_hom`; these are proof-preserving v4.32 API updates.

`CoveringSimplexLift` uses the renamed `LocallyPathConnectedSpace` class, and
`DegreeAPIStrengthening` explicitly closes a post-rewrite reflexive goal.

`CupProduct` uses v4.32's `SSet.ι_chainComplexMap_f` for singular-chain
generators and explicitly closes the definitional conversions around coproduct
inclusions.

`BarycentricSubdivisionDiameter` uses the current singleton-sum identity and
direct `calc` proofs for its one-step and iterated contraction estimates.
