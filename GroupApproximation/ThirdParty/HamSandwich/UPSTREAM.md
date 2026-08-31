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
remaining closure. `RPnCohomologyRingModel` is green on v4.32. Its type is now
an `abbrev`, allowing v4.32 to reuse the quotient ring's canonical `CommRing`
and `Algebra` instances without mismatched transported instances.
