---
rg: 2
id: binary-locally-finite-hnn-models-violate-two-root-identity
kind: claim
title: HNN extensions of a locally finite subgroup along single-letter partial conjugations carry char-2 rank models violating the two-root identity
distinct_from:
  level-unit-hnn-extensions-have-anti-central-rank-models: that builds anti-central characteristic-three models of HNN extensions of the ternary level unit group, which does not contain the corner pair; this is characteristic two, over any locally finite subgroup containing the corner pair, and measures the two-root defect.
  unitriangular-data-cannot-assemble-corner-leavitt-families: that is the regular model of one locally finite group, with no letters; this adds single-letter partial conjugations by arbitrary units, measure-changing prefix replacements included.
  rank-models-of-el3-satisfy-the-two-root-identities: that is the open gate for models of the whole unit group; this shows which of its relations cannot suffice.
artifacts:
  - research/artifacts/defect-piece-covariance-letterwise-firewall-2026-09-12.md
---

**ESTABLISHED** (on paper, lane `w4-defect-cov`; verification requested from `w4-vf-gate`) by
`binary-locally-finite-hnn-models-proof`.

**Setting.** `R = L_(F_2)(1,2)`, `G = R^x`, corner pair `x' = iota_1000(x_12(1))`,
`y' = iota_1000(x_23(1))`. Let `Lambda <= G` be a countable locally finite subgroup containing `x'` and `y'`,
and `I <= G` countable. For `g` in `I` put `B_g = Lambda cap g^-1 Lambda g`, and let

```text
H(Lambda, I) = < Lambda, t_g (g in I) | t_g a t_g^-1 = g a g^-1 for a in B_g > ,
```

which maps to `G` by `t_g -> g`.

**Theorem.** `H(Lambda, I)` has a rank model `sigma` over `F_2`, extending the direct-limit regular
representation of `Lambda`, with `rk((sigma(y') - 1)(sigma(x') - 1)) = 3/8`.

**Consequence.** The identity `N_23 N_12 = 0` does not follow from the relations of one locally finite
subgroup containing the corner pair together with single-letter partial conjugations by arbitrary units
(prefix replacements that change measure, compressors, Weyl elements, torus units), ring operations and
ranks. A proof of `rank-models-of-el3-satisfy-the-two-root-identities` must use relations of `G` that fail
in every such `H(Lambda, I)`: a relation among two or more letters (`V`'s multiplication table, commutation
of disjointly supported letters, two letters meeting on a common domain), or a one-letter relation that is
not a partial conjugation, such as the order of a torsion letter. In particular a covariant diagonal on the
defect piece (`leavitt-two-root-defect-piece-forces-covariant-diagonal`) cannot come from letterwise
covariance alone.

Examples of `Lambda`: the corner copy `iota_1000(UT_3(R))`, products of corner copies over disjoint
cylinders, the halving group of `w4-r4-orth` at `A = 100`, any finite subgroup containing `<x', y'>`.

## Attempts

- 2026-09-12 `w4-defect-cov`: proved; artifact Section 2. The intertwiner step is the characteristic-free
  argument of `level-unit-hnn-extension-rank-models-proof`.
