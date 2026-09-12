---
rg: 2
id: kazhdan-quotientless-hyperbolic-via-common-quotient
kind: route
title: Add property (T) to a finite-quotient-free hyperbolic group through a common hyperbolic quotient
target: kazhdan-hyperbolic-group-without-finite-quotients
requires:
  - hyperbolic-group-without-finite-quotients
  - torsion-free-hyperbolic-kazhdan-partner-exists
  - olshanskii-g-subgroup-quotient-theorem
artifacts:
  - research/artifacts/hyperbolic-quotientless-kazhdan-proof-2026-09-11.md
---

Section 4 of the artifact proves the construction, including all finite
radical checks. Divide the finite-quotient-free group `G_0` by its finite
radical and call the quotient `G_1`. It is non-elementary hyperbolic and has
trivial finite radical. Choose the stated torsion-free non-elementary
hyperbolic Kazhdan partner `K` and form `H = G_1 * K`.

In the Bass--Serre tree of `H`, edge stabilizers are trivial. A nontrivial
finite subgroup normalized by either factor must fix that factor's unique
fixed vertex, so it is a finite normal subgroup of that factor. Therefore
`E_H(G_1) = E_H(K) = E(H) = 1`. Both index conditions in Olshanskii's
characterization are `1 = 1`. Its simultaneous-surjection theorem supplies
a non-elementary word-hyperbolic quotient `Q` onto which both factors
surject. Property (T) descends from `K`; absence of nontrivial finite
quotients descends from `G_1`; non-elementarity guarantees `Q` is infinite.

Hull's common-quotient theorem (`common-quotient-onto-normal-subgroup`) cannot
replace Olshanskii's here: its quotients are only acylindrically hyperbolic,
and word-hyperbolicity is the whole point of the target.
