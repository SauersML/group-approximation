---
rg: 2
id: stw01-three-projection-corner-pair-is-universal-pair
kind: claim
title: The corner words r_1 r_2 r_1, r_1 r_3 r_1 generate the universal C*-algebra of two positive contractions
distinct_from:
  stw01-modular-test-pair-algebra-is-universal-order-pair: that identifies a pair in C^3*C^2 with the universal algebra of one order pair 0 <= k <= h - h^2; this identifies the corner pair in C^2*C^2*C^2 with the universal algebra of two positive contractions with no relation.
  stw01-three-projection-corner-pair-quasitrace-additivity: that asks whether quasitraces on P_3 add the corner pair; this is the purely C*-algebraic identification of the algebra the pair generates, and says nothing about quasitraces.
artifacts:
  - research/artifacts/stw01-three-projection-corner-pair-test-2026-09-16.md
---

Let `P_3 = C^2 * C^2 * C^2` be the universal unital C*-algebra of three projections
`r_1, r_2, r_3`. Put `h_2 = r_1 r_2 r_1` and `h_3 = r_1 r_3 r_1`, and let
`C = C*(r_1, h_2, h_3)`, a unital C*-subalgebra of the corner `r_1 P_3 r_1` with unit `r_1`.

Let `V` be the universal unital C*-algebra of two elements `h_0, k_0` with `0 <= h_0 <= 1`
and `0 <= k_0 <= 1`, that is, the unital full free product `C([0,1]) * C([0,1])`. Then the
unital *-homomorphism `psi : V -> C` with `h_0 -> h_2` and `k_0 -> h_3` is an isomorphism.

So the compressions of two projections to a third satisfy no relation beyond being positive
contractions. Proof: `stw01-three-projection-corner-pair-is-universal-pair-proof`, and §2 of
`research/artifacts/stw01-three-projection-corner-pair-test-2026-09-16.md`.

**Consequence.** `V` surjects onto `C^3 * C^2`: send `h_0` to `sum_i lambda_i e_i`, with
distinct `lambda_i in (0, 1)`, and `k_0` to `p`. `C^3 * C^2` is not exact
(`stw01-modular-test-pair-generates-non-exact-algebra`). So `C` is not exact, and no exactness
argument applies to any algebra containing the corner pair.
