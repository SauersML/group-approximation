---
rg: 2
id: regular-cyclic-twisted-core-has-non-fp-stabilizer-engine
kind: claim
title: The regular cyclic twisted Brin–Thompson group T = Z V_Z is infinite, finitely generated, simple and decidable, yet no group between D(F_T) and F_T is finitely presented, for any k >= 2
distinct_from:
  regular-cyclic-twisted-core-is-decidable-mif-non-fp: that is the input fact that T is decidable, simple and not finitely presented; this is the consequence for its stabilizer engine.
  bffhz-computable-core-fp-upgrade-is-false: that uses the same T against the BFFHZ relative-automorphism upgrade; this uses it against the stabilizer-engine route.
---

**ESTABLISHED** by `regular-cyclic-twisted-core-engine-counterexample-proof` (lane
proof, swarm-0917-w12-w12-bh-last1, 2026-09-18; not reviewed).

## Statement

Let `T = Z V_Z` be the regular cyclic twisted Brin–Thompson group of
`regular-cyclic-twisted-core-is-decidable-mif-non-fp`. It is not Thompson's circle
group. Fix `k >= 2`, and let `F_T` be the stabilizer engine of `Z/k * T`, with commutator
subgroup `D(F_T)`. Then:

1. `T` is an infinite, finitely generated, simple group with solvable word problem.
2. No group `E` with `D(F_T) ≤ E ≤ F_T` is finitely presented. In particular `D(F_T)`
   and `F_T` are not finitely presented.

## Consequence

- **The hole is false.** With `k = 2`, the claim
  `simple-inputs-have-finitely-presented-stabilizer-engines` is false, and `T` is a
  counterexample.
- **Decidability is not enough.** The necessary condition in
  `fp-stabilizer-engines-need-decidable-vertex-groups` (solvable word problem) holds for
  `T`, but it is not sufficient.
