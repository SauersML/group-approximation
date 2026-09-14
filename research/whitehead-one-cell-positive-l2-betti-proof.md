---
rg: 2
id: whitehead-one-cell-positive-l2-betti-proof
kind: route
title: χ = 0 turns the L² asphericity criterion into b₁^(2) > 0, then amenable normalish subgroups are excluded
target: whitehead-one-cell-counterexamples-have-positive-first-l2-betti
requires:
  - contractible-complex-minus-cell-has-cyclic-homology
  - finite-2-complex-with-zero-second-l2-betti-is-aspherical
  - amenable-normalish-kills-l2-betti-bounded-cohomology
artifacts:
  - research/artifacts/ideas-topology-2026-09-14.md
---

Notation as in the claim.

1. **Shape of K.** By `contractible-complex-minus-cell-has-cyclic-homology`, K is a finite
   connected 2-complex with χ(K) = 0, and G is infinite.
2. **First L²-Betti number.** Suppose b₁^(2)(G) = 0. Then χ(K) + b₁^(2)(G) = 0, and
   `finite-2-complex-with-zero-second-l2-betti-is-aspherical` makes K aspherical, which is
   excluded. L²-Betti numbers are nonnegative, so b₁^(2)(G) > 0.
3. **Normalish subgroups.** If G contained an amenable normalish subgroup,
   `amenable-normalish-kills-l2-betti-bounded-cohomology` would give b₁^(2)(G) = 0,
   contradicting step 2.
4. **Special cases.** A subgroup H is normalish when every finite intersection of
   conjugates of H is infinite.
   - G is infinite, so G is normalish in itself, and an amenable G is excluded by step 3.
   - An infinite normal subgroup N is normalish, because every conjugate of N is N; so
     an infinite amenable normal subgroup is excluded too.
