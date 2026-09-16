---
rg: 2
id: fpbs-hyperbolic-3-manifold-via-outer-cyclic-extension
kind: route
title: Pass to a fibered cover and apply the cyclic-extension statement, or the outer-kernel lemma when the monodromy has finite outer order
target: fpbs-hyperbolic-3-manifold-groups-fixed-price-one
requires:
  - fpbs-bounded-cost-outer-cyclic-extension-price-one
  - fpbs-amenable-outer-kernel-forces-price-one
  - fpbs-fibered-3-manifold-cost-inputs
artifacts:
  - research/artifacts/fpbs-normal-bounded-cost-quotient-trichotomy-2026-09-16.md
---

Written derivation. It is Section 4 of the linked artifact.

1. **Fibered cover.** Let `M` be a closed hyperbolic 3-manifold, and
   `Gamma = pi_1(M)`.
   - By item 1 of `fpbs-fibered-3-manifold-cost-inputs`, a finite cover `M'`
     fibers over the circle with closed fiber `S` of genus `g >= 2`.
   - So `Gamma' = pi_1(M') ≅ N semidirect_phi Z` has finite index in `Gamma`.
     Here `N = pi_1(S)` and `phi` is the monodromy.
2. **Bounded cost.** By item 2, every free p.m.p. action of `N` has cost
   `2g-1`.
3. **`Gamma'` has fixed price one.**
   - If `[phi]` has infinite order in `Out(N)`,
     `fpbs-bounded-cost-outer-cyclic-extension-price-one` applies.
   - If `[phi]` has finite order `k`, the outer kernel of `Gamma'/N = Z` is
     `kZ`. That is an infinite amenable subgroup, so
     `fpbs-amenable-outer-kernel-forces-price-one` applies.
4. **Transfer.**
   - Let `Gamma` act freely p.m.p. Its restriction to `Gamma'` is free, so it
     has cost one.
   - By item 3 (commensurated transfer, finite index), the cost of the `Gamma`
     action is at most one.
   - The orbits are infinite, so the cost is exactly one.

**Comparison.** This premise set is weaker than that of
`fpbs-hyperbolic-3-manifold-fixed-price-via-normal-subgroup`, which needs the
full `fpbs-normal-subgroup-bounded-cost-fixed-price-one`. Here only the
cyclic-quotient case is open.

This is dependency bookkeeping for a written deduction, not a formal
verification.
