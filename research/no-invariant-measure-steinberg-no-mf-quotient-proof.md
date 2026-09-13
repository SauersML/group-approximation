---
rg: 2
id: no-invariant-measure-steinberg-no-mf-quotient-proof
kind: route
title: No state normalizes [X], so Tarski gives 2n[X] <= n[X], and the type semigroup maps into V of the Steinberg algebra
target: no-invariant-measure-steinberg-elementary-no-mf-quotient
requires:
  - rainone-sims-tarski-alternative-for-monoids
  - abbl-type-semigroup-states-extend-to-invariant-measures
  - stably-infinite-ring-elementary-groups-have-no-mf-quotient
artifacts:
  - research/artifacts/un-paradox-groupoid-tarski-2026-09-13-part2.md
---

## Why sufficient

1. **No normalized state.** A state `ν` on `S(𝒢)` with `ν[X] = 1` would extend to an invariant Borel
   measure with `μ(X) = 1` (`abbl-type-semigroup-states-extend-to-invariant-measures`). No such
   measure exists, so there is no such state.
2. **Tarski.** By `rainone-sims-tarski-alternative-for-monoids`, `(k+1)[X] <= k[X]` for some `k`.
   Adding `[X]` repeatedly gives `2k[X] <= k[X]`.
3. **Into `V`.**
   - For a compact open bisection `V`, `1_V * 1_(V^(-1)) = 1_(r(V))` and
     `1_(V^(-1)) * 1_V = 1_(s(V))`. This is a direct computation, since `s` is injective on `V`.
   - So `1_(r(V))` and `1_(s(V))` are algebraically equivalent idempotents.
   - Disjoint unions go to orthogonal sums.
   - By ABBL's presentation of `S(𝒢)`, `[U] ↦ [1_U A_k(𝒢)]` is a monoid homomorphism into `V(A_k(𝒢))`
     sending `[X]` to `[1]`. It preserves the algebraic preorder.
   - Hence `2k[1] <= k[1]` in `V(A_k(𝒢))`.
4. **Conclusion.** `A_k(𝒢)` is countable, since `𝒢` is second countable. Apply
   `stably-infinite-ring-elementary-groups-have-no-mf-quotient` with `n = k`.

If `2[X] <= [X]` already holds in `S(𝒢)`, step 3 gives `n = 1` directly.
