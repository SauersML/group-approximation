---
rg: 2
id: some-field-crossed-product-fails-rank-from-ternary-cohn-family
kind: route
title: The ternary anti-central summand is a twisted group algebra of the Leavitt unit group modulo minus one, so a Cohn family in it is a field crossed product without the rank condition
target: some-field-crossed-product-fails-the-rank-condition
requires:
  - ternary-anti-central-summand-has-cohn-family
artifacts:
  - research/artifacts/twisted-linear-entropy-profiles-2026-09-17.md
---

1. **Setting.** Let `R = L_(F_3)(1,2)`, `G = R^x` and `z = -1`. The element `z` is central of order 2 in `G`. Put
   `S_- = F_3[G]/(1 + [z])`.
2. **`S_-` is a twisted group algebra.**
   - Choose a set-theoretic section `s: Q = G/<z> -> G` with `s(1) = 1`.
   - Since `[z g] = -[g]` in `S_-`, the images of `[s(q)]` form an `F_3`-basis of `S_-`.
   - `s(q) s(q') = c(q,q') s(qq')` with `c(q,q') ∈ {1, z}`. So `[s(q)][s(q')] = α(q,q') [s(qq')]` with
     `α = ±1`, a 2-cocycle.
   - Hence `S_- ≅ F_3^α[Q]`, a crossed product over the field `F_3` with trivial action.
3. **A Cohn family breaks the rank condition.** The family `tau_i sigma_j = delta_ij 1_-` in `S_-` makes `S_-^2`
   a direct summand of `S_-`. That is an epimorphism `S_- -> S_-^2`, so the rank condition fails with `r = 1`,
   `d = 2`.
4. **Conclusion.** `Q` and `F_3^α[Q]` witness the target.
5. **Consequence.** By `twisted-linear-profile-deficits-are-rank-condition-failures`, every profile-level proof of
   maximal Bernoulli entropy fails on `Q`. The graph's ternary Leavitt lane is therefore a concrete candidate for
   this kill.
