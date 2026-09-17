---
rg: 2
id: fpbs-mal-long-generator-packing-growth
kind: claim
title: For Gamma_mal, long single generators of a stage pair have packing floors tending to zero
distinct_from:
  fpbs-malnormal-coset-cycles-linear-perimeter: that proves every fixed generator has finite packing growth and a positive floor; this asks whether the floors of varying generators have infimum zero.
  fpbs-locally-free-malnormally-exhausted-finite-cost: that is the finite-cost goal for the whole malnormally exhausted class; this is one packing certificate for one test group, and it implies only fixed price of Gamma_mal.
---

In `Gamma_mal = U_n H_n`, where `H_m = <a, b_m>` and `b_{m-1} = b_m a b_m^{-2}`,
the packing bound is (2.1) of
`research/artifacts/fpbs/small-cancellation-family.md`, applied to
edge-disjoint detours for a single new generator. The claim has two parts:

- For some fixed `n`, there are `m_j > n` and generators `t_j` with
  `<H_n, t_j> = H_{m_j}`.
- The best packing bound for `(H_{m_j}, H_n, t_j)` tends to `0`.

Equivalently, `inf_j exp(-h_{t_j}) = 0`, where `h_t` is the growth rate of
edge-disjoint `t`-detour families.

**Why it matters.**
- **If it holds.** The triple `(H_m, H_n)`, with basis `{a, b_m}`, is
  isomorphic to `(H_{m-n}, H_0)`. So the same bound holds from every base
  stage. Choose `n_0 < n_1 < ...` with packing bounds `relC(H_{n_{i+1}};
  H_{n_i}) <= 2^{-i} ε`. The stage-sum inequality
  `C <= C(H_{n_0} part) + sum_i relC` then gives cost at most `2 + 2ε` in
  every free action. So every free action of `Gamma_mal` has finite cost. By
  the locally free dichotomy recorded under the target's Attempts (free costs
  are `c*` or `infinity`), `Gamma_mal` has fixed price. This removes the test
  obstruction for `fpbs-locally-free-malnormally-exhausted-finite-cost`.
- **If it fails.** Detour packing with a single generator is dead for
  `Gamma_mal` at every generator choice.

**Where the generators must live.**
- **Double cosets.** By [[fpbs-malnormal-coset-cycles-linear-perimeter]]
  Item 4, the `t_j` must leave `H_n b_{m_j}^{±1} H_n`.
- **Length.** A `t_j`-detour with `H_n`-syllables is also a detour over
  `H_{m_j - 1}`, since `t_j` is not in `H_{m_j-1}`. So Item 3 of that node
  applies with `D = 9`, `r = 2`, and `τ = |t_j|` in the basis `{a, b_{m_j}}`.
  The floor is uniform over bounded `τ`, so `|t_j| -> infinity`.

**Status.** OPEN. The proven floor `(7)^{-2c(τ)}/8` tends to zero as `τ` grows.
That is only a lower bound, and nothing yet produces rich detour families for
long generators.

## Attempts
