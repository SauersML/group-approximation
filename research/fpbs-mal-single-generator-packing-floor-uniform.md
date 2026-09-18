---
rg: 2
id: fpbs-mal-single-generator-packing-floor-uniform
kind: claim
title: For Gamma_mal, every single-generator detour-packing certificate for every stage pair is at least the constant δ_mal
distinct_from:
  fpbs-malnormal-coset-cycles-linear-perimeter: that proves the uniform floor δ_mal only for generators in H_n b_m^{±1} H_n and leaves other generators open; this removes that restriction for every generator of the stage pair.
  fpbs-mal-long-generator-packing-growth: that conjectured floors tending to zero along long generators; this is its negation, established.
  fpbs-mal-stage-generators-lie-in-b-double-coset: that is the group-theoretic rigidity of generators; this is its consequence for packing certificates.
artifacts:
  - research/artifacts/fpbs-mal-stage-generator-rigidity-2026-09-17.md
---

**ESTABLISHED.** In `Gamma_mal = U_m H_m`, with `H_m = <a, b_m>` and
`b_{m-1} = b_m a b_m^{-2}`, take `n < m` and any `t` with `<H_n, t> = H_m`.
Every packing certificate (2.1) of
`research/artifacts/fpbs/small-cancellation-family.md` for `relC(H_m; H_n)`,
using edge-disjoint `t`-detours, is at least
`δ_mal = δ(F_2, <a, b a b^{-2}>, b) > 0`.

In particular, `inf_j exp(-h_{t_j}) >= δ_mal` along every sequence of stage
pairs `(H_{m_j}, H_n)` with generators `t_j`. This refutes
[[fpbs-mal-long-generator-packing-growth]].

**Proof.**
- **Rigidity.** By [[fpbs-mal-stage-generators-lie-in-b-double-coset]],
  `t ∈ H_n b_m^{±1} H_n`.
- **Import.** Item 4 of
  [[fpbs-malnormal-coset-cycles-linear-perimeter]], verbatim: "Every packing
  certificate for `relC(H_m; H_n)` with new generator `b_m`, or with any
  generator in `H_n b_m^{±1} H_n`, is at least the constant
  `δ_mal = δ(F_2, <a, b a b^{-2}>, b)`".

**Consequence.** Single-generator detour packing cannot certify
`fpbs-fixed-price-universal` for `Gamma_mal`. This covers every stage pair,
every generator, and every growth regime, so both the stage-sum strategy and
the subsequence strategy fail.

**Not claimed.**
- No lower bound on `relC(H_m; H_n)` itself.
- Nothing about multi-generator correlated repairs.
- Nothing about repairs that are not Bernoulli colorings.

## Attempts
