---
rg: 2
id: fpbs-fibre-summed-connectivity-operator
kind: claim
title: The connectivity operator is bounded by its fibre sum on a quotient group, with equality for amenable kernels
distinct_from:
  fpbs-nonamenability-bounds-critical-connectivity-operator: that is Hutchcroft's open L2 conjecture for the whole connectivity operator; this is a proved norm comparison that moves that operator to a nonnegative convolution kernel on a quotient group.
artifacts:
  - research/artifacts/fpbs/docs/fibre-summed-hyperbolic-quotient-criterion.md
---

**ESTABLISHED.** Let `Gamma` be finitely generated with finite symmetric
generating set `S`, let `H` be a normal subgroup, `Q = Gamma/H`, and let
`T_p(x,y) = P_p(x <-> y)` for Bernoulli bond percolation on `Cay(Gamma,S)`.
Put `sigma_p(q) = sum_{x in q} P_p(o <-> x)` and let `S_p` be convolution by
`sigma_p` on `l2(Q)`. Then for every `p`,

```text
||T_p||_{l2(Gamma) -> l2(Gamma)}  <=  ||S_p||_{l2(Q) -> l2(Q)}     (in [0, infinity]),
```

with equality when `H` is amenable. In particular, for amenable `H` one has
`E_p|K_o ∩ H| <= ||T_p||`. So Hutchcroft's L2 boundedness condition at `p_c`
holds on `Cay(Gamma,S)` if and only if `S_(p_c)` is bounded on `l2(Q)`.

The inequality is Schur's test on the fibre blocks, whose row and column sums
all equal `sigma_p(q^(-1) q')`. Equality uses the weak containment of the
quasi-regular representation `l2(Gamma/H)` in `l2(Gamma)` for amenable `H`.
Proof in Section 1 of the artifact.
