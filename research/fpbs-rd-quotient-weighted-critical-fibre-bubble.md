---
rg: 2
id: fpbs-rd-quotient-weighted-critical-fibre-bubble
kind: claim
title: Over a hyperbolic quotient the critical fibre bubble is finite against a polynomial weight
distinct_from:
  fpbs-hyperbolic-quotient-uniform-fibre-bubble: that is the unweighted critical fibre bubble; this adds the polynomial weight (1+|q|)^(2D+2), which makes it sufficient for the L2 gap on its own, without the far-halfspace share.
  fpbs-tree-projected-critical-sphere-bubble-below-one: that asks for one finite-radius critical sphere bubble below one on tree-projected generating sets, which gives exponential decay there; this asks for polynomially weighted summability on every generating set of every group in the class.
artifacts:
  - research/artifacts/fpbs/docs/rd-weighted-fibre-bubble-criterion.md
---

**OPEN.** Let `Gamma` be finitely generated with an infinite normal subgroup
`H` such that `Q = Gamma/H` is non-elementary word hyperbolic, let `S` be a
finite symmetric generating set, and let `D` be a rapid decay exponent of `Q`
for the word length from `pi(S)`. Then

```text
W_D = sum_{q in Q} (1+|q|)^(2D+2) sigma_(p_c)(q)^2  <  infinity,
where sigma_p(q) = E_p|K_o ∩ q|.
```

By monotone convergence this equals the supremum of the same sum over
`p < p_c`. With `fpbs-rd-quotient-weighted-bubble-gives-critical-l2` and
`hyperbolic-groups-have-property-rd` it gives `p_c < p_u` on every Cayley graph
in the class. It implies the unweighted premise
`fpbs-hyperbolic-quotient-uniform-fibre-bubble`. The far-halfspace share is not
needed on this route.

## Attempts

* **Mean-field prediction.** For critical branching random walk, the fibre
  occupation is the projected Green function. Its weighted bubble is finite for
  every polynomial weight, because `rho(Q) < 1` (artifact Section 3). **Where it
  stops:** comparing percolation with branching random walk is a triangle-type
  input.
* **Tree-projected generating sets.** Fibres are cut sets, so a single
  `b_(R_0)(p_c) < 1` gives exponential decay of `b_R`, hence `W_D < infinity` for
  every `D` (artifact Section 4). **Where it stops:** that finite-radius bound is
  the open `fpbs-tree-projected-critical-sphere-bubble-below-one`.
* **Differential inequality.** Russo plus BK push forward to weighted fibre sums,
  but the growth rate is an L2-type operator norm of `S_p`. **Where it dies:** the
  same barrier as the unweighted bubble.
* **One-ended quotients (corrected 2026-09-12).** For surface-group bases, as in
  the Seifert-fibred case, no single fibre separates the Cayley graph. But the
  fibre saturation `pi^(-1)(S_Q(R))` of a sphere separates every Cayley graph over
  every quotient.
  * BK at the first crossing gives `T_{R+m} <= ||lambda(sigma_R)||^2 T_m`
    (`fpbs-sphere-cut-fibre-tails-decay-exponentially`).
  * So this premise is equivalent to one finite-radius condition,
    `||lambda_Q(sigma_{p_c} 1_{S_Q(R_0)})|| < 1` for some `R_0`, and to exponential
    decay of critical fibre tails
    (`fpbs-rd-weighted-bubble-iff-sphere-fibre-operator-below-one`).

  **Where it stops:** that single-radius condition is the open
  `fpbs-critical-sphere-fibre-operator-below-one`.
* **Upgrading the unweighted bubble.** For amenable `H` the unweighted bubble is
  necessary for the L2 gap (`fpbs-amenable-kernel-l2-gap-forces-fibre-bubble`),
  and this weighted bubble is sufficient. **Where it stops:** no mechanism turns
  square summability of sphere bubbles into polynomially weighted summability
  without a decay input.
