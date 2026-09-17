---
rg: 2
id: fpbs-sphere-two-point-rate-below-arccosh-universal
kind: claim
title: Slightly above p_c the sphere two-point growth rate is below arccosh of the inverse spectral radius
distinct_from:
  fpbs-pivotal-nonconcentration-universal: that asks lambda(p)<1 for some p>p_c through pivotal counts; this asks an extrinsic sphere growth bound that implies it, and is strictly stronger on regular trees.
  fpbs-green-visit-criterion-universal: that asks finite expected walk visits to the cluster; this asks a decaying radial tilt of the two-point function to be finite.
  fpbs-critical-sphere-fibre-operator-below-one: that is an operator norm on a hyperbolic quotient at p_c; this is a scalar growth rate of E|K_o ∩ S_r| on the whole graph slightly above p_c.
artifacts:
  - research/artifacts/fpbs/docs/gauge-certificates-and-sphere-rate-2026-09-17.md
---

**OPEN (kernel G).** For every nonamenable Cayley graph, some `p > p_c` has

```text
limsup_r (1/r) log E_p|K_o ∩ S_r|  <  arccosh(1/rho).
```

By `fpbs-sphere-two-point-rate-bounds-walk-rate` this gives `lambda(p) < 1` and
`p_c < p_u`. The route is `fpbs-bs-via-sphere-two-point-rate`.

- **Necessary sanity.** Under uniqueness the rate is `log gr`, and
  `log gr >= arccosh(1/rho)` (artifact Section 4), so (G) fails in the
  collapse scenario, as it must.
- **Calibration.** On `T_d` (G) holds exactly on `(p_c, 1/sqrt(d-1))`.

## Attempts

* **Simon–Lieb certificate for the decaying tilt.** (G) is finiteness of
  `sum_x tau_p(o,x) e^{-t|x|}` for some `t < arccosh(1/rho)`. **Where it
  dies:** the recursion's envelope weight is `e^{t|x|}`, and by
  `fpbs-simon-lieb-gauge-certificates-die-at-pc` its certificate is at least 1
  at every `p >= p_c`.
* **From the l2 gap.** `||T_p|| < infinity` gives `g(p) <= (1/2) log gr`.
  **Where it stops:** `(1/2) log gr` exceeds `arccosh(1/rho)` whenever `rho` is
  near 1. On trees the two coincide only at the endpoint.
