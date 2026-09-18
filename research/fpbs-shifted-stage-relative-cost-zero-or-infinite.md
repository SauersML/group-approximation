---
rg: 2
id: fpbs-shifted-stage-relative-cost-zero-or-infinite
kind: claim
title: Under a stage-shifting automorphism, the relative cost of an invariant free action over each stage is the same at every stage and is 0 or infinity; for the Bernoulli shift of Gamma_mal, cost 2 iff one stage has relative cost 0
distinct_from:
  fpbs-locally-free-free-action-costs-are-c-star-or-infinite: that says the total cost is c* or infinity; this says the relative cost over each stage is 0 or infinity, and is independent of the stage, for shift-invariant actions such as Bernoulli shifts.
  fpbs-malnormal-coset-cycles-linear-perimeter: that is a positive floor for packing certificates only; this is an exact 0-or-infinity dichotomy for relC itself, over all graphings, for theta-invariant actions.
  fpbs-mal-long-generator-packing-growth: that is an open certificate that would give relative cost tending to 0; this shows that for the Bernoulli shift, tending to 0 already forces exactly 0 at every stage.
artifacts:
  - research/artifacts/fpbs-shifted-stage-relative-cost-zero-or-infinite-2026-09-17.md
---

**ESTABLISHED** through `fpbs-shifted-stage-relative-cost-zero-or-infinite-proof`.

Let `Gamma = U_n H_n` be an increasing union of subgroups, and let `theta` be
an automorphism of `Gamma` with `theta(H_n) = H_{n+1}`. Let `a` be a free
p.m.p. action with `T a(g) T^{-1} = a(theta g)` for some measure-preserving
`T`. Write `E = E_a` and `R_n = E_{a|H_n}`, and assume `C(R_0) < infinity`.
Then:
- `relC(E; R_n)` does not depend on `n`;
- either `C(a) < infinity` and `relC(E; R_n) = 0` for all `n`, or
  `C(a) = infinity` and `relC(E; R_n) = infinity` for all `n`;
- every Bernoulli shift of `Gamma` is free and theta-invariant.

**Gamma_mal.** `theta(a) = a`, `theta(b_k) = b_{k+1}` is a stage shift of
`Gamma_mal = U_m <a, b_m>`. Let `beta` be its Bernoulli shift, or any
theta-invariant free action, for instance the restriction of any free action of
`M = F_2 *_phi`. Then `C(beta) = 2` iff `relC(E_beta; E_{beta|H_1}) = 0`.
Otherwise `C(beta) = infinity` and every stage has relative cost `infinity`.

**Consequence.** Shape (B) for the Bernoulli shift of `Gamma_mal` needs a
positive lower bound at one stage, not a floor uniform in the stage. That open
test is `fpbs-mal-bernoulli-single-stage-floor`.

## Attempts
