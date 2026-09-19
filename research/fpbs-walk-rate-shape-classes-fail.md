---
rg: 2
id: fpbs-walk-rate-shape-classes-fail
kind: claim
title: No convexity or concavity of the walk rate in any parametrisation can give integrated sensitivity
distinct_from:
  fpbs-integrated-sensitivity-universal: that is the open right-continuity of lambda at p_c; this kills one class of routes to it, the closed shape conditions (convexity or concavity of any increasing transform of lambda or of a_n^(1/n) in any reparametrisation of p)
  fpbs-two-point-state-axioms-admit-collapse: that builds collapsing state families satisfying the infinite-volume axioms; this uses only the plateau structure of the Bernoulli profile and kills shape constraints, which that family does not address
  fpbs-pivotal-budget-universal: that is a quantitative slope bound; this shows scale-free shape classes cannot replace it, since any pointwise-closed class containing arbitrarily steep continuous ramps contains the collapse profile
artifacts:
  - research/artifacts/fpbs/docs/walk-rate-shape-classes-2026-09-19.md
  - experiments/fpbs-is-convexity-2026-09-17/lambda_shape.py
---

**ESTABLISHED for (A), (B) and (D). (C) is an exact-formula computation.**
The proof is in `fpbs-walk-rate-shape-classes-fail-proof`. The artifact has
Sections 1–5.

**Setting.** `G` is a nonamenable Cayley graph with spectral radius `rho < 1`.
Put `a_n(p) = E tau_p(o,X_n)` and `lambda = lim a_n^(1/n)`. Let `phi` be any
homeomorphism from `(0,1)` onto an interval, of either orientation. Let `psi`
be any strictly increasing function on `[rho,1]`. Put
`f = psi o lambda o phi^(-1)`.

* **(A)** `f` is never concave. This holds on every nonamenable Cayley graph.
  The reason is the plateau `lambda = rho` on `(0,p_c]` together with
  `lambda >= p`.
* **(B)** `f` is never convex when `p_u < 1`. This covers one-ended finitely
  presented groups and planar hyperbolic groups. The reason is the plateau
  `lambda = 1` on `(p_u,1)`, which comes from the floor `theta^2`, together
  with `lambda(p_c) = rho < 1`.
* **(C)** On `T_3 box K_2`, where `p_u = 1` and `p_c = 0.38055`, `log lambda`
  is not convex in `log p` on `(0.70, 0.995)`. The formula used is
  `lambda = 1/4 + mu/2 + 1/(4 mu)` past `p_2 = 0.52620`, with `mu` the Perron
  root of the exact ladder transfer. The values match the exact `a_n`
  polynomials to 6 digits.
* **(D)** Imposing the shape only on a domain defined by the percolation, such
  as `{lambda < 1}` or `(0,p_u)`, is vacuous in the collapse scenario.

**Corollary.** These properties pass to pointwise limits, and
`a_n^(1/n) -> lambda` on `(0,1)`. So no statement "each `a_n` is
convex/concave in some parametrisation" holds on these graphs. The
thermodynamic-formalism transplant (pressure as a limit of convex
log-partition functions) is dead for (IS).

**Invariant.** The two forced plateaus of the profile, subcritical at `rho` and
saturation at `1`. Every closed shape class that contains arbitrarily steep
continuous plateau–ramp–plateau profiles also contains the collapse profile.
So any closed route must carry a quantitative modulus at `p_c`.
