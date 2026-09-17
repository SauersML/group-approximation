---
rg: 2
id: fpbs-green-visit-kernel-ordering
kind: claim
title: Pivotal budgets, the l2 gap and non-concentration all imply finite expected walk visits to the cluster
distinct_from:
  fpbs-l2-gap-cayley-graphs-satisfy-pivotal-kernels: that verifies PB, IS, NC and RATE under an l2 gap; this places a new, weaker kernel below PB, NC and the gap.
  fpbs-pivotal-nonconcentration-implies-nonuniqueness: that derives nonuniqueness from NC directly; this proves NC implies the weaker visit criterion, which gives nonuniqueness separately.
---

Theorem 3.1(b)–(f) of
`research/artifacts/fpbs/docs/green-visit-kernel-2026-09-17.md`.

**Setting.** `G=Cay(Gamma,S)` is nonamenable, `c=p_c`, `d=|S|`, and `rho` is
the spectral radius of the walk. Let `E_(n,R)`, `N_(n,R)` and `a_(n,R)` be as
in `fpbs-pivotal-budget-universal`. Define

    A(p)     = sum_n a_n(p),
    A_R(p)   = sum_(n<=R) a_(n,R)(p),
    E^tilt_(p,R)[N] = sum_(1<=n<=R) E_p[N_(n,R);E_(n,R)] / A_R(p),

so that `d/dp log A_R = E^tilt/p`. The Green budget (GB) is the statement
that there are `C` and `p0>c` with `E^tilt_(p,R)[N] <= C` for all `R` and all
`p in [c,p0]`.

**Claims.**

* **(b)** GB on `[c,p0]` implies `A(p) <= (p/c)^C/(1-rho)` on `[c,p0]`.
* **(c)** PB, read with the lazy walk, implies GB for the lazy walk.
* **(d)** `||T_(p0)||_(2->2)<infinity` for some `p0>c` implies GB on `[c,p0]`,
  with `C=d||T_(p0)||^2/(1-rho)`.
* **(e)** NC implies `A_L(c+eps)<infinity` for some `eps>0`. Moreover
  `A_L=2A_S`.
* **(f)** `A(p) <= ||tau_p||_2/(1-rho)`.
