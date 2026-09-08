---
rg: 2
id: padded-rectangular-heat-seed-equivalence-proof
kind: route
title: Start rectangular heat at a supplied padded inclusion and combine with Osgood extraction
target: padded-heat-equates-linear-logarithmic-schreier-seeds
requires:
  - kazhdan-approximate-coefficients-have-curved-hodge-control
  - moving-subgroup-schreier-correction-has-no-index-loss
  - nonhyperlinear-sep7-osgood-extraction
artifacts:
  - research/artifacts/sep7-padded-heat-linear-seed-self-improvement-2026-09-07.md
---

Let rho:SL5->U(D) be exact with n<=D<=2n, and let its full padded
generator error against U direct_sum I_(D-n) be at most eta_0. Start
the required rectangular heat flow at the inclusion J:C^n->C^D.
All rectangular HS norms are normalized by sqrt(n), so

```text
N(0)=1,
E(0)=sum_s ||rho(s)J-JU_s||_(2,n)^2
     <=h eta_0^2 D/n<=2h eta_0^2.
```

Choose eta_0 so 2h eta_0^2<=mu/4. The required curved heat estimate,
at t=log(1/delta)/mu, then gives, below a uniform defect threshold,

```text
N(t)>=1/2,
E(t)<=(mu/4+K0/mu)delta^2.
```

The Rayleigh quotient for Delta=L0/h is E/(hN), proving the first
vector bound with L_0^2=(2/h)(mu/4+K0/mu). A nonzero irreducible
component of the heat vector has no larger Rayleigh quotient. Its
target type has dimension at most D<=2n and occurs in Q_(2n) by
the required universal-host theorem, proving the literal host bound.
No embedding of all multiplicities of rho into its regular host is
needed.

If SL5 is flexibly stable, the fixed coarse eta_0 comparison with
D<=2n exists for every sufficiently small-defect tuple. Otherwise a
sequence of arbitrarily small-defect counterexamples would contradict
the sequence definition of flexible stability. Thus stability implies
the uniform linear seed. This argument assumes stability inside one
direction of the equivalence; it does not conclude stability outright.

The linear seed implies the logarithmic seed at delta<1. Conversely,
given the logarithmic seed, (MSC14) supplies either an exact nonzero
corner or a full padded correction. Its squared corner error and
relative padding are at most K delta^2 log(e/delta^2), where

```text
K=max(h(1+4/kappa)^2 B,4h B/kappa^2).
```

The required established Osgood extraction theorem applies to this
modulus and proves SL5 flexible stability under that seed assumption.
This proves all implications of the equivalence, using only the
three established conditional/analytic theorems listed above.
