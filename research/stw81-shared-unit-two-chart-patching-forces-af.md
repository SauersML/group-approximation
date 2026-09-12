---
rg: 2
id: stw81-shared-unit-two-chart-patching-forces-af
kind: claim
title: A nonconstant shared-unit scalar transition still forces a projectionless fibre to be AF
distinct_from:
  stw81-projectionless-rotating-overlap-degeneracy: that theorem assumes the two local frames separately return the unit; the present theorem starts only with two scalar-weighted mixtures returning the unit and recovers the separate near-unitality by evaluating at two different cutoff values.
  stw81-stationary-two-colour-interval-patching-forces-af: that theorem copies one stationary fibre frame; the present theorem permits two unrelated local factorizations and permits the unit to be shared between them throughout the transition band.
artifacts:
  - research/artifacts/stw81-shared-unit-two-chart-firewall-2026-08-30.md
---

Let `D` be a separable unital projectionless C-star algebra and fix
`kappa>0`.  Suppose that for every finite set `E` in the unit ball of `D`
and every `epsilon>0` there are two ordinary piecewise-c.p.c. two-colour
factorizations

```text
T^r=sum_(i=0)^1 phi_i^r psi_i^r:D->D,       r=0,1,    (SUT1)
```

and numbers `lambda,mu in [0,1]` such that

```text
abs(lambda-mu)>=kappa,                                (SUT2)
```

both scalar mixtures

```text
lambda T^0+(1-lambda)T^1,
mu T^0+(1-mu)T^1                                     (SUT3)
```

approximate the identity on `E union {1_D}` within `epsilon`.  Assume,
after possibly interchanging the two labels of the second factorization,
that corresponding outgoing colours have orthogonal ranges:

```text
phi_i^0(F_i^0) phi_i^1(F_i^1)=0,       i=0,1.         (SUT4)
```

Then `D` is AF.

Quantitatively, each `T^r` approximates the identity on
`E union {1_D}` within

```text
delta=epsilon(1+2/kappa).                             (SUT5)
```

The two returned unit frames are therefore separately near-unital.  The
projectionless rotating-overlap theorem makes one colour of either frame
vanish in map norm, leaving nuclear-dimension-zero approximations.

Consequently, consider a scalar two-chart interval patch

```text
Phi_t=g(t)T^0+(1-g(t))T^1,       t in J,              (SUT6)
```

where the two local factorizations do not depend on `t`, the two localized
outgoing maps assigned either global colour form one order-zero map, and
the oscillation of `g` on `J` is bounded below independently of the
approximation tolerance.  If these patches approximate the constant
sections of `C(J) tensor D` arbitrarily well, then `D` is AF.  In
particular, for `D=Z`, sharing the unit between two fixed independently
rotated local frames does not evade the stationary or rotating-overlap
firewalls.

For the standard two-anchor architecture the oscillation hypothesis is
automatic.  If the incoming maps factor through evaluations at fixed
`x_0,x_1 in [0,1]`, so the returned approximation has the form

```text
Phi(f tensor a)(t)
 =g(t)f(x_0)T^0(a)+(1-g(t))f(x_1)T^1(a),             (SUT7)
```

then approximation of both `1 tensor 1` and the coordinate function
`id_[0,1] tensor 1` within `epsilon<1/4` forces

```text
osc(g)>=(1-2epsilon)/2>1/4.                           (SUT8)
```

Hence no sequence of ordinary fixed-anchor scalar patches can hide in an
asymptotically flat transition profile.

The conclusion is deliberately architectural, not a nuclear-dimension
lower bound.  A successful two-colour construction for
`C([0,1]) tensor Z` must now make the fibre maps themselves depend on the
base variable through the incoming factorization, or split an outgoing
local colour into smaller pieces before reuse.  Scalar sharing by a
nonconstant partition of unity is insufficient.

DERIVATION
[[stw81-two-point-deconvolution-of-scalar-patches]]
