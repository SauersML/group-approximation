---
rg: 2
id: fixed-depth-strict-contractions-have-dilution-escape
kind: claim
title: Every fixed-depth strict-contraction power test has a finite dilution escape
distinct_from:
  positive-density-power-dilation-forces-finite-depth: that proves positive head density makes unbounded coherent depth impossible; this constructs the complementary finite-depth models with head density of order one over the depth.
  depthwise-pauli-packets-have-canonical-regular-escape: that uses the regular representation of each finite Heisenberg packet; this uses finite unitary power dilations of a strict acceptance contraction.
  block-encoded-acceptance-still-needs-corner-return: that identifies a one-step Hecke coefficient; this shows why merely adjoining finitely many further compressed powers cannot promote it.
---

Fix `0<=rho<1` and a depth `N`.  There is a finite-dimensional unitary `U_N`
and a nonzero projection `Q_N` such that

```text
Q_N U_N^n Q_N=rho^n Q_N,       0<=n<=N,                (FDE1)
tr(Q_N)=Theta(1/N).                                        (FDE2)
```

Thus strict contraction plus any fixed finite list of exact compressed-power
relations has an exact finite-dimensional model.  The escape is precisely
head dilution; it is excluded only if an independent canonical packet keeps
`tr(Q_N)` bounded below.

## Construction

The Poisson probability measure `mu_rho` on the unit circle has moments

```text
integral z^n d mu_rho(z)=rho^n,        n>=0.             (FDE3)
```

The vector of real and imaginary parts of the first `N` moments lies in the
convex hull of the corresponding moment curve.  Caratheodory's theorem gives
points `z_1,...,z_K` and positive weights `a_j`, with `K<=2N+1`, matching all
moments through depth `N`.  On `C^K`, let

```text
U_N=diag(z_1,...,z_K),
v=(sqrt(a_1),...,sqrt(a_K)),
Q_N=|v><v|.                                             (FDE4)
```

Then `(FDE1)` follows from `(FDE3)` and `tr(Q_N)=1/K`.  If fewer atoms occur,
repeat or split atoms to obtain `K` comparable to `N` without changing the
moments, giving `(FDE2)`.

The scalar construction is enough to refute any promotion theorem whose only
input is the strict norm bound.  A source-specific compiler must couple all
depths to one fixed positive-density carrier.
