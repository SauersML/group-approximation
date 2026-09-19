---
rg: 2
id: ambient-h1-triviality-need-not-be-short-edge-local
kind: claim
title: Ambient H1 triviality need not be short-edge local
invalidates:
  - torsor-h1-vanishing-gives-spherical-gauge
distinct_from:
  short-edge-gauge-torsor-h1-vanishes: that conditional theorem starts after triviality in the local short-edge coefficient system is known; this firewall shows that ambient triviality does not supply that premise.
  spherical-displacement-length-is-not-conjugation-invariant: that theorem exhibits inflation under arbitrary conjugation; here the local subgroup is preserved exactly and the obstruction is noninjectivity of the map on nonabelian H1.
  a3-cone-repairs-to-coboundaries-not-cocycles: that separates coboundaries from cocycles on a non-simply-connected complex; this separates local from ambient coboundaries for the same cocycle.
artifacts:
  - research/artifacts/d8-ambient-local-h1-firewall-2026-08-30.md
---

There are finite permutation coefficient groups

```text
A <= B,
```

an action of `Q=C2` preserving `A`, and arbitrarily short cocycles
`z in Z^1(Q,A)` such that

```text
[z] != 1 in H^1(Q,A),
[z]  = 1 in H^1(Q,B),
```

while every ambient cochain trivializing `z` has displacement bounded away
from zero.

Concretely, let

```text
B=D8=<r,s | r^4=s^2=1, srs=r^(-1)>,
A=<r^2,s> ~= C2 x C2,
```

and let the generator `q` of `Q` act by `alpha_q=Ad(s)`.  This action is
trivial on `A).  Hence `z(q)=r^2` is a nontrivial class in `H^1(Q,A)`.
But

```text
z(q)=r^(-1) alpha_q(r),
```

so its image in `H^1(Q,B)` is trivial.

This failure persists quantitatively for cloud displacement.  Realize

```text
r=(0 1 2 3),    s=(1 3)
```

and, for `theta>0`, put

```text
x_0=cos(theta)e_1+sin(theta)e_3,
x_2=cos(theta)e_1-sin(theta)e_3,
x_1=cos(theta)e_2+sin(theta)e_4,
x_3=cos(theta)e_2-sin(theta)e_4.
```

Every element of `A` moves points by at most `2 sin(theta)`.  In
particular `z(q)=r^2` and the action implementer `s` are short.  Every
`b in B` satisfying

```text
b^(-1) alpha_q(b)=r^2
```

has odd `r`-parity, hence exchanges the orthogonal clusters
`{0,2}` and `{1,3}` and satisfies

```text
ell_infinity(b)=sqrt(2).
```

Thus exact ambient compatibility—or the ambient correction available for an
actual permutation table—does not imply triviality in the short-edge
coefficient system.

This is not a regular-character table counterexample and does not refute
`short-edge-gauge-torsor-h1-vanishes` or its target.  It invalidates the
present consumer route, which treats ambient table compatibility as sufficient
for the local premise.
