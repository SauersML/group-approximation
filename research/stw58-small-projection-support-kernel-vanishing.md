---
rg: 2
id: stw58-small-projection-support-kernel-vanishing
kind: claim
title: Stably null families with sufficiently small varying projection support contract
distinct_from:
  stw58-simple-finite-pure-split-stable-surjectivity: this proves vanishing of explicitly supported unstable kernels rather than surjectivity onto stable K-theory.
artifacts:
  - research/artifacts/stw58-small-projection-support-kernel-contraction-2026-09-05.md
---

Let \(X\) be a connected finite CW complex of dimension \(d\ge1\),
let \(B\) be a nonzero unital simple C*-algebra of stable rank one,
and set \(A=C(X,B)\). Let \(p\in A\) be a projection nonzero
at every point, and suppose
\[
d[p]\le[1-p]\quad\text{in }\mathrm{Cu}(A).
\]
Every \(u\in U(A)\) satisfying
\[
u-1=p(u-1)p,\qquad [u]=0\text{ in }K_1(A)
\]
belongs to \(U_0(A)\). More generally, it suffices that
\((N-1)[p]\le[1-p]\) for an integer \(N\ge d+1\).

If \(B\) is also finite and pure, the comparison follows whenever
\(0<p(x)<1_B\) for every \(x\), and there is a number
\(c<1/(d+1)\) with
\[
\tau(p(x))\le c\quad
(x\in X,\ \tau\in\mathrm{QT}_1(B)).
\]

For \(X=S^k\), a based family with zero stable homotopy class
therefore has a based contraction under the corresponding
support hypothesis.

The projection may vary over the base. No localization of an
arbitrary kernel family into such a support is asserted, and
the general LVIII kernel question remains open here.

ROUTES

stw58-projection-copies-and-skeletal-stable-rank-proof
