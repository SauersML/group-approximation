---
rg: 2
id: stw58-soft-support-reservoir-kernel-vanishing
kind: claim
title: Stably null families in full soft supports contract when an orthogonal reservoir supplies enough Cuntz copies
distinct_from:
  stw58-small-projection-support-kernel-vanishing: this uses positive hereditary supports without spectral gaps or projections, and applies to compact finite-dimensional metric bases.
artifacts:
  - research/artifacts/stw58-soft-support-orthogonal-reservoir-contraction-2026-09-05.md
---

Let \(X\) be compact metric with covering dimension \(d\ge1\), let
\(B\) be unital of stable rank one, and set \(A=C(X,B)\).
Suppose \(h,b\in A_+\) satisfy
\[
h\text{ full in }A,\qquad hb=0,\qquad
(N-1)[h]\le[b]
\]
for an integer \(N\ge d+1\).
Every \(u\in U(A)\) with
\[
u-1\in\operatorname{Her}(h),\qquad [u]=0\text{ in }K_1(A)
\]
belongs to \(U_0(A)\).

In particular \(d[h]\le[b]\) suffices. No projection or spectral
gap is required for either support.

For unital simple finite pure \(B\), full orthogonal positive
contractions \(h,b\), and nonempty \(\mathrm{QT}_1(B)\), it suffices
that there are numbers \(\alpha,\beta\) with
\[
(N-1)\alpha<\beta,\qquad
d_\tau(h(x))\le\alpha,\qquad d_\tau(b(x))\ge\beta
\]
for every \(x\) and every normalized bounded 2-quasitrace \(\tau\)
on \(B\).

For spheres, a stably null based homotopy class satisfying the
support condition has a based contraction. The theorem does not
supply such supports for arbitrary families; the general LVIII
kernel question remains open here.

ROUTES:

- stw58-cutdown-soft-matrix-copies-contraction-proof
