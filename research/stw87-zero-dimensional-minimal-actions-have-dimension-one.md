---
rg: 2
id: stw87-zero-dimensional-minimal-actions-have-dimension-one
kind: claim
title: Minimal zero-dimensional virtually nilpotent crossed products have dimension at most one and PV forces equality
distinct_from:
  stw87-z2-has-no-periodic-boundary-quotient: that claim excludes finite periodic quotients and torus retractions for the full Z2 uniform Roe algebra; this theorem computes minimal zero-dimensional dynamical quotients for a strict virtually nilpotent class.
  stw87-asdim-zero-one-equality: that claim computes uniform Roe algebras when the metric asymptotic dimension is zero or one; this theorem computes crossed products of compact dynamical systems, including quotients of higher-dimensional uniform Roe algebras.
artifacts:
  - research/artifacts/stw87-minimal-boundary-dimension-collapse-audit-2026-08-30.md
---

Let `G` be an infinite finitely generated virtually nilpotent group.  If `G`
acts freely and minimally on a nonempty compact zero-dimensional Hausdorff
space `K`, then, without any metrizability assumption,

```text
dim_nuc(C(K) crossed_product_r G)<=1.                  (VU)
```

If, in addition, the abelianization `G_ab` is infinite, then

```text
dim_nuc(C(K) crossed_product_r G)=1.                   (NM)
```

In particular, let `M` be a minimal nonempty closed `G`-invariant subset of
`beta G`.  For any proper left-invariant metric on `G`, restriction of
coefficients induces a quotient

```text
C*_u(G)=C(beta G) crossed_product_r G
  ->> C(M) crossed_product_r G.                         (BQ)
```

The map annihilates the compact operators and therefore factors surjectively
through the uniform Roe corona.  The algebra on the right has nuclear
dimension at most one, and exactly one when `G_ab` is infinite.  In particular,
for every infinite finitely generated virtually nilpotent group of asymptotic
dimension at least two, these minimal boundary quotients lie strictly below
the target value; hence quotient monotonicity applied to them cannot prove the
missing LXXXVII lower bound.

This strictly extends the nilpotent case.  For example, `Z direct_product S_3`
is virtually cyclic and has infinite abelianization, but is not nilpotent.  If
`T` is a free minimal Cantor `Z`-system, then

```text
(n,s)(y,t)=(T^n(y),st)
```

is a free minimal action of `Z direct_product S_3` on
`Y direct_product S_3`, and its crossed product has nuclear dimension one.
