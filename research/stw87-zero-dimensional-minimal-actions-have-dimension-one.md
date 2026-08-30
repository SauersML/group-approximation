---
rg: 2
id: stw87-zero-dimensional-minimal-actions-have-dimension-one
kind: claim
title: Free minimal zero-dimensional nilpotent crossed products have nuclear dimension one without metrizability
distinct_from:
  stw87-z2-has-no-periodic-boundary-quotient: that claim excludes finite periodic quotients and torus retractions for the full Z2 uniform Roe algebra; this theorem computes every minimal zero-dimensional dynamical quotient in every positive rank.
  stw87-asdim-zero-one-equality: that claim computes uniform Roe algebras when the metric asymptotic dimension is zero or one; this theorem computes crossed products of compact dynamical systems, including quotients of higher-dimensional uniform Roe algebras.
artifacts:
  - research/artifacts/stw87-minimal-boundary-dimension-collapse-audit-2026-08-30.md
---

Let `G` be an infinite finitely generated nilpotent group acting freely and
minimally on a nonempty compact zero-dimensional Hausdorff space `K`.  No
metrizability assumption is made.  Then

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
dimension exactly one.  In particular, for `G=Z^d` and `d>=2`, these canonical
minimal boundary quotients lie strictly below the target value `d`; hence
quotient monotonicity applied to them cannot prove the missing LXXXVII lower
bound.
