---
rg: 2
id: stable-representation-block-rounding
kind: claim
title: Positive-density almost-reducing blocks of a same-dimension stable group round to exact subrepresentations
distinct_from:
  finite-schur-clifford-packet-flexible-hs-exactification: that exactifies an approximate finite-group table without a prescribed block cut; this starts from one exact representation of an arbitrary same-dimension HS-stable finitely presented group and preserves a positive-density two-block cut.
  iwahori-outlier-repair: that asks to repair an almost edge intertwiner and glue two modular vertices; this only makes an almost-reducing projection exact for one already stable vertex.
---

Let `H=<S|R>` be same-dimension Hilbert--Schmidt stable.  Let
`rho_n:H->U(d_n)` be exact representations and let `P_n` be projections
such that, for one `c>0`,

```text
tr(P_n),1-tr(P_n)>=c,
max_(s in S)||[P_n,rho_n(s)]||_2->0.                 (SBR1)
```

Then there are exact representations on the two physical blocks,

```text
rho_(n,0):H->U(P_n C^(d_n)),
rho_(n,1):H->U((1-P_n) C^(d_n)),                     (SBR2)
```

such that

```text
max_(s in S)||rho_n(s)-(rho_(n,0)(s) directSum
                              rho_(n,1)(s))||_2->0.   (SBR3)
```

**Proof.**  Put `Q_n=1-P_n` and delete the off-diagonal blocks of each
`rho_n(s)`.  The resulting block-diagonal contraction is at normalized HS
distance at most a fixed multiple of `||[P_n,rho_n(s)]||_2`.  Polar-round
its two diagonal blocks to unitaries.  Because each block has normalized
rank at least `c`, ambient normalized-HS convergence implies convergence in
the normalized HS norm of each block, with loss at most `c^(-1/2)`.

Every relator is a fixed word, so the two block tuples have relator defect
tending to zero.  Apply same-dimension stability of `H` separately in the
two fixed physical block dimensions.  Direct-summing the corrected block
representations gives `(SBR3)`.  No padding or commutant spectral gap is
used.
