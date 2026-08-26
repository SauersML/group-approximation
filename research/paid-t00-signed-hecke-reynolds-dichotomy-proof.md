---
rg: 2
id: paid-t00-signed-hecke-reynolds-dichotomy-proof
kind: route
title: Expand the signed Reynolds complement and retain the paid discrepancy on its source
target: paid-t00-carrier-has-signed-hecke-reynolds-dichotomy
requires:
  - native-t00-y1-collision-pays-marked-opnorm
  - center-chain-mixed-hecke-overlap-is-common-pauli-source
  - finite-group-opnorm-support-profile
---

Let `C=P_zP_D`.  The collision payment gives `(PSD2)`.  The root `z` is
supported on indices `(1,3)`, while every displayed generator of `L_0` is
supported on indices in `{2,4,5,6,7,8,9}`.  Hence `z` commutes with `L_0`
and with the signed Reynolds projection `Q`.

For `g in L_0`, equation `(PSD2)` and the commutation just noted give

```text
||(1-lambda_0(g)g)C||_op=||(r_g-1)C||_op.             (1)
```

Indeed this is immediate when `lambda_0(g)=+1`; when
`lambda_0(g)=-1`, one has

```text
(zg-1)C=zgC-C=gzC-C=-gC-C=-(g+1)C.                   (2)
```

Expanding the complement of the character average now gives

```text
(1-Q)C
 =|L_0|^(-1) sum_(g in L_0)(1-lambda_0(g)g)C.         (3)
```

Therefore, with

```text
a=||(1-Q)C||_op,
b=max_(g in L_0)||(r_g-1)C||_op,
```

the triangle inequality and `(1)` give

```text
a<=b.                                                 (4)
```

Choose any unit vector `xi` in the nonzero range of `C`.  Since `T,Y` are
unitaries, `||T-Y||_op<=2`; and `(PSD2)` gives
`||(T-Y)xi||=2`.  Hence

```text
||(T-Y)Qxi||
 >=||(T-Y)xi||-||(T-Y)(1-Q)xi||
 >=2-2a.                                              (5)
```

It follows that

```text
(1/2)||(T-Y)Q||_op+b >=(1-a)+b>=1,                   (6)
```

which is `(PSD5)`.  If `b<1/2`, then `(4)` gives `a<1/2`; also

```text
||QCxi||=||Qxi||>=1-||(1-Q)xi||>=1-a>1/2,            (7)
```

and `(5)` gives the last inequality in `(PSD7)`.  Otherwise `(PSD6)`
holds.  The menu is finite, so a detector selected infinitely often is
constant after passage to a subsequence.

All identities above hold in an arbitrary C*-algebra representation.  In a
norm corona they therefore hold exactly.  For a coordinate statement,
`finite-group-opnorm-support-profile` corrects the fixed `L_0` table in the
same matrix dimension, while functional-calculus rounding corrects the
fixed involutions.  Fixed-word telescoping changes `(1)--(7)` by `o(1)`.
