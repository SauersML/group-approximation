---
rg: 2
id: projective-row-gauge-countermodel-proof
kind: route
title: Tensor the native rows by balanced spectator involutions
target: projective-row-data-do-not-authenticate-hecke-polars
requires:
  - center-chain-mixed-hecke-overlap-is-common-pauli-source
---

Let `(M,tr_M)` be a finite matrix algebra containing a packet model, let
`Q,P in M` have equal trace `t`, and let `W,S in P M Q` satisfy

```text
W^*W=S^*S=Q,                 WW^*=SS^*=P.              (1)
```

Let `D=diag(1,-1)` in `M_2(C)` and use the normalized tensor trace.  Put

```text
W_D=W tensor D,              S_0=S tensor 1.            (2)
```

Then `(1)` remains true after amplification.  If `R,T,g` are packet
operators and

```text
WRW^*=T,                     W^2=g,                     (3)
```

then, with all packet operators amplified by `1`,

```text
W_D(R tensor 1)W_D^*=T tensor 1,
W_D^2=g tensor 1.                                        (4)
```

More generally, in every evaluated monomial the spectator factor is the
corresponding power of `D`.  It disappears from every relation having even
total `W`-exponent.  This includes support rows, conjugation covariances,
polar-square identities, and their adjoints.

On the other hand, for every fixed packet-label operator `L in M`,

```text
tr((W_D)^*(LS tensor 1))
 =tr_M(W^*LS) tr_2(D)=0.                                (5)
```

Using `(1)` and `L` unitary on the source/range packet gives

```text
||W_D-LS tensor 1||_2^2
 =||W_D||_2^2+||LS tensor 1||_2^2
 =2t.                                                   (6)
```

Thus the separation is fixed whenever the retained source mass is fixed.
It cannot be charged to the relation defect, since the relations in `(4)`
have defect zero.

For two rows use the regular representation of
`K=<d_1,d_2:d_1^2=d_2^2=[d_1,d_2]=1>~=(C_2)^2` and replace
`W_i` by `W_i tensor lambda_K(d_i)`.  Each nontrivial gauge character has
trace zero, the two modifications are independent, and all internal Hecke
operators remain amplified by `1`.  This proves the stated two-row fence.

The argument deliberately does not apply to a relation with odd gauge
parity, for example `W a=b` with `a,b` ungauged packet words.  Such a row is
exactly the additional occurrence anchor still required.
