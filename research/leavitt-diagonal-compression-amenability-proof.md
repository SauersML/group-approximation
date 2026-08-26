---
rg: 2
id: leavitt-diagonal-compression-amenability-proof
kind: route
title: Decompose the diagonal Leavitt group into finite cylinder factors
target: leavitt-diagonal-compression-is-elementary-amenable
requires:
  - amenable-implies-operator-mf
---

For words `u,v` of one common length, prefix cancellation gives

```text
(s_ut_u)(s_vt_v)=delta_(u,v)s_ut_u,
sum_(|u|=k) s_ut_u=1.                                 (1)
```

Thus the depth-`k` cylinder idempotents are pairwise orthogonal and span a
copy of `F_2^(2^k)`.  Splitting each cylinder into its two children gives
`D_k<=D_(k+1)` and identifies the union with locally constant functions on
the Cantor set.  Entrywise passage to `3` by `3` matrices yields

```text
EL_3(D_k)=product_(|w|=k) EL_3(F_2)
         =GL_3(F_2)^(2^k),                            (2)
```

because `GL_3(F_2)=SL_3(F_2)=EL_3(F_2)`.  This proves local finiteness.

For a depth-`k` cylinder `e_w=s_wt_w`, equation `(DLC1)` places its
nontrivial action in the `0w` cylinder and acts identically on the `1`
branch.  The branch-exchanged map does the reverse.  Hence their images
commute, intersect trivially, and their product is every depth-`k+1`
locally constant matrix function.  This proves

```text
Lambda_(k+1)=Psi(Lambda_k) x Psi'(Lambda_k).           (3)
```

The coefficient `q=s_1t_1` is a depth-one cylinder idempotent, so
`x_13(q) in Lambda_1`.

Conjugation by the literal rank-twelve compressor realizes `Psi` on the
embedded `EL_3` block.  Therefore `<Lambda,tau>` is a homomorphic image of
the ascending HNN extension `Lambda*_Psi`.  The latter is

```text
(union_(n>=0) tau^(-n)Lambda tau^n) semidirect Z,      (4)
```

where the union is locally finite.  It is elementary amenable, and so is
its image `A_0`.  By `amenable-implies-operator-mf`, `A_0` is MF and its MF
radical is trivial.  Since the displayed mark is nonidentity already in
the elementary matrix group, it is separated by some norm-matrix-corona
homomorphism of `A_0`.  This proves the stated one-compressor firewall.
