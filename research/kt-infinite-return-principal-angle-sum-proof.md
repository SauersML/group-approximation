---
rg: 2
id: kt-infinite-return-principal-angle-sum-proof
kind: route
title: Sum reverse compressor leakage over arbitrarily many edge cosets
target: kt-infinite-index-returns-force-divergent-edge-leakage
requires:
  - kt-return-expectation-pays-one-full-edge-principal-angle
  - kt-intrinsic-subfactor-data-does-not-see-ambient-wall
---

Fix `N`.  Infinite index in `(KDL1)` supplies representatives
`gamma_1,...,gamma_N` of distinct nonidentity left `Lambda`-cosets.  If
`h_i=t^(-1)gamma_i t` belonged to `Gamma`, then
`gamma_i` would belong to `t Gamma t^(-1)=Lambda`, a contradiction.  The
elements `gamma_i` are distinct, so canonical character convergence and
approximate multiplicativity give

```text
G_n->I_N.                                                 (KDP1)
```

Work on `L2(M_(d_n),tr_n)`.  Write `W_n=Ad(T_n)` and

```text
R_n=(1-P_n)W_n^*P_n.
```

For `b_(i,n)=phi_n(gamma_i)`, the same Pythagorean estimate as in
`kt-return-principal-angle-gram-proof` gives

```text
||R_n b_(i,n)||_2^2>=1-(q_(i,n)+eta_(i,n))^2.           (KDP2)
```

Let `Z_n` be the Gram matrix of the vectors `R_n b_(i,n)`.  Orthonormalizing
the input family by `G_n^(-1/2)` shows that the squared Hilbert--Schmidt norm
of `R_n` on their span is

```text
Tr(G_n^(-1)Z_n)
 >=Tr(Z_n)/lambda_max(G_n)
 >=[sum_i(1-(q_(i,n)+eta_(i,n))^2)]/lambda_max(G_n).    (KDP3)
```

For a unitary `W` and an orthogonal projection `P`, the two blocks

```text
(1-P)WP,             (1-P)W^*P
```

have identical singular values: their squared moduli on `PK` are
`1-C^*C` and `1-CC^*`, where `C=PWP`.  Consequently the total squared
Hilbert--Schmidt norm of the first block is the same as that of the second.
The first is exactly `L_n`, so `(KDP3)` proves `(KDL7)`.

For fixed `N`, `(KDL3)`, the word defects, and `(KDP1)` turn `(KDL7)` into
`(KDL8)`.  Since the same sequence satisfies this for every fixed `N`, it
must obey `L_n->infinity`.

Finally `(KPA7)--(KPA10)` identify `L_n` with the Gram-weighted covariance
leakage of any full edge word basis and give the stated upper bounds.
Divergence of `L_n` therefore forces `(KDL9)--(KDL10)`.
