# Passive Reynolds column over `PSL_2(Z/25Z)`

This is the depth-two continuation of
`passive-reynolds-diagonal-prime-sweep-2026-08-23.md`.  It was run on one
MSI CPU with one BLAS thread.  The matrices are integer signed-incidence
matrices built directly from `(DSS3)`.

```text
level  |Q|   |<h(2)>|  domain  rank  s_min      s_max      ||C^dagger||_inf
5       60       2        15     10   6.000000   6.000000   0.6666666667
25    7500      10       375    346  10.954451  13.416408   1.2640000000
```

The rank comparison has exact certificates rather than depending on the
floating-point singular values:

```text
level 5:   G=C^T C,  G^2=36G,  Tr(G)=360;
level 25:  rank_(F_1000003)(C^T C)=346.
```

The first line proves `rank(C_5)=10`.  The second exhibits a nonzero
`346`-minor over the integers and therefore proves `rank(C_25)>=346` over
the reals.  Since the reduction fibers have input dimension `25`, a tensor
lift of the level-five column would have rank at most `10*25=250`.

The infinity norms were obtained from

```text
(C^T C)^dagger C^T
```

and are not used as exact certificates.  In particular, the level-25
increase is evidence to guide the deeper audit, not a proof of divergence.

