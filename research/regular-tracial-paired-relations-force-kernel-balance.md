---
rg: 2
id: regular-tracial-paired-relations-force-kernel-balance
kind: claim
title: Exact paired relations between regular-trace finite-group charts force equal projection kernels
---

Let `G` be finite, `K<=G x G`, and let `p_1,p_2` be the coordinate
projections.  Suppose `(M,tau)` is a finite tracial von Neumann algebra,
`pi_1,pi_2:G->U(M)` are representations with regular normalized character

```text
tau(pi_i(g)) = 1  if g=1,
               0  if g!=1,                              (RTK1)
```

and there is a unitary `U in M` satisfying

```text
pi_1(p_1(k)) U = U pi_2(p_2(k))                        (RTK2)
```

for a generating set of `K` (hence for all `k in K`).  Then

```text
ker p_1 = ker p_2.                                      (RTK3)
```

Consequently the corresponding paired relation system between finite regular
`G` charts has an exact unitary solution at every common external multiplicity.
Its zero-energy intertwiner space, and therefore every spectral low-energy
superspace, has zero shrunk-subspace deficiency.

This is a representation-theoretic no-go for operator-scaling certificates
built only from two-term paired equations which already hold in a regular-trace
exact model.  Such equations can constrain the relative unitary but cannot by
themselves create noncommutative-rank shrinkage in finite regular charts.
