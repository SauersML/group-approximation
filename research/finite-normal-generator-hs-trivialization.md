---
rg: 2
id: finite-normal-generator-hs-trivialization
kind: claim
title: A finite normal generator controls all noninvariant representation mass
distinct_from:
  finite-normal-generator-approximate-table-trivialization: that starts with an approximate multiplication table and proves every table entry is close to one; this starts with an exact representation and bounds the dimension of its nontrivial invariant complement.
---

Let `G` be finite and let `g in G` normally generate `G`.  There is an integer
`L=L(G,g)<infinity` such that every finite-dimensional exact unitary
representation

```text
pi:G->U(d)
```

with invariant-vector projection `Q_pi` satisfies

```text
tr_d(1-Q_pi)<=L^2 ||pi(g)-1||_2^2.                    (FNG-HS)
```

The constant depends only on the fixed finite pair `(G,g)`, not on `d` or on
any external multiplicity.  Consequently `pi_n(g)->1` forces the normalized
dimension of every nontrivial representation sector to tend to zero.