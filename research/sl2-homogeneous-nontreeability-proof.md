---
rg: 2
id: sl2-homogeneous-nontreeability-proof
kind: route
title: Compute the positive second L2-Betti number of the homogeneous orbit relation
target: sl2-homogeneous-action-is-not-treeable
requires: []
---

Write bars for passage to the finite central quotient.  The diagonal group

```text
bar A = PSL_2(Z[1/2])
```

is a lattice in

```text
G = PSL_2(R) x PSL_2(Q_2).                              (NTP1)
```

Both factors in `(NTP1)` have positive first L2-Betti number and zero
zeroth L2-Betti number.  The Kunneth formula therefore gives

```text
beta_2^(2)(G)
  = beta_1^(2)(PSL_2(R)) beta_1^(2)(PSL_2(Q_2)) > 0.    (NTP2)
```

L2-Betti-number proportionality for lattices now gives

```text
beta_2^(2)(bar A)
  = covol(bar A in G) beta_2^(2)(G) > 0.                (NTP3)
```

The finite central extension from `bar A` to `A` preserves positivity.

For completeness, the left `A`-action on `X=L/Lambda'` is essentially
free.  If a nonidentity `a in A` fixes `g Lambda'`, then
`g^(-1) a g in Lambda'`.  For fixed `a` and `lambda in Lambda'`, the solution
set of `g^(-1) a g=lambda` is empty or a coset of the proper centralizer of
`a`, hence Haar-null.  There are only countably many `lambda`.  A nontrivial
central torsion element gives no exception because the lattice is
torsion-free.  Thus every nonidentity element has a null fixed set.

Gaboriau's identification of group and orbit-relation L2-Betti numbers for
an essentially free p.m.p. action yields

```text
beta_2^(2)(R_A) = beta_2^(2)(A) > 0.                    (NTP4)
```

Finally a treeing is a one-dimensional contractible simplicial resolution
of the relation, so a treeable relation has
`beta_n^(2)=0` for every `n>=2`.  Equation `(NTP4)` rules out a treeing.

