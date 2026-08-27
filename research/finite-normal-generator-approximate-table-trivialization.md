---
rg: 2
id: finite-normal-generator-approximate-table-trivialization
kind: claim
title: A finite normal generator trivializes approximate unitary multiplication tables without representation rounding
---

Let `G` be a finite group, let `g in G` normally generate `G`, and let

```text
u : G -> U(d),       u(1)=1.
```

Set

```text
eps = max_(x,y in G) ||u(xy)-u(x)u(y)||_2,
delta = ||u(g)-1||_2.
```

There is an integer `L=L(G,g)<infinity`, depending only on the fixed finite
pair, such that

```text
max_(x in G) ||u(x)-1||_2
 <= L delta + 5 L eps.                                (NG-TABLE)
```

Thus an approximate multiplication table on a fixed finite group needs no
separate stability or integer-multiplicity theorem at this endpoint: once one
normal generator is close to identity and the multiplication defect is small,
the whole table is uniformly close to the trivial table, with constants
independent of matrix dimension.

## Attempts

- First recover approximate inverses from the multiplication table.  Then bound
  every conjugate of `g` or `g^-1`, write each group element as a bounded word
  in those conjugates, and telescope both the word and multiplication errors.
