---
rg: 2
id: finite-normal-generator-approximate-table-trivialization-proof
kind: route
title: Approximate inverses and conjugate-word telescoping trivialize the table
target: finite-normal-generator-approximate-table-trivialization
requires: []
---

Choose a symmetric generating set `S` consisting of conjugates of `g` and
`g^-1`, and let `L` be the diameter of `Cay(G,S)`.

First the multiplication defect gives approximate inverses.  Since `u(1)=1`,

```text
||u(h)u(h^-1)-1||_2 <= eps,
```

and left multiplication by `u(h)^*` yields

```text
||u(h^-1)-u(h)^*||_2 <= eps.                           (1)
```

Hence `||u(g^-1)-1||_2<=delta+eps`.  If
`c=h g^sigma h^-1`, `sigma in {+1,-1}`, apply the multiplication defect twice
and `(1)` once:

```text
||u(c)-u(h)u(g^sigma)u(h)^*||_2 <= 3 eps.
```

Therefore every `s in S` satisfies

```text
||u(s)-1||_2 <= delta+4 eps.                           (2)
```

Now fix `x in G` and write a shortest word

```text
x=s_1 ... s_l,       l<=L.
```

Induction using the multiplication defect at each prefix gives

```text
||u(x)-u(s_1)...u(s_l)||_2 <= (l-1) eps.              (3)
```

Unitary telescoping of the product together with `(2)` and `(3)` gives

```text
||u(x)-1||_2
 <= (l-1)eps + sum_j ||u(s_j)-1||_2
 <= l delta + (5l-1)eps
 <= L delta + 5L eps.
```

Taking the maximum over `x` proves `(NG-TABLE)`.  Every constant comes from the
fixed finite Cayley graph, so arbitrary matrix amplification does not change
the estimate.
