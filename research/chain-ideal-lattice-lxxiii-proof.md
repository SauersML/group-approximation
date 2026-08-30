---
rg: 2
id: chain-ideal-lattice-lxxiii-proof
kind: route
title: A finite family of ideals in a chain has a largest member
target: chain-ideal-lattice-solves-lxxiii
requires:
  - finite-square-zero-packet-covers-cutdown
---

Fix `a in A_+` and `epsilon>0`.  By the finite-packet theorem there are
square-zero elements `x_1,...,x_n` such that

```text
(a-epsilon)_+ in Ideal(x_1)+...+Ideal(x_n).
```

The finitely many ideals `Ideal(x_i)` are linearly ordered, so one of them,
say `Ideal(x_j)`, is the largest.  Their sum is therefore exactly
`Ideal(x_j)`.  Taking `x=x_j` gives both required conclusions.
