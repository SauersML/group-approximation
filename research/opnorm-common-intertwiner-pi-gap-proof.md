---
rg: 2
id: opnorm-common-intertwiner-pi-gap-proof
kind: route
title: Telescope every standard-polynomial monomial through the common intertwiner
target: opnorm-common-intertwiner-pi-gap-is-sparse-terminal
requires: []
---

Write `A=s_m(D_1,...,D_m)`.  For one permutation `sigma`, telescope

```text
D_(sigma(1))...D_(sigma(m)) T
  -T C_(sigma(1))...C_(sigma(m))                       (1)
```

by replacing the factors from right to left.  Since all `C_j,D_j,T` are
contractions, the norm of `(1)` is at most

```text
sum_(l=1)^m ||D_(sigma(l))T-TC_(sigma(l))||_op.         (2)
```

Sum `(2)` over the `m!` signed monomials and discard the signs by the
triangle inequality.  Each permutation contains each index exactly once,
so the deliberately coarse uniform bound is

```text
||A T-T s_m(C)||_op <= m! delta.                        (3)
```

The source identity in `(SPI3)` reduces `(3)` to

```text
||A T||_op <= m! delta.                                 (4)
```

On the other hand `A=AP`, and therefore

```text
||A-A T T^*||_op <= ||A||_op eta.                       (5)
```

Since `T` is a contraction,

```text
||A T T^*||_op <= ||A T||_op.                          (6)
```

Equations `(5)--(6)` give

```text
(1-eta)||A||_op <= ||AT||_op.                           (7)
```

Combine `(4)`, `(7)`, and `||A||_op>=kappa` to obtain `(SPI4)`.

No trace or rank estimate occurred.  In particular the proof is unchanged
when `P` has rank one, and common amplification tensors every term with an
identity without changing any operator norm.
