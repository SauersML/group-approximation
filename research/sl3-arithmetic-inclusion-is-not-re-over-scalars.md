---
rg: 2
id: sl3-arithmetic-inclusion-is-not-re-over-scalars
kind: claim
title: The SL3 arithmetic inclusion is not relatively embeddable over scalars
distinct_from:
  sl3-arithmetic-inclusion-is-not-re-over-lattice: that uses the lattice factor as Gao's coefficient algebra; the established coefficient-elimination theorem makes this scalar version equivalent but exposes the pure hyperfinite-carrier microstate content.
---

OPEN.  For

```text
N=L(SL_3(Z)) subset M=L(SL_3(Z[1/2])),
```

there is no scalar-coefficient relative-embeddability model.  Equivalently,
there do not exist finite QWEP algebras `A_k`, hyperfinite subalgebras
`B_k subset A_k`, and a trace-preserving embedding

```text
pi : M -> prod_omega A_k
```

such that `pi(N) subset prod_omega B_k` and the resulting square is a
commuting square.  This is the coefficient-free form of the exact
arithmetic-double terminal.

