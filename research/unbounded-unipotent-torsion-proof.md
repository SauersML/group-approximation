---
rg: 2
id: unbounded-unipotent-torsion-proof
kind: route
title: Reduce the arithmetic generators modulo every odd integer and use the regular action
target: full-iwahori-relations-do-not-bound-unipotent-torsion
requires:
  - bs14-unitary-representations-are-periodic-cycle-packets
---

Because `2` is invertible modulo odd `n`, entrywise reduction defines the
finite image `Q_n` in `(UIT1)` and sends every defining arithmetic matrix,
including the denominator diagonal, to an invertible projective matrix.
Therefore every word relation in the exact Iwahori presentation survives
reduction.

For

```text
u_n=[[1,1],[0,1]] mod n,
```

one has

```text
u_n^k=[[1,k],[0,1]] mod n.                              (UTP1)
```

Its projective class is the identity only if `k=0 mod n`: a scalar matrix
with diagonal entries one has scalar one, and then its upper-right entry
must vanish. Hence `u_n` has order exactly `n` in `Q_n`.

The left regular representation of a finite group is faithful, so the
corresponding unitary has the same order. Taking odd `n` arbitrarily large
proves the order and level assertions. If one finite spectral set contained
all root spectra, its elements would have bounded orders, contradiction.
If one nonzero polynomial annihilated every root unitary, it would vanish on
all `n`-th roots occurring in the regular action of `<u_n>` for unbounded
odd `n`, an infinite subset of the circle, and hence would be the zero
polynomial. This proves every assertion of the claim.
