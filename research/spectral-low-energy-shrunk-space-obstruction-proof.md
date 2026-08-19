---
rg: 2
id: spectral-low-energy-shrunk-space-obstruction-proof
kind: route
title: Spectral truncation puts every low-energy unitary near the shrunk matrix space
target: spectral-low-energy-shrunk-space-obstruction
requires:
  - shrunk-matrix-space-unitary-distance
---

Let `Pi_a` be the spectral projection of `L` onto eigenvalues in `[0,a]`, so
`K_a=range(Pi_a)`.  Decompose

```text
U = U_low + U_high,
U_low=Pi_a U.
```

On the orthogonal complement of `K_a`, the quadratic form of `L` is at least
`a` times squared normalized Hilbert--Schmidt norm.  Therefore

```text
E(U)=<U,LU> >= a ||U_high||_2^2.                     (1)
```

Since `U_low in K_a`,

```text
dist_2(U,K_a)^2 <= ||U-U_low||_2^2
                 = ||U_high||_2^2
                 <= E(U)/a.                          (2)
```

If `(SLS1)` holds, `shrunk-matrix-space-unitary-distance` gives the opposite
bound

```text
dist_2(U,K_a)^2 >= gamma.                            (3)
```

Combining `(2)` and `(3)` proves `E(U)>=a gamma`, which is `(SLS2)`.