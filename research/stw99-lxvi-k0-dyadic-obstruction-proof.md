---
rg: 2
id: stw99-lxvi-k0-dyadic-obstruction-proof
kind: route
title: Send the coherent projection-monoid halves to K0
target: stw99-lxvi-k0-dyadic-divisibility-obstruction
requires:
  - stw99-lxvi-car-corner-iff-coherent-dyadic-v-chain
---

The CAR-corner criterion gives classes `x_n in V(B)` with

```text
x_0=[p],                x_n=2x_(n+1).
```

Let `g_n` be the image of `x_n` under the canonical monoid map
`V(B)->K_0(B)`.  Iterating the displayed equality gives

```text
[p]_0=g_0=2^n g_n
```

for every `n`, and each `g_n` is represented by a projection.  This proves
the asserted positive coherent divisibility and the obstruction.

If a homomorphism from `K_0(B)` to a finitely generated free abelian group
sends `[p]_0` to a nonzero element, that image cannot be divisible by every
power of two: the intersection of the subgroups `2^n Z^d` is zero.  Hence
`[p]_0` cannot lie in the displayed intersection.
