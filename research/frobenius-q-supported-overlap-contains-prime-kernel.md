---
rg: 2
id: frobenius-q-supported-overlap-contains-prime-kernel
kind: claim
title: A nonzero faithful-block coefficient in a Frobenius overlap contains the prime kernel
distinct_from:
  common-carrier-lives-in-packet-intersection: that identifies the literal subgroup intersection supporting a common coefficient; this exploits annihilation by the Frobenius trivial-block average to force the whole prime kernel into that intersection.
  fourier-frobenius-common-carriers-classicalize-bcs: that assumes diagonal Fourier context PVMs and derives a classical assignment; this applies to arbitrary coefficients in the full faithful Frobenius block.
---

**ESTABLISHED.**  Let `Gamma` contain a Frobenius packet

```text
H=N rtimes T,
N=C_p,
e_N=(1/p)sum_(n in N)n,
q=1-e_N.
```

For every subgroup `K<=Gamma` and every nonzero coefficient

```text
0!=a in C[K]
```

satisfying `aq=a`, one has

```text
N<=K.                                                   (QPK1)
```

Consequently, in `affine-frobenius-common-negative-carrier`, if an incidence
carrier `p_x` is nonzero, then the literal packet intersection supporting
`p_x` contains the prime normal subgroup of every incident Frobenius packet.
All such prime kernels are therefore the same subgroup of the ambient group.

After orienting each nonconstant source variable so that its negative
marginal is nonzero, every connected component of the context-incidence
graph must use one common `C_p`.  Thus the surviving common-carrier
construction is not an arbitrary cycle of small packet overlaps: it is a
common-prime-kernel extension, and all contextuality must be carried by the
different complements or their centralizer twists.
