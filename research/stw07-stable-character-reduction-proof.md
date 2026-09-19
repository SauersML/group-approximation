---
rg: 2
id: stw07-stable-character-reduction-proof
kind: route
title: Stabilize and unitize while proving finiteness through the split K_0 sequence
target: stw07-bk-reduces-to-stable-character-kernels
requires: []
artifacts:
  - research/artifacts/stw07-status-and-stable-character-reduction-2026-08-30.md
---

Assertion 1 trivially implies assertion 2.  Conversely, let `A` be nonzero,
separable, nuclear, and stably finite.  Put `I=A tensor K` and `E=I~`.
Separability and nuclearity pass to `I` and `E`.  The scalar quotient is a
character `chi:E -> C`; its kernel `I` is stable and essential in its
unitization.

We verify stable finiteness of `E`.  Suppose at some matrix level that
`v in M_n(E)` is an isometry, and put

```text
p=1-vv*.
```

The scalar image of `v` is an isometry in `M_n(C)`, hence a unitary, so
`p in M_n(I)`.  Murray--von Neumann equivalence of `v*v=1` and `vv*=1-p`
gives

```text
[p]=[1]-[1-p]=0 in K_0(E).                              (SC2)
```

The unitization extension is split, so `K_0(I) -> K_0(E)` is injective.
Thus `[p]=0` in `K_0(I)`.  By the definition of the Grothendieck group there
is a projection class `r in V(I)` such that

```text
[p]+r=r in V(I).                                        (SC3)
```

If `p` were nonzero, `(SC3)` would make a matrix projection over `I`
infinite, contradicting stable finiteness of `I`, equivalently of `A`.
Therefore `p=0`; every matrix isometry in `E` is unitary and `E` is stably
finite.

Finally, quasidiagonality is invariant under stabilization and unitization:

```text
A is QD  iff  A tensor K is QD  iff  (A tensor K)~ is QD. (SC4)
```

For the first equivalence use matrix amplification and the injective limit
`A tensor K=closure(union_n A tensor M_n)` in one direction, and the corner
`A tensor e_11` in the other.  The second is the standard unitization
permanence of quasidiagonality.  Hence a nonquasidiagonal `A` gives a
nonquasidiagonal `E`, completing the reduction.
