---
rg: 2
id: boolean-towers-of-simple-mf-black-holes
kind: claim
title: Simple Hilbert-hotel factors build Boolean towers of total MF invisibility
artifacts:
  - research/boolean-towers-of-simple-mf-black-holes-proof.md
---

Let

```text
H=EL_16(L_(F_2)(1,2)).
```

For every nonempty countable index set `I`, put

```text
K_I=directSum_(i in I) H.
```

Then:

1. `Rad_MF(K_I)=K_I`; every homomorphism from `K_I` to an MF group is
   trivial;
2. every normal subgroup of `K_I` is uniquely
   `K_S=directSum_(i in S)H` for a subset `S<=I`;
3. every normal subgroup and every nontrivial quotient of `K_I` again has
   full MF radical;
4. the normal-subgroup lattice of `K_I` is canonically the complete Boolean
   algebra `P(I)`.

For finite `I={1,...,n}`, the groups `H^n` are pairwise nonisomorphic,
finitely generated, Kazhdan, ICC, perfect full-radical groups with exactly
`n` minimal nontrivial normal subgroups.

Consequently, for every countable MF group `Q`,

```text
E_(n,Q)=H^n x Q
```

has

```text
Rad_MF(E_(n,Q))=H^n x {1},
R_MF(E_(n,Q))=Q,
Hom(E_(n,Q),M) ~= Hom(Q,M)                            (BT1)
```

naturally for every MF target `M`.  The groups `E_(n,Q)` are pairwise
nonisomorphic because their characteristic MF radicals have respectively
`n` minimal normal subgroups.  Thus every prescribed countable MF reflection
has an infinite hierarchy of nonisomorphic split thickenings whose invisible
kernels have explicitly different finite Boolean normal lattices.

For `I=N`, the countable group `K_N x Q` has the same prescribed reflection
`Q` and a radical containing continuum many normal subgroups, all themselves
MF-invisible.
