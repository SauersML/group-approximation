---
rg: 2
id: common-higher-rank-syndrome-cylinder-proof
kind: route
title: Intersect group-basis supports and Fourier-restrict from the shared subgroup
target: common-higher-rank-context-projections-are-syndrome-cylinders
requires: []
---

The group elements of `Gamma` are a linear basis of `C[Gamma]`.  An element
lying in both `C[H_1]` and `C[H_2]` has group-basis support contained in both
subgroups, hence in `L`; the reverse inclusion is immediate.  This proves
`(SHC1)`.

Because `L` is finite abelian, a projection in `C[L]` is the sum of the
minimal Fourier idempotents indexed by some `S subseteq dual(L)`.  For
`psi in dual(L)`, its idempotent decomposes in `C[H_i]` as

```text
e_psi^L=sum_(chi in dual(H_i), chi|_L=psi) e_chi^(H_i).  (SHC3)
```

Summing `(SHC3)` over `psi in S` proves `(SHC2)`.  Every restriction fiber
has size `|H_i|/|L|`.  Hence a common projection can select a singleton
character of `H_i` only if `|H_i|=|L|`, i.e. `H_i=L`.  Applying this to both
contexts gives the final rank-one statement.

