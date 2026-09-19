---
rg: 2
id: dephasing-destroys-multiplicativity
kind: claim
title: Entrywise modulus squaring is doubly stochastic but forgets composition
invalidates: [sofic-model-via-unistochastic-dephasing]
artifacts:
  - research/artifacts/hyperlinear-divergent-strategies-2026-08-18.md
---

For `U ∈ U(d)` let `P_U(i,j) = |u_{ij}|^2`.  Then `P_U` is doubly stochastic,
hence by Birkhoff a convex combination of permutation matrices — the single
most tempting classicalization of a unitary.  But the assignment is not
multiplicative:

```text
P_{UV} ≠ P_U P_V   in general,
```

because `|(UV)_{ik}|^2 = |sum_j u_{ij} v_{jk}|^2` contains the interference
cross terms `2 Re( u_{ij} v_{jk} conj(u_{ij'} v_{j'k}) )`, `j ≠ j'`, which
`(P_U P_V)_{ik} = sum_j |u_{ij}|^2 |v_{jk}|^2` discards.  A two-dimensional
Hadamard example already separates them: for
`U = V = (1/√2)·[[1,1],[1,-1]]`, `UV = I`, so `P_{UV} = I`, while
`P_U P_V = [[1/2,1/2],[1/2,1/2]]`.

**Consequence.**  Dephasing loses exactly the information a sofic model needs
— the multiplication table — and it loses it *before* any rounding step, so no
amount of downstream combinatorics can recover it.  The route that squares the
entries, Birkhoff-decomposes, and reads off permutations is recorded dead
(`sofic-model-via-unistochastic-dephasing`).

**The design constraint it imposes.**  Any classicalization for Q3.4 must
retain path coherence long enough for the multiplication constraints to be
imposed, and may discard phase only afterwards.  This is why the encodings
proposed in `definetti-group-table-rounding` are built from *path-amplitude*
data (products `(U_g)_{lj}(U_h)_{ji} conj((U_k)_{li})` with the middle index
live) rather than from dephased transition matrices, and it is the reason the
hard step there is product-state integrality rather than the de Finetti
collapse itself.
