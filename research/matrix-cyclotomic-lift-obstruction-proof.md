---
rg: 2
id: matrix-cyclotomic-lift-obstruction-proof
kind: route
title: Apply direct finiteness in the matrix group factor and reduce the reverse identity
target: matrix-cyclotomic-lift-obstruction
requires: []
artifacts:
  - research/artifacts/matrix-cyclotomic-lift-and-rank-decoder-audit-2026-08-21.md
---

## Direct proof

The left regular representation embeds `M_k(C[G])` faithfully into the finite
von Neumann algebra `M_k(L(G))`.  Hence `AB=I_k` implies `BA=I_k`.

All entries of `A,B` lie in `O[G]`, so reduce the reverse equality
coefficientwise modulo `p`.  The coefficient-faithfulness hypotheses give

```text
A mod p = a I_k,         B mod p = b I_k.
```

Consequently `BA=I_k` reduces to `(ba)I_k=I_k` in `M_k(F_2[G])`.  Comparing
one diagonal entry yields `ba=1`, a contradiction.  The proof has no bound on
`k`; exact finite matrix amplification never escapes it.
