---
rg: 2
id: multiplicity-pi-turing-tape-proof
kind: route
title: Apply Schur's lemma on the isotypic block and run the degree-2k identity
target: multiplicity-pi-turing-tape
requires:
  - two-generator-amitsur-levitzki-dimension-oracle
---

The isotypic decomposition for the finite group `H` identifies the
`pi`-isotypic block with `pi tensor C^k`.  Schur's lemma gives the commutant
identity `(MPT1)`.  Any operator commuting with `rho(H)` preserves the
isotypic block and restricts to `I_r` tensored with a unique element of
`M_k(C)`; apply this to `x` and `y`.

Polynomial evaluation respects tensoring by the identity, so

```text
p_k(I_r tensor X,I_r tensor Y) = I_r tensor p_k(X,Y).
```

The size-`k` instance `(ALO2)` of
`two-generator-amitsur-levitzki-dimension-oracle` makes the second tensor
factor zero, proving `(MPT2)`.

