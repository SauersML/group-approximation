---
rg: 2
id: finite-character-hnn-transport-proof
kind: route
title: Conjugate the character sum termwise and assemble its spectral pieces
target: finite-character-idempotents-have-exact-hnn-transport
requires:
  - piecewise-group-transport-gives-corner-unitaries
---

Britton's lemma embeds `Gamma` in `(FHI2)`.  Conjugating the first sum in
`(FHI1)` term by term gives

```text
t z_(H,chi)t^(-1)
 =dim(chi)/|H| sum_(h in H) chi(h^(-1))phi(h)
 =z_(L,psi),
```

because `phi` is bijective, preserves inverses, and `psi(phi(h))=chi(h)`.
This proves `(FHI3)` and also applies to one-dimensional character
idempotents.

In `(FHI4)`, all source pieces form an orthogonal partition of `q`, as do all
range pieces.  Equation `(FHI3)` is precisely `(PGT1)` for each matched pair,
so `piecewise-group-transport-gives-corner-unitaries` makes `(FHI5)` a corner
unitary.  Every source and range piece indexed by `s` lies below the same
separator atom `e_s`; hence `Ve_s=e_sV`, and `V` commutes with the separator
algebra.  It maps the sum of the positive source pieces to the sum of the
positive range pieces and likewise for the negative pieces, which is exactly
`(FHI6)`.
