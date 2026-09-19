---
rg: 2
id: shared-s5-r4-r5-blindness-proof
kind: route
title: Put the disjoint arm in the common point stabilizer
target: shared-s5-gauge-is-invisible-to-all-r4-r5-cells
requires:
  - shared-s5-selector-face-has-multiplicity-rotation-gauge
---

Two disjoint transpositions cannot both contain the missing letter `i`.
Hence one of them, say `b`, lies in `H`.  Equation `(RGI1)` gives
`rho_1(b)=rho_0(b)`, while `U in rho_0(H)'` gives
`[U,rho_0(b)]=0`.  Therefore

```text
[rho_1(a),rho_0(b)]
 =[U rho_0(a)U^*,rho_0(b)]
 =U[rho_0(a),rho_0(b)]U^*=I.
```

The other three chart assignments are identical or obtained by swapping
the roles.  This proves `(RGI2)`.  The explicit `U` in the required gauge
claim changes `rho_0((i p))`, so it supplies the asserted zero-energy,
positive-mismatch countermodel.

For the approximate assertion, use

```text
||AB-BA||_2
 <=||AB-Phi(ab)||_2+||Phi(ba)-BA||_2
 <=2 epsilon
```

inside one chart.  The identity
`||[A,B]-I||_2=||AB-BA||_2` transfers this to commutator words.  Replacing
either occurrence of `B` by a unitary within `eta` changes the commutator by
at most `2eta`.  Since at most two common-face factors need replacement,
the bound is `2epsilon+4eta`, proving `(RGI4)`.
