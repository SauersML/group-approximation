---
rg: 2
id: formanek-procesi-diagonal-hnn-is-residually-finite
kind: claim
title: The diagonal free-support HNN is the residually finite Formanek-Procesi group
artifacts:
  - research/artifacts/signed-hecke-common-type-normalization-2026-08-20.md
distinct_from:
  finite-edge-hnn-closures-cannot-finish-the-nonce-atlas: that proves residual finiteness from finite edge groups; this edge group is a nonabelian finite-rank free group.
  symmetric-free-support-hnn-remains-hyperlinear: that has a path-RAAG height kernel after identifying two commuting factors; this is the asymmetric diagonal embedding and is identified with the Formanek-Procesi group.
---

For every finitely generated residually finite group `L`, put

```text
H(L)=<L times L,s | s(g,g)s^(-1)=(g,1), g in L>.         (FPH1)
```

The group `H(L)` embeds in `Aut(L * Z)`.  Since `L * Z` is finitely generated
and residually finite, its automorphism group is residually finite; hence so
is the finitely generated subgroup `H(L)`.

Taking `L=F_(D-1)`, reverse the stable letter in `(DHA2)`.  Its relation

```text
t(g,1)t^(-1)=(g,g)
```

becomes `(FPH1)`, so `E_delta isomorphic to H(F_(D-1))`.  Therefore the exact
diagonal phase-depth transport group is residually finite and hyperlinear.

The definition, semidirect-product description, and embedding
`H(L)<=Aut(L*Z)` are proved in Section 4.1 of V. Bardakov and R. Mikhailov,
*On certain questions of the free group automorphisms theory*,
arXiv:math/0701441.  The same section explicitly notes residual finiteness for
the poison group `H(F_2)`; the characteristic-quotient argument in the proof
route gives the stated finitely generated residually finite generality.
