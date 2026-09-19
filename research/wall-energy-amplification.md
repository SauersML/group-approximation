---
rg: 2
id: wall-energy-amplification
kind: claim
title: Wall energy is free — any wall amplifies to the maximal-energy wall
distinct_from:
  relative-wall-commutant-growth: That claim is the equivalence between existence of a wall and properness of a relative-commutant inclusion; this one is about the numerical energy of a given wall and shows the maximal-energy hypotheses used on the FALSE side cost nothing.
  additive-index-instability: That claim says an additive finite-phase index is destroyed by block amplification; this one says diagonal tensor amplification preserves a wall and drives its trace energy up to the maximum.
artifacts:
  - notes/TRUE_WALL_ENERGY_AND_COMMUTANT_DENSITY.md
---

Let `pi:G->U(M)` with `M` Connes-embeddable finite tracial, and let
`v in M intersect pi(Gamma)'` be a unitary with `[v,pi(h)]!=1`.  Then the
diagonal tensor powers `(M^(tensor k),pi^(tensor k),v^(tensor k))` are again
walls in Connes-embeddable algebras, self-adjoint if `v` is, and

```text
sup_k ||v^(tensor k)-pi_k(h)v^(tensor k)pi_k(h)^*||_2^2 >= 2.
```

Hence the maximal-energy hypotheses `(CHI8)` and `(WFI4)` follow from the
existence of any wall, and the flexible-Hilbert--Schmidt-instability
conclusions drawn from them hold as soon as a wall exists at all.

Scope: amplification does **not** produce the Clifford (anticommuting) wall
of the Clifford normal form, since `v_k w_k=(vw)^(tensor k)`.  Anticommutation
is a genuinely stronger demand; energy is not.
