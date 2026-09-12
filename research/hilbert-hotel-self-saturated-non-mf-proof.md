---
rg: 2
id: hilbert-hotel-self-saturated-non-mf-proof
kind: route
title: Quotient St20 by finite transport and one defect-identification relation
target: hilbert-hotel-self-saturated-non-mf
requires:
  - leavitt-whitehead-20x20-compression-cell
  - full-leavitt-idempotent-defect-saturation
  - normal-kazhdan-defect-non-mf
  - elementary-group-property-t-over-free-algebras
  - atlas-steinberg-context-absorption
artifacts:
  - research/artifacts/hilbert-hotel-st20-full-mf-radical-2026-08-21.md
---

Let `S` be a finite generating set of `St_5(R)`.  In `Delta=St_20(R)`, impose
the transport relators for `s in S` and the single relation

```text
[Ttilde*c*Ttilde^-1,j(lambda0)] = x_13(q).
```

The block calculation makes every relator vanish under
`Delta ->> E_20(R)`, so that map factors through a surjection from the
quotient `G`, and the defect maps to `e_13(q)!=1`.  Krstic--McCool gives
finite presentability; EJZ property `(T)` descends to `G`.

Transport on `S` extends to the whole rank-five domain because both sides are
homomorphisms.  The block-disjoint mark centralizes the domain.  The
defect-identification relation and the full-idempotent theorem give
`defectNormal=G`.  Applying the machine-checked normal-Kazhdan theorem with
the nontrivial normal Kazhdan subgroup `K=G` gives `Res_MF(G)=G`; heredity to
quotients follows by composition.
