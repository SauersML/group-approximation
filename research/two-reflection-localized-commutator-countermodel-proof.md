---
rg: 2
id: two-reflection-localized-commutator-countermodel-proof
kind: route
title: Amplify two anticommuting Pauli reflections and classify their reducing projections
target: two-reflection-pressure-does-not-force-localized-commutation
requires: []
---

The matrices in `(TRP1)` satisfy

```text
C^2=B^2=I,                   CB=-BC.                    (TRP3)
```

They generate `M_2 tensor I_m`.  Hence their common commutant is
`I_2 tensor M_m`, so every common reducing projection has the form

```text
Q=I_2 tensor q                                                (TRP4)
```

for a projection `q in M_m`.  In fact only commutation with `C,B` is needed
for the norm calculation below.

Using `(TRP3)` and `[Q,C]=[Q,B]=0`,

```text
(C-B)^*(C-B)=2I-CB-BC=2I,
(CB-BC)^*(CB-BC)=(2CB)^*(2CB)=4I.                      (TRP5)
```

Multiply by `Q` and take normalized traces.  This gives exactly `(TRP2)`.
Taking tensor products with arbitrary auxiliary matrix representations
preserves `(TRP3)--(TRP5)`, and setting a separate central involution to
`-I` preserves all relations and norms.  Therefore neither finite dimension,
amplification, a central marked sign, nor an independent exact finite packet
turns positive two-letter disagreement into localized cross-commutation.

