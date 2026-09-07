---
rg: 2
id: non-hyperlinear-from-hs-relator-defect-gap
kind: route
title: A normalized-HS relator defect gap refutes every microstate sequence
target: non-hyperlinear-group
requires:
  - saturated-group-hs-relator-defect-gap
  - defect-saturation-full-mf-radical
artifacts:
  - research/artifacts/hs-defect-gap-and-padding-2026-09-07.md
---

## Why sufficient

The prerequisites supply the explicit two-generated finitely presented group
`Q=<S|R>` and the constant `eta>0` of `(HSG)`.

Suppose `Q` is hyperlinear.  Then `L(Q)` embeds in `R^omega`, so the
restriction of the trace to the canonical unitaries kills every nonidentity
element, and pulling the embedding back through matrix microstates gives
unitary tuples `U^((n)) in U(d_n)^S` with

```text
d_2(U^((n))) -> 0,
||U_s^((n)) - I||_2 -> sqrt 2   for each s.
```

The generators of `Q` are nontrivial because `Q` is infinite and torsion-free,
so `D_2(U^((n))) -> sqrt 2`, and `D_2(U^((n))) >= 1` for large `n`.  Then
`(HSG)` gives `d_2(U^((n))) >= eta` for those `n`, against
`d_2(U^((n))) -> 0`.

So `Q` is not hyperlinear, and it is explicit.
