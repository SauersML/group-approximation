---
rg: 2
id: hilbert-hotel-self-saturated-non-mf
kind: claim
title: A rank-20 Hilbert-hotel quotient is finitely presented, Kazhdan, and has full MF residual
distinct_from:
  defect-saturation-full-mf-radical: that construction uses the Fournier--Facio source and a Hull--Osin torsion-free small-cancellation routing quotient; this uses one binary-Leavitt Steinberg cover and one full-idempotent root defect, and is torsion-full.
  kazhdan-clifford-non-mf-construction: that construction uses a central involution and Clifford anticommutation; this uses no Clifford group or central sign, and its defect is a noncentral Steinberg root over a full idempotent.
artifacts:
  - research/artifacts/hilbert-hotel-st20-full-mf-radical-2026-08-21.md
  - research/artifacts/hilbert-hotel-character-rigidity-seam-audit-2026-08-21.md
  - GroupApproximation/Sofic/NormalKazhdanMFRadical.lean
  - GroupApproximation/Steinberg/BinaryLeavitt.lean
---

There is a nontrivial finitely presented property-`(T)` group `G` with

```text
Res_MF(G) = G.
```

Take `Delta=St_20(L_2(F_2))`.  The explicit
[[leavitt-whitehead-20x20-compression-cell]] supplies a lifted Whitehead word,
the block map `j:St_5(R)->Delta`, and the corner endomorphism `alpha`.  Quotient
`Delta` by finitely many relators forcing Whitehead conjugation to equal
`alpha` on a finite generating set, and by one relation identifying the
moved-centralizer defect with `x_13(q)`, where `q=s1*t1`.

All added relators hold under `Delta ->> E_20(R)`, where the defect is
`e_13(q)!=1`, so the quotient remains nontrivial.  By
[[full-leavitt-idempotent-defect-saturation]], the defect normally generates
`G`.  The rank-five domain and `G` are Kazhdan, so
[[normal-kazhdan-defect-non-mf]] applies with `K=G` and yields the displayed
full MF residual.  Every nontrivial quotient of `G` has the same property.

Krstic--McCool supplies finite presentability of the Steinberg source and
Ershov--Jaikin-Zapirain supplies property `(T)`; the exact binary-Leavitt
property-`(T)` instance is also proved in-repo.  This claim does not assert
torsion-freeness or non-hyperlinearity.
