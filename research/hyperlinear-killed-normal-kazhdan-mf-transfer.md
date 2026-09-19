---
rg: 2
id: hyperlinear-killed-normal-kazhdan-mf-transfer
kind: claim
title: Every normal Kazhdan part of an op-to-HS killed defect lies in the MF residual
distinct_from:
  normal-kazhdan-defect-non-mf: that claim assumes the killed subgroup is the defect of a Kazhdan compression core; this theorem accepts an arbitrary subgroup together with any tracial kill proof and has no compression data in its hypotheses.
  finite-normal-compression-obstruction: that claim obtains a corner by averaging a finite normal subgroup; this theorem permits infinite torsion-free Kazhdan subgroups and obtains the corner from their fixed-space projection.
  hs-invisibility-inflation-no-go: that claim shows tracial invisibility alone cannot control operator norm; this theorem adds the exact normal-Kazhdan hypothesis that detects and renormalizes the diluted moving corner.
artifacts:
  - research/artifacts/hyperlinear-to-mf-saturation-compiler-2026-08-22.md
  - GroupApproximation/Sofic/NormalKazhdanHyperlinearKilled.lean
  - GroupApproximation/Sofic/InternalRadicalGap.lean
---

Let `E` be countable and let `D <= E` be killed in the normalized-HS
ultraproduct shadow of every operator-norm almost representation of `E`.
If

```text
K triangleleft E,
K has property (T),
K <= D,
```

then

```text
K <= normMFResidual E.
```

Equivalently, the join of all normal Kazhdan subgroups contained in `D`
satisfies

```text
normalKazhdanPart D <= normMFResidual E.
```

If one such `K` is nontrivial, `E` is not MF.  No compression core,
centrality, torsion, finite order, or designated mark occurs in the
hypotheses.  The source of the tracial kill may be any hyperlinear theorem.

The detector is the moving-space projection of `K`.  Normality makes it
ambient-invariant; property `(T)` gives a fixed lower bound after the trace is
renormalized by the moving rank.  The assumed tracial kill then contradicts
that lower bound.
