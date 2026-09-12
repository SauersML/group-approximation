---
rg: 2
id: defect-saturation-via-hyperlinear-compiler
kind: route
title: Feed the Fournier--Facio compression defect to the general hyperlinear saturation compiler
target: defect-saturation-full-mf-radical
requires: [acylindrical-hyperlinear-saturation-compiler, fournier-facio-torsion-free-skeleton]
artifacts:
  - research/artifacts/hyperlinear-to-mf-saturation-compiler-2026-08-22.md
  - research/artifacts/router-detector-torsion-free-non-mf-2026-08-22.md
  - GroupApproximation/Sofic/NormalKazhdanHyperlinearKilled.lean
  - GroupApproximation/Sofic/TorsionFreeFullMFRadical.lean
---

## Why sufficient

The Fournier--Facio source is finitely presented, torsion-free,
acylindrically hyperbolic, and Kazhdan.  Its compression defect `D_0` contains
the surviving nonabelian simple subgroup and is therefore nontrivial.  The
kernel-checked declaration

```text
KazhdanCompressionCore.defectNormal_hyperlinear_killed
```

proves that `D_0` is op-to-HS killed in every operator-norm almost
representation.  Hence `(G_0,D_0)` meets the input interface of
`acylindrical-hyperlinear-saturation-compiler`.

One further Hull routing pass produces a protected, nontrivial, 2-generated,
finitely presented, torsion-free, acylindrically hyperbolic Kazhdan quotient
`Q` with `q(D_0)=Q`.  The general compiler gives
`normMFResidual Q = top`, and quotient heredity gives the same result for
every quotient of `Q`.

This is an alternative factorization of the existing explicit proof.  It
shows that the reusable theorem is the abstract hyperlinear-to-MF compiler;
the compression group is one certified input object.
