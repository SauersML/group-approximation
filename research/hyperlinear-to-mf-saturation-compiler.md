---
rg: 2
id: hyperlinear-to-mf-saturation-compiler
kind: claim
title: Routing an op-to-HS killed defect over a Kazhdan subsystem compiles it into the MF residual
root: true
distinct_from:
  hyperlinear-killed-normal-kazhdan-mf-transfer: that theorem detects a normal Kazhdan subgroup already inside a killed defect of one ambient group; this compiler first pushes the defect through an arbitrary quotient and includes the full-saturation and quotient-heredity conclusions.
  defect-saturation-full-mf-radical: that claim constructs one explicit torsion-free full-radical group from the Fournier--Facio data; this theorem is source-independent and accepts any op-to-HS killed subgroup.
  common-quotient-onto-normal-subgroup: that claim is only the group-theoretic routing tool and assumes no tracial kill or property (T); this theorem is the analytic semantic consequence of any routing map.
artifacts:
  - research/artifacts/hyperlinear-to-mf-saturation-compiler-2026-08-22.md
  - research/artifacts/shadow-kleene-saturation-compiler-2026-08-22.md
  - GroupApproximation/Sofic/NormalKazhdanHyperlinearKilled.lean
  - GroupApproximation/Sofic/OpToHSShadowResidual.lean
  - GroupApproximation/Sofic/TorsionFreeFullMFRadical.lean
---

Let `E` and `Q` be countable, let `D <= E` be op-to-HS killed, and let
`q : E -> Q` be a homomorphism.
Then the image `q(D)` is op-to-HS killed in `Q`: precompose any almost
representation of `Q` with `q` and lift each element of `q(D)` to `D`.

Consequently, every normal Kazhdan subgroup

```text
K triangleleft Q,
K <= q(D)
```

lies in `normMFResidual Q`.  Equivalently,

```text
normalKazhdanPart (q(D)) <= normMFResidual Q.
```

In the full-saturation case

```text
q(D) = Q,
Q has property (T),
```

one may take `K=Q` and obtain

```text
normMFResidual Q = top.
```

This conclusion passes through every surjection `Q ->> L`.  Thus every
nontrivial quotient of `Q` is non-MF, and every homomorphism from `Q` to an
operator-MF group is trivial.

The one-word frontend is `single-shadow-word-saturation-compiler`: it takes
one nontrivial element of the shadow residual, forms its normal closure, and
constructs the routing map required here.
