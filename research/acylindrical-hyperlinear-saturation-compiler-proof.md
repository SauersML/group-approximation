---
rg: 2
id: acylindrical-hyperlinear-saturation-compiler-proof
kind: route
title: Choose Hull's suitable two-generator reservoir inside the killed normal subgroup
target: acylindrical-hyperlinear-saturation-compiler
requires: [hyperlinear-to-mf-saturation-compiler, common-quotient-onto-normal-subgroup]
artifacts:
  - research/artifacts/hyperlinear-to-mf-saturation-compiler-2026-08-22.md
  - notes/TORSION_FREE_NORMAL_GENERATION_HULL_QUOTIENT.md
---

## Why sufficient

Since `E` is torsion-free and `D != 1`, `D` is infinite.  Normality makes it
`s`-normal; Osin's theorem makes its acylindrical action non-elementary, and
torsion-freeness removes Hull's finite-radical obstruction.  Thus `D` is
suitable.  Choose noncommensurable loxodromics `h_1,h_2 in D` whose generated
subgroup `S_0` is suitable.

Apply Hull's Theorem 7.1 to a finite generating list `t_1,...,t_m` of `E`,
with the injectivity ball enlarged to contain the protected set.  Every
`q(t_i)` lies in `q(S_0)`, hence

```text
Q = q(S_0) = q(D).
```

The images of `h_1,h_2` generate `Q`.  Hull preserves acylindrical
hyperbolicity and torsion-freeness; only finitely many relators are added, so
finite presentation survives.  The protected nonidentity element makes `Q`
nontrivial, and property `(T)` passes through `E->>Q`.

Now apply `hyperlinear-to-mf-saturation-compiler`: `q(D)=Q` makes all of `Q`
op-to-HS killed, and `Q` is Kazhdan, so its MF residual is all of `Q`.
Quotient heredity supplies the final clause.

The source verification of every Hull--Osin clause is the established route
`common-quotient-onto-normal-subgroup-proof`; no small-cancellation theorem is
postulated in Lean.
