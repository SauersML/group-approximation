---
rg: 2
id: projective-gauge-charge-no-go-proof
kind: route
title: Fourier-grade projective observables and polarize charged intertwiners
target: projective-gauge-charge-forces-morita-or-corner
requires:
  - projective-atlas-cannot-orient-transverse-branch-phase
  - two-chart-square-lift-recreates-schur-m2
---

# Fourier-grade projective observables and polarize charged intertwiners

Apply the circle Fourier projector

```text
F_k(W)=integral lambda^(-k) F(lambda W) dlambda.
```

Representative independence makes `F=F_0`, proving gauge neutrality. Extra
nonzero charge must therefore enter through lift data. For a full unitary
intertwiner, compressing by its source and target projections gives `(GCF4)`
and hence matrix units. Trace cyclicity gives equal source and range traces;
failure of full Morita equivalence is possible only when the range is a
proper subprojection of a larger target. The two-chart computation supplies
the concrete Schur specialization.
