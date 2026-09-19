---
rg: 2
id: rectangular-wedderburn-block-isometry-gap
kind: claim
title: A rectangular regular-chart Fourier block has a dimension-free isometry defect
---

Let `G` be finite and let `sigma,tau` be irreducible representations with

```text
d_sigma < d_tau.
```

In the regular multiple `l2(G) tensor C^k`, let `p_sigma,p_tau` be the minimal
Wedderburn projections from `regular-chart-wedderburn-coefficient-compiler`.
For every operator

```text
X = p_sigma X p_tau : p_tau H_k -> p_sigma H_k,
```

one has the rank obstruction

```text
||p_tau-X*X||_(2,ambient)^2 >= (d_tau-d_sigma)/|G|.   (RWI1)
```

Equivalently, with the Hilbert--Schmidt norm normalized on the domain corner,

```text
||p_tau-X*X||_(2,p_tau)^2 >= 1-d_sigma/d_tau.         (RWI2)
```

No operator-norm bound on `X` is required.  Thus a single atlas relation which
forces one compiled Fourier block from a larger irreducible multiplicity
corner into a smaller one to become an approximate isometry gives a fixed
matrix-only contradiction, independent of external multiplicity.

For `A_8` there are unequal irreducible degrees (already the trivial
representation and any nontrivial irreducible suffice), so this supplies a
new finite search endpoint for the regular-atlas program.  It is strictly
less data than reconstructing a Leavitt family: only one rectangular block
and one Gram relation `X*X ~= 1` are needed.