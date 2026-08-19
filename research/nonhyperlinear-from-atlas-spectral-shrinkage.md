---
rg: 2
id: nonhyperlinear-from-atlas-spectral-shrinkage
kind: route
title: A linearly shrunk low-energy atlas matrix space forbids hyperlinear microstates
target: non-hyperlinear-group
requires:
  - atlas-steinberg-rank-five-translation
  - spectral-low-energy-shrunk-space-obstruction
  - atlas-spectral-shrunk-intertwiner-certificate
---

`atlas-steinberg-rank-five-translation` fixes the explicit finite atlas group
and its canonical trace target.  Suppose that group were hyperlinear.  Then
there would be trace-preserving finite-dimensional atlas microstates with
packet defect `delta_n->0`.

Apply `atlas-spectral-shrunk-intertwiner-certificate`.  For the relative chart
unitary `U_n` it supplies a positive quadratic form `E_n`, a cutoff `a_n`, and
a `gamma d_n`-shrunk spectral low-energy space with

```text
E_n(U_n) <= C delta_n^p,
C delta_n^p / a_n -> 0.                                (1)
```

The established theorem `spectral-low-energy-shrunk-space-obstruction` gives
for the same unitary

```text
E_n(U_n) >= gamma a_n.                                 (2)
```

Divide `(1)--(2)` by `a_n`:

```text
gamma <= C delta_n^p/a_n -> 0,
```

a contradiction.  Hence the canonical atlas trace has no hyperlinear
microstate sequence, and the explicit atlas group is nonhyperlinear.

This makes `atlas-spectral-shrunk-intertwiner-certificate` a single open atlas
leaf on a direct route to the primary goal.  Its operator-scaling formulation
is therefore not merely exploratory: one certified linear shrunk subspace per
sufficiently accurate microstate closes the group-level problem.
