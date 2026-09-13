---
rg: 2
id: serre-class-atoms-obey-degree-bound
kind: claim
title: A Serre-class measure puts mass at most 1/d on a real algebraic number of degree d and no mass on a transcendental number
distinct_from:
  atomic-serre-measures-are-equal-weight-real-orbits: that characterizes the purely atomic Serre-class measures supported on algebraic integers; this bounds the atoms of an arbitrary Serre-class measure, continuous part allowed, and excludes transcendental atoms
  galois-invariance-implies-algebraic-eigenvalues: that derives algebraic eigenvalues from invariance of kernel dimensions under automorphisms of C; this derives algebraic atoms from the Serre inequalities alone, through the box principle
  integral-spectral-limits-satisfy-serre-inequalities: that shows limits of integer spectra lie in the Serre class; this is a consequence of lying in the Serre class, valid with no approximation in sight
artifacts:
  - research/artifacts/determinant-spectral-atoms-2026-09-12.md
---

**ESTABLISHED** by `serre-class-atoms-degree-bound-proof` (artifact Theorem 1).

Let `mu` be a compactly supported probability measure on `R` with
`integral_(Q != 0) log|Q| d mu >= 0` for every nonzero `Q in Z[x]`. Then for
every `x in R`,

```text
mu({x}) <= 1 / deg(x),        deg(x) = [Q(x):Q],  = infinity if x is transcendental.
```

So every atom of `mu` is algebraic.

**Sharp.** The uniform measure on a Galois orbit of `d` totally real algebraic
integers is in the class and has mass exactly `1/d` at each conjugate.

**Not stronger.** The class admits an atom `1/2` at the rational
non-integer `1/2`, and Galois-unequal atoms at `phi^2` and `phi^(-2)`
(artifact Examples 4.1 and 4.2). So the only arithmetic the one-variable class
forces on atoms is this degree bound.
