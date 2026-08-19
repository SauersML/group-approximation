---
rg: 2
id: nonhyperlinear-from-supercritical-pauli-branching
kind: route
title: A supercritical Pauli branching component forbids atlas microstates
target: non-hyperlinear-group
requires:
  - atlas-steinberg-rank-five-translation
  - perron-frobenius-branching-carrier-collapse
  - atlas-supercritical-pauli-branching-cycle
---

`atlas-steinberg-rank-five-translation` fixes the explicit finite atlas group
`Gamma_St` and its canonical trace target.  Assume `Gamma_St` were
hyperlinear.  Then there would be trace-preserving finite-dimensional
microstates whose fixed atlas relator defect `delta_n` tends to zero.

Apply `atlas-supercritical-pauli-branching-cycle` after exactifying its fixed
finite Pauli packet.  On the supercritical strongly connected component it
produces carrier masses `x^(n)`, Perron weights `y`, and leakage vectors
`e^(n)` with

```text
y . x^(n) >= c0,
y . e^(n) <= C delta_n^c.
```

The established trace-capacity theorem
`perron-frobenius-branching-carrier-collapse` gives

```text
(rho-1) y . x^(n) <= y . e^(n).
```

Since `rho>1`, the left side is bounded below by `(rho-1)c0>0`, whereas the
right side tends to zero.  This contradiction rules out a hyperlinear
microstate sequence for the canonical trace.  Hence the explicit atlas group
is nonhyperlinear.

The gain over the one-cut route is structural: the two already-known Pauli
branches may expand into a different coefficient carrier and the return may
pass through arbitrarily many fixed finite sectors.  Only the spectral radius
of the finite branch automaton matters.