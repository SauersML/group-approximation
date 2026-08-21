---
rg: 2
id: fanizza-wandering-dirichlet-return-route
kind: route
title: Replace the Fanizza heat-filter tower by one wandering return word
target: non-hyperlinear-group
requires:
  - two-copy-bcs-game-hamiltonian-dominates-fanizza-signal
  - wandering-mark-cesaro-amplifier
  - fanizza-wandering-dirichlet-return
  - kleene-completeness-needs-only-a-nontrivial-exact-representation
---

The two-copy theorem gives the explicit semantic inequality

```text
D_R <= C_m H_m
```

on every exact representation in the nonmember case.  Instead of returning
all polynomial filters of `H_m`, construct one infinite-order group word `w`
whose finite-matrix packet compression satisfies

```text
H_m <= C'(1-Re w)                                     (FWD1)
```

in the weighted sense needed by `wandering-mark-cesaro-amplifier`.  Arrange
by an HNN/free normal form that the translates of the fixed signal mark by
`w^k` are canonically orthogonal.  The Cesaro amplifier then gives a direct
finite-dimensional HS ceiling versus regular square-root growth.

Exact HALT completeness may realize the packet return on countably infinite
multiplicity.  The finite-matrix estimate must not become a universal
tracial inequality.

This is potentially smaller than `fanizza-heat-filter-one-sided-return`: it
asks for one ordinary return word and one Dirichlet-form comparison, not a
coherent return for every polynomial depth.
