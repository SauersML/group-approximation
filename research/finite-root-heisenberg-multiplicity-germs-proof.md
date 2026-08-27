---
rg: 2
id: finite-root-heisenberg-multiplicity-germs-proof
kind: route
title: Apply finite Fourier theory and lift the finite-dimensional group algebra on a tail
target: finite-root-heisenberg-multiplicity-germs
requires:
  - matrix-corona-projection-monoid-is-rank-germs
---

The root addition relation makes `a |-> rho(x_ij(a))` an exact unitary
representation of `A`.  Finite Fourier orthogonality makes the displayed
elements pairwise orthogonal projections summing to one.  Rank-germ dimension
is additive, and the usual restriction identity for characters gives the
refinement formula.

For the three-root window, the Steinberg relations make the `C` root central
and give the displayed bilinear commutator law.  Finiteness of `A,B,C` makes
the generated group finite.  Its group C-star algebra is finite-dimensional.
Lifting a finite system of matrix units and applying spectral and polar
correction gives exact coordinate representations on a cofinite tail.

At coordinate `n`, decompose this exact representation as

```text
directSum_(pi in Irr(H)) C^(m_(pi,n)) tensor pi.
```

The germ `[m_(pi,n)]` is independent of exactification: the minimal central
projection for `pi` has rank `(dim pi)m_(pi,n)`, and its rank germ is intrinsic
to the corona representation.  Ordinary restriction of finite-group
representations supplies the integral branching maps between nested windows.
