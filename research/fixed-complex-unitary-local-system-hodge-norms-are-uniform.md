---
rg: 2
id: fixed-complex-unitary-local-system-hodge-norms-are-uniform
kind: claim
title: Cellular and analytic Hodge norms are uniformly equivalent for all unitary local systems on one fixed complex
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
distinct_from:
  iwahori-cochain-petersson-comparison: that applies the comparison to the cuspidal, Eisenstein and coboundary pieces of three modular groups; this is the fixed-base local-system norm theorem used for its interior part.
---

Let `X` be one fixed compact smooth triangulated manifold or orbifold, possibly
with boundary and fixed absolute or relative boundary conditions.  For every
finite-rank flat **unitary** bundle `E -> X`, equip cellular cochains with the
sum-of-squares norm on the fixed cells and differential forms with the `L^2`
norm.  On cohomology use the quotient cellular norm and the norm of the
analytic harmonic representative.  There are constants

```text
0<c_X<=C_X<infinity                                      (ULH1)
```

depending only on the fixed geometry and triangulation, not on the rank or
holonomy of `E`, such that

```text
c_X ||[a]||_cell <= ||[a]||_harm <= C_X ||[a]||_cell.   (ULH2)
```

The same statement holds for a fixed compact core with the corresponding
relative/interior cohomology.  No spectral gap for the local system is used;
the comparison is between quotient norms and follows from bounded chain maps
in both directions.

This does **not** by itself compare the compact-core harmonic norm with the
full Petersson `L^2` norm on an infinite cusp.  Such a comparison can lose
uniformity when parabolic holonomy approaches the identity; applications to
cuspidal automorphic cohomology must control that tail separately or work
directly in the cellular Hodge norm.
