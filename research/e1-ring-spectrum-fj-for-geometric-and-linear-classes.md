---
rg: 2
id: e1-ring-spectrum-fj-for-geometric-and-linear-classes
kind: claim
title: Ring-spectrum Farrell--Jones holds for standard geometric and rational-linear classes
distinct_from:
  full-farrell-jones-for-fixed-fp-torsion-free-tester: that is an unresolved universal assertion for Lueck's Full K- and L-theoretic package, including finite wreath products and coefficient categories; this is an established K-theory theorem for specified group classes and arbitrary E1-ring spectra.
  a-theory-fj-fixed-two-generator-tester: that is an exact unresolved all-torsion-free-group A-theory tester with coefficients and finite wreath products; this establishes the un-twisted ring-spectrum assembly for four broad classes.
  connective-loday-assembly-fixed-fp-torsion-free-tester: that concerns connective integral assembly over the trivial family; this is nonconnective K-theory over the virtually cyclic family and arbitrary E1-ring spectra.
---

Let `R` be an `E1`-ring spectrum. Let `G` be a group satisfying at
least one of the following:

1. `G` is hyperbolic;
2. `G` is virtually solvable;
3. `G` is a subgroup of `GL_n(Q)` for some `n`; or
4. `G` acts isometrically, properly, and cocompactly on a
   finite-dimensional CAT(0) space.

Then the virtually-cyclic assembly map is an equivalence:

```text
colim_{G/V in G-VCyc-Orb} K(R[V])  ->  K(R[G]).
```

For `R` the sphere spectrum, this specializes to the corresponding
nonconnective Waldhausen A-theory assembly equivalence. The statement
does not include L-theory, arbitrary left-exact coefficient categories,
or an extra finite-wreath quantifier.

**ESTABLISHED 2026-01-11** by
[[bunke-kasprowski-winges-ring-spectrum-fj-citation]].
