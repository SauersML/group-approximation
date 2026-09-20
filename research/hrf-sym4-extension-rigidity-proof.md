---
rg: 2
id: hrf-sym4-extension-rigidity-proof
kind: route
title: Use explicit low-weight polarization and Sylow-normalizer cohomology to split all Sym4 extensions
target: hrf-sym4-isotypic-modules-are-semisimple
requires: []
artifacts:
  - research/artifacts/hrf-sym4-extension-rigidity-2026-09-20.md
---

The artifact constructs the characteristic-19 decomposition
End(Sym4)=L0+L2+L4+L6+L8 by explicit polarization and proves each
summand irreducible using finite-torus weight projections and the two
unipotent substitutions. Restriction of H1 to the Sylow C19 is
injective: average an affine fixed point over its 180 cosets.

For each summand Lr, the cyclic norm is zero and H1(C19,Lr) is its
one-dimensional coinvariant quotient, represented by y^r. The diagonal
normalizer acts on it by a^(-r-2). None of these characters is trivial
for r=0,2,4,6,8. Restricted global classes must be normalizer-invariant,
so every H1 vanishes. The block-matrix cocycle description of extensions
then gives Ext1(V,V)=0 and induction splits every single-type module.

All operations and finite-characteristic coefficients are checked in
the written proof; no software computation or characteristic-zero
semisimplicity assumption is used.
