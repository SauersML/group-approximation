---
rg: 2
id: invariant-output-injective-ca-need-torsion-proof
kind: route
title: Invariant output factors through the coset shift over G/H, which is constant when H is infinite
target: invariant-output-injective-ca-need-torsion
requires:
  - full-shift-maps-to-infinite-stabilizer-coset-shifts-are-constant
artifacts:
  - research/artifacts/gk-vf-linear-verification-2026-09-12.md
  - research/artifacts/fournier-facio-torsion-free-host-constraints-2026-09-12.md
---

Section 2 of the artifact. `F(x)(gH) = tau(x)(g)` is well defined by invariance,
continuous, and equivariant for the left action on `G/H`, whose base point has
stabilizer `H`. If `H` is infinite the lemma makes `F` constant. Then `tau` is
constant, which contradicts injectivity because `A^G` has at least two points.

*Verified independently by `gk-vf-linear` (2026-09-12): `F` is well defined, continuous and left-equivariant, and the constancy lemma applies when `H` is infinite. See Section 7 of the linear-family verification artifact.*
