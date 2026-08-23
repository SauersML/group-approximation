---
rg: 2
id: finite-depth-readable-groupoid-closes-iff-full-orbit-is-finite
kind: claim
title: A finite-depth readable translate groupoid closes monomially only when the full readable orbit is finite
artifacts:
  - research/artifacts/zpc-finite-depth-groupoid-boundary-2026-08-23.md
distinct_from:
  zpc-readable-control-freezing-to-lcs: that asks for one invariant positive readable fiber in the particular perfect gap strategy; this proves a structural boundary theorem for retaining finitely many translated readable atoms without freezing.
  finite-groupoid-diagonals-have-only-classical-gluing: that classifies already closed finite groupoids; this proves that truncating an infinite readable translate action does not produce such a closed groupoid at any finite word depth.
  tensor-affine-selector-pattern-barrier: that obstructs scalar selector menus under tensor products; this concerns normalization of the whole finite readable atom algebra by unreadable group generators.
---

Let a finitely generated group `Gamma=<S>` act on an abelian von Neumann
algebra, and let `D_0` be a finite-dimensional Boolean subalgebra (the joint
readable partition).  Define

```text
D_n = join_{|w|<=n} w D_0 w^(-1).                         (FDG1)
```

Then the following are equivalent:

1. `D_n` is normalized by every generator in `S`;
2. `D_n=D_(n+1)`;
3. `D_n` contains every word translate of `D_0`.

Consequently, if the full translate algebra `D_infinity` is infinite
dimensional, every finite-depth inclusion is strict and **no** finite-depth
atom groupoid is closed under the unreadable generators.

This rules out a universal ZPC groupifier of the proposed monomial form.
Any ordinary group presentation in which the unreadable generators are
monomial relative to one finite readable diagonal makes them normalize that
diagonal.  Group multiplication then forces all word-depth translates into
the same finite algebra, regardless of the bounded depth of the verifier
constraints.  A truncated arrow `D_n -> D_(n+1)` is not a group action on a
finite object set; completing its boundary introduces extra return holonomy
not present in the source model.

The ZPC axioms do not force finite translate orbit.  There are perfect ZPC
pmp models with one named readable bit whose translates under one remote
unreadable shift generate the full Bernoulli coordinate algebra.  Hence
bounded verifier depth alone cannot justify the monomial compiler.  A
positive construction for the special perfect-gap game must prove additional
finite-orbit/invariant-fiber structure for its chosen strategy, or use a
genuinely nonmonomial canonical-trace mechanism.

