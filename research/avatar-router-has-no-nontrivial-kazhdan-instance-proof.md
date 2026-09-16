---
rg: 2
id: avatar-router-has-no-nontrivial-kazhdan-instance-proof
kind: route
title: Cubulate the small-cancellation output, fix a point with the Kazhdan partner, and kill the finite stabilizer by torsion-freeness
target: avatar-router-has-no-nontrivial-kazhdan-instance
requires:
  - hyperbolic-cubulated-groups-are-residually-finite
  - niblo-reeves-kazhdan-groups-fix-points-on-cube-complexes
  - cprime-one-sixth-presentations-hyperbolic-and-torsion-free
artifacts:
  - research/artifacts/torsion-free-router-nonhyperbolic-output-2026-09-16.md
---

Let `psi : N -> Q` be a homomorphism, with `N` Kazhdan and `Q` given by a
finite classical `C'(1/6)` presentation without proper-power relators.

1. By [[hyperbolic-cubulated-groups-are-residually-finite]], whose statement
   records that finite classical `C'(1/6)` presentations satisfy its
   hypothesis by Wise's cubulation theorem (GAFA 14 (2004), quoted in
   `hyperbolic-cubulated-rf-citation`), `Q` acts properly and cocompactly by
   combinatorial automorphisms on a CAT(0) cube complex `X`.
2. Cocompactness means finitely many `Q`-orbits of cubes, so the cube
   dimensions are bounded and `dim X` is finite.
3. `N` acts cellularly on `X` through `psi`.  By
   [[niblo-reeves-kazhdan-groups-fix-points-on-cube-complexes]] it fixes a
   point `p`.
4. `psi(N)` lies in the setwise stabilizer of the cube carrying `p` in its
   relative interior.  That stabilizer is finite by properness.
5. `Q` is torsion-free by
   [[cprime-one-sixth-presentations-hyperbolic-and-torsion-free]], so
   `psi(N) = 1`.

**Invalidation of `free-group-avatar-router`.**  That route's clause 3 makes
the partner map `psi : B -> Q` surjective from the Kazhdan partner `B` of
`bespoke-routing-lemma` onto `Q = F(y_1,y_2)/<<R>>`, where `R` is finite,
satisfies whole-family `C'(1/6)` and has no proper powers.  By steps 1--5,
`Q = 1`, while the same route requires the protected element `s != 1` to
survive in `Q`.

There is an independent cross-check through
`cubulated-hyperbolic-groups-are-virtually-special` and
`kazhdan-groups-map-trivially-to-torsion-free-special-groups`.
