---
rg: 2
id: avatar-router-has-no-nontrivial-kazhdan-instance
kind: claim
title: Kazhdan groups map trivially to classical C'(1/6) groups, so the free-group avatar router has no instance
invalidates:
  - free-group-avatar-router
distinct_from:
  kazhdan-groups-map-trivially-to-torsion-free-special-groups: that concerns homomorphisms into torsion-free virtually compact special groups and marked limits; this specializes to finite classical C'(1/6) presentations through Wise's cubulation and Niblo--Reeves directly, and draws the consequence that the recorded avatar architecture for the routing lemma is uninstantiable.
  free-product-router-factor-embedding-obstruction: that kills factor-embedding free-product regimes through the partner field and points to the avatar presentation as the working architecture; this kills that avatar architecture itself, through property (T) of the partner and cubulation of the output.
  torsion-free-router-forces-nonhyperbolic-output: that obstructs hyperbolic outputs for the partner-free torsion-free router through Baumslag--Solitar subgroups and MF radicals; this obstructs classical C'(1/6) outputs in the Kazhdan lane through fixed points on cube complexes.
artifacts:
  - research/artifacts/torsion-free-router-nonhyperbolic-output-2026-09-16.md
---

**ESTABLISHED.**  Let `N` have Kazhdan's property (T).  Let `Q` be given by
a finite classical `C'(1/6)` presentation without a proper-power relator.
Then every homomorphism `N -> Q` is trivial.

*Proof sketch.*

* `Q` is word-hyperbolic and torsion-free, and it acts properly and
  cocompactly on a CAT(0) cube complex (Wise).
* Cocompactness makes the complex finite-dimensional.
* Niblo--Reeves gives a global fixed point for `N`.
* The image of `N` lies in a finite cube stabilizer, so it is trivial.

**Consequence.**  The route `free-group-avatar-router` presents the routed
quotient as `Q = F(y_1, y_2)/<<R>>`, where `R` is finite, satisfies
whole-family metric `C'(1/6)` and has no proper powers.  Its tying relators
make `psi : B ->> Q` surjective from the Kazhdan partner `B` ("so psi is onto
and (T) descends").  It also requires the protected element `s != 1` to
survive.  Surjectivity forces `Q = 1`, which contradicts survival.  No choice
of avatar words, piece ledger or length margins can repair this, so the route
is invalidated.

This does not refute `bespoke-routing-lemma`, which keeps its other route,
and it does not exclude Kazhdan quotients that are not classical `C'(1/6)`
groups.

Details are in Section 5 of the artifact.

DERIVATION
[[avatar-router-has-no-nontrivial-kazhdan-instance-proof]]
