---
rg: 2
id: virtually-free-full-algebras-are-rfd-citation
kind: route
title: Import property FD for virtually free groups and read off joint faithfulness of the finite-dimensional representations
target: virtually-free-full-algebras-are-rfd
requires: []
artifacts:
  - research/artifacts/enders-shulman-ffw-llp-sources-2026-08-21.md
---

Three steps, the first two imported and the third elementary.

1. **Free groups have property FD** (Lubotzky--Shalom): the representations
   with finite image are dense in the unitary dual with the Fell topology.
2. **FD passes to finite-index overgroups.**  If `H <= G` has finite index and
   `H` has FD, inducing a finite-image representation of `H` to `G` gives a
   finite-dimensional representation of `G`, and induction is continuous for
   the Fell topology, so approximations upstairs of `Res_H pi` produce
   approximations of `pi` inside `Ind Res_H pi`, which contains `pi` as a
   subrepresentation.  A finitely generated virtually free `G` therefore has
   FD.
3. **FD implies `(VFR1)`.**  Density of the finite-dimensional representations
   in the unitary dual means every representation of `G` is weakly contained in
   the finite-dimensional ones.  The universal representation is one of them,
   so `pi_u prec (+)_(rho fin dim) rho`, and weak containment of the universal
   representation is exactly the norm identity `(VFR1)`; equivalently the
   direct sum of all finite-dimensional representations is faithful on
   `C^*(G)`.

Steps 1-2 are the literature content and are credited in the claim body, with
their verification status stated there.  This route is recorded as a citation
import, not as a derivation owned by this graph; see the claim's verification
paragraph for exactly which readings remain open.
