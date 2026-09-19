---
rg: 2
id: nonhyperlinear-from-profile-pure-finite-projection-orbit
kind: route
title: Put the profile-pure stabilizer quotient inside one fixed Higman universal group
target: non-hyperlinear-group
requires:
  - perfect-zpc-irs-quantum-gap-game
  - perfect-gap-zpc-has-profile-pure-finite-projection-orbit
  - profile-pure-finite-projection-orbit-groupifies-zpc-gap
  - mikaelian-explicit-higman-embedding
  - local-approximation-properties-are-marked-closed
---

Choose the perfect gap ZPC-IRS witness with the projection orbit asserted by
`perfect-gap-zpc-has-profile-pure-finite-projection-orbit`. The
profile-pure projection compiler constructs a finitely presented group
`K_T` which is not hyperlinear.

Fix a computable enumeration of all finite group presentations and take the
countable free product of the presented groups. Apply the explicit
Mikaelian--Higman embedding once and for all to obtain a fixed finitely
presented group `V` containing that recursively presented free product.
Thus `V` contains an isomorphic copy of every finitely presented group,
including the existentially selected `K_T`.

Hyperlinearity passes to subgroups by
`local-approximation-properties-are-marked-closed`. If `V` were
hyperlinear, its subgroup `K_T` would be hyperlinear, a contradiction.
Therefore the fixed explicit finitely presented group `V` is
nonhyperlinear.
