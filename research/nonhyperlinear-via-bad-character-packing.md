---
rg: 2
id: nonhyperlinear-via-bad-character-packing
kind: route
title: Pack one maximal forbidden root atom past the marked-sector capacity
target: non-hyperlinear-group
requires:
  - mipstar-bcs-tracial-nonru-exists
  - maximal-forbidden-atom-has-a-named-positive-half
  - finite-pauli-seed-reducing-quarter-carrier
  - simultaneous-character-packing-removes-max-loss
  - finite-bad-character-packing-extension
---

**INVALIDATED.**  Its packing prerequisite is refuted by
`canonical-trace-forbids-supercritical-character-packing`: the canonical
trace gives `K<=2M/beta`, while the route requires a strictly larger `K`.

Adjoin the finite overgroups supplied for the finitely many forbidden types,
identifying each `H_i` with its seed-context words. Their prescribed trace
extensions agree with the perfect contextual trace on the amalgamated
finite-dimensional context images, so trace-compatible amalgamated free
products give one exact tracial representation with `J=-1`.

In a hypothetical canonical microstate, correct the finite Pauli seed and
round the contextual tuple in its commutant. Choose the maximal root
forbidden type. Its `K=floor(2M/beta)+1` conjugates satisfy the static packing
compiler, which contradicts the capacity of `Q_-`. The exact model proves
that `J` is nontrivial in the presented group, so the contradiction excludes
hyperlinearity of that finite ordinary presentation.
