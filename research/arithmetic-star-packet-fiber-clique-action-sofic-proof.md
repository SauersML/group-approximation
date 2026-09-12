---
rg: 2
id: arithmetic-star-packet-fiber-clique-action-sofic-proof
kind: route
title: Reuse finite telescope orbits and cyclic stacking with the induced clique relation
target: arithmetic-star-packet-fiber-clique-action-sofic
requires:
  - arithmetic-star-packet-carrier
artifacts:
  - GroupApproximation/Sofic/AscendingHNNCosetActionSofic.lean
  - GroupApproximation/Sofic/SoficActionFiniteOrbits.lean
  - GroupApproximation/Sofic/SoficActionCyclicExtension.lean
  - GroupApproximation/Sofic/MappingTelescopeFiniteOrbits.lean
---

The kernel `L=ker(theta)` has finite index in `P`.  Since the finite-index
compression makes `P` commensurated in `E`, commensurability is transitive and
`L` is commensurated in `E`.  Every telescope level is commensurable with `P`
and hence with `L`.  Apply
`MappingTelescopeFiniteOrbits.finite_orbit_on_quotient_of_commensurated` with
quotient subgroup `L`: every level has finite orbits on `E/L`.

The proof of `isSoficAction_telescope_cosets` now applies verbatim to `E/L`.
Its models are the exact finite-orbit models from
`SoficActionFiniteOrbits.lean`, not arbitrary approximate charts.  Give their
finite chart targets the relation induced by

```text
adj(y,z) <=> y!=z and image(y)=image(z) in E/P.
```

Every chart permutation comes from a level element and therefore preserves
this invariant relation exactly.  The cyclic extension theorem stacks these
models and defines its height-`j` chart by precomposing with `t^(-j)`.  Since
each `t^(-j)` is also a graph automorphism, the stacked charts still preserve
the full induced graph on every finite window.  These are precisely finite
sofic graph-action models.

