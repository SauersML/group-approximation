---
rg: 2
id: a3-cone-repairs-to-coboundaries-not-cocycles-proof
kind: route
title: A simply connected cone has no holonomy to keep
target: a3-cone-repairs-to-coboundaries-not-cocycles
requires: []
artifacts:
  - research/artifacts/hyperbolic-residual-finiteness-audit-2026-08-17.md
  - notes/TRUE_A3_METRIC_CONE_SYNCHRONIZATION.md
  - notes/TRUE_AUXILIARY_CONE_RADICAL_WITNESS_NO_GO.md
---

The synchronization theorem produces a **vertex gauge** `a` with
`||a·φ||` small.  A connection that is exactly gauge-trivial is a coboundary;
the theorem's conclusion is therefore of the form "`φ` is close to `B^1`", and
its proof is the reason: the Dinur--Meshulam filling assigns to each edge an
explicit contractible disk of at most nine triangles, and the gauge is built
by transporting along those fillings from a base vertex.  Such a construction
is well defined precisely because the relevant cone is simply connected — any
two transport paths are related by a filling, so curvature bounds the
discrepancy.

On a complex with `π_1 ≠ 1` the same recipe is not even well posed: transport
around a noncontractible loop returns the holonomy of `φ`, and a gauge cannot
remove it.  A flat connection with nontrivial holonomy is a cocycle at
distance `0` from `Z^1` and at distance bounded below from `B^1`, so the two
distances are not comparable in the direction needed; an estimate against
`B^1` is strictly stronger where it applies and simply unavailable where the
fundamental group is nontrivial.

The repository's own auxiliary-cone no-go is the quantitative form of the same
sentence: for the sofic-radical witness, radical membership forces the encoded
paths closed on `1-o(1)` of the base, and then

```text
average w-holonomy energy
  <= cone_constant · curvature_energy
   + diameter_constant · C_rad · relator_motion,
```

so vanishing curvature and vanishing relator motion force the marked holonomy
to vanish.  A cone that kills marked holonomy is a cone that cannot certify a
nontrivial cocycle class.
