---
rg: 2
id: extreme-traces-and-local-pruning-do-not-select-fano-caps
kind: claim
title: Extremality, local pruning, and equivariant maximality do not select a Fano cap
distinct_from:
  rstar-fano-ghost-affine-hull-criterion: that characterizes which supports are safe once chosen; this proves three natural canonical selection rules need not choose one.
  tracial-support-affine-linearization: that permits passage to an extreme trace inside a support face; this shows extremality alone does not make the resulting local supports affine-safe.
  commuting-neighborhood-pruning-pays-atom-mass: that proves pruning under a no-joint-extension hypothesis; this gives exact models where every atom has an extension and the pruning fixed point remains the unsafe full relation.
---

ESTABLISHED.
None of the following operations forces Fano-cap support for `R_*`.

## Extreme traces

Let

```text
A=C^7 * C^7.                                                   (ETP1)
```

This is the universal algebra of two disjoint `R_*` contexts.  Map the first
context PVM to the seven coordinate rank-one projections in `M_7(C)` and the
second to their conjugates by the `7 x 7` Fourier matrix.  The two MASAs
generate `M_7(C)`: if `e_i` are the coordinate atoms and `q` is the Fourier
uniform-vector atom, then

```text
e_i q e_j=(1/7)e_(ij).                                           (ETP2)
```

Hence the map `A -> M_7(C)` is onto.  Composing with normalized matrix trace
gives a tracial state whose GNS von Neumann algebra is the factor `M_7(C)`,
so the trace is extreme.  Every atom in both contexts has trace `1/7`; its
local support is all seven Fano points and contains every line.

Thus passing to an extreme or factorial perfect trace does not imply cap
support.

## Pairwise or arc-consistency pruning

Take two copies of `R_*` joined by equality of their answer labels.  Every
atom has exactly one compatible neighbor atom.  The full seven-point domains
are therefore a fixed point of pairwise pruning, although they are not caps.
The same example survives any pruning rule whose only certificate for
deletion is absence of a compatible neighbor.

## Canonical maximal caps

After translation by the ghost, `GL(3,2)` acts transitively on the seven
nonzero points and preserves Fano incidence.  Therefore no nonempty proper
subset of `R_*` is invariant under every predicate symmetry.  In particular,
there is no symmetry-equivariant choice of one maximal cap; the four-point
caps form one orbit.  A local canonical rule must either break the labels
arbitrarily or retain the entire orbit of caps.

These are no-gos only for the stated canonical operations.  A globally
support-minimal perfect trace could still be cap-supported because the
instance's overlap structure breaks the local symmetry.  Proving that fact
for the actual Culf--Mastel completeness model, or finding a forced-line
counterexample inside that model, remains the sharp source-specific gate.
