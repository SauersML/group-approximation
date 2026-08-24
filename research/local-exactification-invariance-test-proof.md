---
rg: 2
id: local-exactification-invariance-test-proof
kind: route
title: Read the residual gauge group off each recorded witness
target: local-exactification-invariants-cannot-close-gluing-holes
requires: []
---

Items (1)--(3) are immediate: an observable computed from data that only
determine a `Gamma_loc`-orbit is a function on orbits, and a function constant
on an orbit cannot distinguish two points of that orbit, nor detect a property
that is itself `Gamma_loc`-stable and already realized on `G`.

The substance is the table, and each row is read directly off an existing
node.

**Per-context transport.**  `globally-conditioned-v4-exit-capacity` states
that its control term must be a bounded-overlap sum of relator energies
*before* local context copies are separated, and that the proof "may not
factor through the scalar list `(tau(P_c))_c`".  Independent local rounding
fixes each context's exit only up to its own conjugating isometry; the scalar
list is exactly the invariant part.

**Multiplicity involution.**  `paired-same-reservoir-boundary-lemma` records
the transition `t=R_f tensor V` with `V` a multiplicity involution invisible
to the covariance relations, which see conjugation only.  Conjugation by
`1 tensor V` fixes every visible relation, so `V` generates a residual gauge
direction.

**Tensor extension.**  `hybrid-rank-router-tensor-closure-obstruction` builds
its witness by tensoring three exact marked representations of the scalar
zero-overlap pairs `(HRT1)`.  Exactness of ordinary relators is preserved by
that operation, so it is a residual gauge direction for every observable
defined by exact relator satisfaction; `source-specific-pointed-rank-router-face`
is precisely the demand for an observable that is *not* invariant under it.

**Relative commutant.**  `full-raw-packet-commutant-witness` produces, by Haar
averaging over the unitary group of `Alg(rho_n(K))'`, a coordinate unitary
`V_n` commuting with the whole exactified packet and satisfying
`||[V_n,F_n]||_2^2>=3/8-o(1)`.  Conjugating the microstate by `V_n` fixes the
packet pointwise and moves the transported carrier, which is the definition of
a residual gauge direction that the local data cannot see.

The three screening examples in the consequences are then immediate: a scalar
per-context list is unchanged by per-context conjugation; a word in the
ordinary relators evaluates to the same exactness statement in a tensor
product; and an element of `Alg(rho_n(K))` commutes with `Alg(rho_n(K))'` by
definition.
