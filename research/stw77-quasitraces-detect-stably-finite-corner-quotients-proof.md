---
rg: 2
id: stw77-quasitraces-detect-stably-finite-corner-quotients-proof
kind: route
title: Divide by the quasitrace null ideal and invoke Blackadar-Handelman in reverse
target: stw77-quasitraces-detect-stably-finite-corner-quotients
requires: []
---

Suppose first that `pi:C->Q` is a nonzero stably finite quotient.  The
Blackadar--Handelman theorem gives a nonzero bounded `2`-quasitrace on the
unital stably finite algebra `Q`; after scaling at `1_Q` it is normalized.
Composing with `pi` gives a normalized `2`-quasitrace on `C`.

Conversely, let `tau` be a normalized `2`-quasitrace on `C`.  Its null space

`N_tau = {x in C : tau(x*x)=0}`

is a closed two-sided ideal, and `tau` descends to a faithful normalized
`2`-quasitrace on `Q=C/N_tau`.  The quotient is nonzero because `tau(1)=1`.
It is stably finite.  Indeed, the matrix extensions of the descended
quasitrace are faithful.  If an isometry `v` in some `M_n(Q)` had proper range
projection, quasitracial invariance would give

`tau_n(vv*) = tau_n(v*v) = tau_n(1)`,

while orthogonal additivity and faithfulness would give
`tau_n(1-vv*)>0`, a contradiction.

Finally, Haagerup, [*Quasitraces on exact C*-algebras are
traces*](https://arxiv.org/abs/1403.7653), proves that every `2`-quasitrace on
a unital exact C*-algebra is a trace.  A tracial state is already a normalized
`2`-quasitrace, giving the exact-case equivalence.
