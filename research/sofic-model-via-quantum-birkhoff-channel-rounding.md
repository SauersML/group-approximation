---
rg: 2
id: sofic-model-via-quantum-birkhoff-channel-rounding
kind: route
title: Dead — classicalize the microstate channels by asymptotic quantum Birkhoff
target: hyperlinear-implies-sofic
requires: []
---

**Dead.**  Recorded as an attempt, not as a live decomposition; the kill is
`asymptotic-quantum-birkhoff-false`, which carries the `invalidates` key.

The attempt: given a hyperlinear microstate `g ↦ U_g`, replace each `U_g` by
the bistochastic channel `Ad U_g`, tensor many copies, and invoke an
asymptotic quantum Birkhoff theorem to approximate `(Ad U_g)^{⊗n}` by a convex
combination of permutation channels; select a permutation from the mixture for
each generator and read off a sofic model, the multiplicative defect being
carried along by the channel norm.

Where it dies: the second step is false.  Haagerup–Musat exhibit bistochastic
channels that stay a fixed distance from the mixed-unitary hull under all
tensor powers, so no theorem of the assumed shape exists — and the failure is
generic in the sense that it does not use any property of the group table, so
one cannot hope to dodge it by choosing the microstate well.

What survives: the *shape* of the argument — replicate, then classicalize —
is exactly the shape of `hyperlinear-implies-sofic-via-definetti-rounding`.
The difference that matters is that the replication there is balanced
(`balanced-replica-hs-amplification`) and the classicalization is asked only
on the symmetric-extension face cut out by the group table at the regular
trace, never for arbitrary channels.  This route is the record of why that
restriction is not optional.
