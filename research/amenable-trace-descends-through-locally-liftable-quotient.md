---
rg: 2
id: amenable-trace-descends-through-locally-liftable-quotient
kind: claim
title: Amenable traces descend through locally liftable trace-preserving quotients
distinct_from:
  llp-regular-dominating-completion-forces-nonhyperlinear: that uses LLP of one representation completion to contradict hyperlinearity through Paulsen--Rahaman--Samei; this is the elementary trace-descent mechanism for one specified quotient map.
  invariant-free-near-state-is-amenable-regular-cover: that constructs the trace-kernel quotient associated to a near-state; this identifies the extra local-lifting property that would force amenability to survive that quotient.
---

Let `q:A -> B` be a unital surjective *-homomorphism and let `tau_B` be a
tracial state on `B`. Put `tau_A=tau_B o q`. Assume:

1. `tau_A` is an amenable trace on `A`; and
2. the quotient map is locally liftable: every finite-dimensional operator
   system `E subset B` admits a u.c.p. map `s:E -> A` with `q o s=id_E`.

Then `tau_B` is an amenable trace on `B`.

The trace-preserving hypothesis is load-bearing. Local lifting alone does not
make an arbitrary trace on the quotient amenable; here every multiplicative
defect of a local section lies in `ker q`, hence has exactly zero
`tau_A`-Hilbert--Schmidt seminorm.
