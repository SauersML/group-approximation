---
rg: 2
id: split-decoders-have-generic-cantor-fibers
kind: claim
title: A cellular decoder with a section is bijective or has generic Cantor fibers
distinct_from:
  split-ca-defects-force-linear-observable-rank: that measures a tower of rational observable defects; this localizes a finite collision and embeds independent binary choices into single decoder fibers.
  nonlinear-certificate-fibers-are-all-surjective-or-all-strict: that concerns maps indexed by unchanged certificate configurations; this concerns inverse images of individual outputs of a split cellular map.
artifacts:
  - research/artifacts/gottschalk-decoder-fibers-2026-09-07.md
---

Let G be a group and A,B finite nonempty alphabets. Let cellular maps
tau:B^G -> A^G and sigma:A^G -> B^G satisfy sigma tau=id. Then sigma
is pre-injective exactly when it is bijective.

More precisely, if R=tau sigma is not the identity, memories N,M for
tau,sigma containing the identity give a distinct collision u,v of sigma,
with v=R(u), both constant off (NM)(NM)^(-1).

If G is infinite and sigma is not bijective, there is a dense G_delta
Omega in B^G of measure one for every full-support Bernoulli product
measure, such that sigma^(-1)(z) contains a closed copy of the Cantor
space {0,1}^N for every z in Omega. The same conclusion holds over every
configuration with dense G-orbit. It follows that one countable fiber
over a transitive configuration forces a split cellular map to be bijective.

No amenability, finite generation, or group approximation is assumed in
the theorem. Cardinality of fibers gives no automatic conditional entropy
bound for a measure concentrated on the chosen section. In particular
this does not establish surjunctivity in the square-alphabet case.
