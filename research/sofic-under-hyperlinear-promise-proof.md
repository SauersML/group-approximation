---
rg: 2
id: sofic-under-hyperlinear-promise-proof
kind: route
title: Seed the countably generated switch with the hyperlinear nonsofic group and read the two isomorphism types as the promise
target: sofic-recognition-under-hyperlinear-promise-dichotomy
requires:
  - arbitrary-forbidden-seed-hereditary-property-switch
---

**(A)** is immediate.

**(B)**  Let `E` be a recursively presented hyperlinear nonsofic group.
The parametric switch of
[[arbitrary-forbidden-seed-hereditary-property-switch]] is stated for a
finite presentation code; for a recursively enumerated seed, let the
stage-`j` copy carry the first `j` relators of the seed's enumeration.  An
unbounded event set still kills every generator, and after a last cut all
tail copies are identified generator by generator, so their union carries
every relator of the seed and the group is again `E`.  So the outputs have
the two isomorphism types `1` and `E`, both hyperlinear, and
`P(G(c)) iff InfiniteDomain(c)` for `P` = sofic (hereditary, true for `1`,
false for `E`).  The reduction `c |-> switchCode(c)` is computable and lands
in the promise, which is the definition of `Pi02HardUnder` in
`Computability/SoficPromiseMFRecognition`.  Complements give the
`Sigma^0_2` statement.

If the bridge `B2` preserves hyperlinearity (open in general; it is an HNN
extension of `E * F(a,b)` along free subgroups), the same holds on
two-generator presentations.
