---
rg: 2
id: unique-trace-signed-corner-quotient-proof
kind: route
title: Pull back a quotient trace and identify the two GNS completions
target: unique-trace-signed-corner-quotient-forces-nonhyperlinear
requires: []
---

Take any trace `sigma` on the quotient `B`.  Trace uniqueness on the signed
corner gives `sigma Phi=tau_q`.  The surjection `Phi` therefore induces a
unitary from the `L2` completion of `A` modulo the `tau_q`-null ideal onto the
`L2` completion of `B` modulo the `sigma`-null ideal, intertwining left
multiplication.  Their generated von Neumann algebras are isomorphic.

Hyperlinearity makes the canonical group trace Connes embeddable, and a
positive central corner of a Connes-embeddable finite von Neumann algebra is
Connes embeddable.  The GNS isomorphism would make `sigma` Connes embeddable,
contradicting the hypothesis on `B`.

