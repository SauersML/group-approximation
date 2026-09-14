---
rg: 2
id: mf-root-transport-is-vacuous-on-leavitt-units-proof
kind: route
title: Full MF radical leaves only the trivial corona model to extend
target: mf-root-transport-is-vacuous-on-leavitt-units
requires: [binary-leavitt-all-ranks-full-mf-radical]
---

By `binary-leavitt-all-ranks-full-mf-radical`, `Rad_MF(G) = G`: every
homomorphism from `G` into a norm matrix corona unitary group has kernel `G`.
The extension step of the matrix-root argument starts from such a
homomorphism, so it starts from the trivial one, and its extension detects no
coefficient.

For the subgroup clause, the same theorem covers every positive matrix rank
`GL_n(L) = EL_n(L)`.  If `EL_n(L) <= K`, every homomorphism from `K` to a
corona restricts to a homomorphism from `EL_n(L)`, which is trivial.  So
`EL_n(L) <= Rad_MF(K)`, and the transport over `K` detects none of its
elements.
