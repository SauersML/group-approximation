---
rg: 2
id: marked-limits-of-special-groups-have-domain-group-rings
kind: claim
title: Marked limits of torsion-free virtually compact special groups satisfy the zero-divisor conjecture over every field
distinct_from:
  fisher-sanchez-peralta-special-and-3-manifold-domains: that gives domain group rings for torsion-free virtually compact special groups and their subgroups; this extends the conclusion to groups that are only marked limits of such groups, which need not embed in any of them.
  group-ring-domains-pass-to-local-embeddings: that is the general local transfer of the domain property; this specializes it to the geometric class where main has a domain theorem in every characteristic.
---

**ESTABLISHED.** Let `(G, S)` be a finitely generated marked group, and suppose
it is the limit in the space of marked groups of marked groups `(H_n, S_n)`,
each torsion-free and virtually the fundamental group of a compact special cube
complex. Then `k[G]` is a domain for every field `k`.

More generally, the same holds if every finite subset of `G` containing `1`
admits a multiplicative injection, in the sense of
`group-ring-domains-pass-to-local-embeddings`, into some torsion-free virtually
compact special group.

**Why this matters.** It turns Steenbock's question "Do Rips-Segev groups
satisfy Kaplansky's zero-divisor conjecture?" (arXiv:1307.0981, introduction)
into an approximation question. A Rips--Segev group would satisfy the
conjecture in every characteristic if it were a marked limit of torsion-free
virtually compact special groups. Its finite presentation forces such
approximants to be quotients of the group itself. So this needs no cubulation
of the Rips--Segev group itself.

DERIVATION
[[marked-limits-of-special-groups-domain-proof]]
