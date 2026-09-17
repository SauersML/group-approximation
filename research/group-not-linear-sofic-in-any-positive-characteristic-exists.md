---
rg: 2
id: group-not-linear-sofic-in-any-positive-characteristic-exists
kind: claim
title: Some countable group is not linear sofic over any field of positive characteristic
distinct_from:
  non-linear-sofic-group: that asks for failure over one field; this asks for failure over F_p for every prime p, possibly with a group that is complex-linear sofic.
  non-finite-field-linear-sofic-group-exists: that also forbids models in large characteristic; this allows them, so it is the fixed-characteristic component only.
  non-large-characteristic-linear-sofic-group-exists: that is the large-characteristic component of the root; this is the fixed-characteristic component.
  linear-sofic-group-algebra-is-stably-finite: that gives stable finiteness from linear soficity over one field; this is the existence of a group escaping every positive characteristic, for which non-stable-finiteness of every F_p[G] is one sufficient certificate.
---

**OPEN.** Some countable `G` is not `F_p`-linear sofic for any prime `p`.
- Equivalently, for every prime `p` some `G_p` is not `F_p`-linear sofic. The free product of the `G_p` is a single
  witness, and it can be taken two-generator simple.
- Definitions are on `root-splits-into-large-and-fixed-characteristic-witnesses`.

**Role.** This is component (b) of the characteristic split. The root holds iff this holds together with
`non-large-characteristic-linear-sofic-group-exists`. Given a witness `H` of that component, only the primes in the
finite set `S(H)` are needed here.

**Sufficient certificates.**
- **Direct finiteness, prime by prime.** For each `p`, find `G_p` and a one-sided invertible matrix pair over `F_p[G_p]`
  (`linear-sofic-group-algebra-is-stably-finite`). Formal strict pairs also work
  (`formalizable-strict-pairs-certify-non-linear-soficity`).
- **Asymmetry with component (a).**
  - In characteristic `0`, group algebras are stably finite (Kaplansky), and every `C[G]` carries a separating
    Sylvester rank function.
  - No such theorem is known in characteristic `p`. So algebraic certificates are available here and only here.
