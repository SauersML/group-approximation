---
rg: 2
id: fg-metabelian-groups-have-roots-at-finitely-many-primes
kind: claim
title: In a finitely generated metabelian group an element of infinite order has q-th roots for only finitely many primes q, so no such group contains Z_(l) or Z[1/P] with P infinite
distinct_from:
  fg-linear-groups-have-roots-at-finitely-many-primes: that is the same conclusion for finitely generated linear groups over one field; finitely generated metabelian groups need not be linear, and this is proved directly from generic freeness.
  fp-metabelian-groups-satisfy-boone-higman: that embeds finitely presented metabelian groups in finitely presented simple groups; this shows that metabelian overgroups, including the finitely presented envelopes of Baumslag and Remeslennikov, cannot carry the residually finite hosts the gq routes need.
---

**ESTABLISHED** through `fg-metabelian-groups-have-roots-at-finitely-many-primes-proof`.
Lane proof, not independently reviewed. No priority is claimed.

**Statement.** Let `G` be a finitely generated metabelian group and `x in G` of
infinite order. Then there are only finitely many primes `q` for which some
`y in G` satisfies `y^q = x`.

**Consequences.**
- No finitely generated metabelian group contains `Z_(l)`, `Z[1/P]` with `P` an
  infinite set of primes, or `(Q,+)`. In each, `1` has `q`-th roots for
  infinitely many `q`.
- Finitely generated metabelian groups are residually finite (P. Hall), and every
  one embeds in a finitely presented metabelian group (Baumslag, Remeslennikov;
  survey arXiv:2306.16356v3, footnote 9). So this route to a finitely presented
  residually finite group fails for these inputs. It cannot supply the host `Λ` of
  `sl-2-z-localized-has-fp-hecke-overgroup`, a witness for
  `z-localized-embeds-in-fp-rf-group`, or a self-similar host of
  `aff-n-z-localized-lies-in-fp-self-similar-group`.
- The conclusion also follows from `fg-linear-groups-have-roots-at-finitely-many-primes`
  through Wehrfritz's embedding of finitely generated metabelian groups in finite
  products of linear groups over fields of different characteristics: `x` and its
  roots project to some factor where `x` has infinite order. The proof here does not
  use that import.
