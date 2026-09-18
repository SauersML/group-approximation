---
rg: 2
id: char-p-linear-groups-satisfy-permutational-boone-higman
kind: claim
title: Every finitely generated linear group in positive characteristic lies in a finitely presented self-similar group, hence in the permutational Boone--Higman class
distinct_from:
  positive-char-linear-groups-satisfy-boone-higman: that is the plain property through Leavitt projective elementary hosts, which are not known to carry type (A) actions; this puts the same groups inside finitely presented self-similar affine groups over F_p[s_1..s_k], hence in B_A.
  char-zero-linear-groups-satisfy-permutational-boone-higman: that is characteristic zero, through hosts over Z[1/m][t_1..t_k]; this is positive characteristic, through hosts over F_p[s_1..s_k].
  global-field-soluble-linear-products-satisfy-boone-higman: that reaches only soluble groups, and in positive characteristic only transcendence degree at most one; this is every finitely generated linear group in positive characteristic.
  positive-char-surface-linear-groups-satisfy-boone-higman: that is transcendence degree at most two, through Leavitt tensor envelopes; this is every transcendence degree, through self-similar hosts.
---

**ESTABLISHED (2026-09-13)** through
`char-p-linear-pbh-via-polynomial-self-similar-hosts`. The route composes the
three new nodes of lane `bh-metabelian` with established, reviewed nodes. ~~Not
independently reviewed.~~ *Reviewed:* the route and all three new nodes PASS in
`research/artifacts/review-metabelian-bh-2026-09-13.md` (items 2–4, 2026-09-13).
Status line updated 2026-09-18 by lane `bh-linear-fields`; the mathematics is
unchanged.

**Statement.** Let `K` be a field of characteristic `p > 0` and let
`H <= GL_n(K)` be finitely generated. Then `H` embeds in a finitely presented
self-similar group, namely `R^N x| E_N(R)` with `R = F_p[s_1, ..., s_k]`. So `H`
embeds in a group admitting an action of type (A): it is in `B_A`, as defined in
`boone-higman-type-a-class-closed-under-finite-extensions`. In the language of
Belk--Fournier-Facio--Hyde--Zaremsky (BFFHZ), arXiv:2503.21882v2, `H` satisfies
the permutational Boone--Higman conjecture.

**Consequences.**
- **Envelope.** `H` embeds in a finitely presented simple group, through
  Zaremsky's Theorem 1.1, and in a finitely presented simple twisted
  Brin--Thompson group, through BFFHZ Theorem C.
- **Permanence.** By parts 1--3 of
  `boone-higman-type-a-class-closed-under-finite-extensions`, finite direct
  products of such groups with each other, with characteristic-zero linear groups
  and with other members of `B_A` embed in finitely presented simple groups, as do
  their finite-index overgroups. This is
  `quasi-linear-groups-satisfy-permutational-boone-higman`.

**Examples.**
- `SL_n(F_p[s_1, ..., s_k])` for every `k`, and `Z/p wr Z^k`.
- Baumslag's finitely presented metabelian group `F_p[x^±1, (1+x)^-1] x| Z^2`.

**Credit.** The mechanism is the characteristic-zero one of
`char-zero-linear-groups-satisfy-permutational-boone-higman`, with the variable
`s_1` as the uniformizer. The bounded novelty search is recorded in
`research/artifacts/bh-quasi-linear-pbh-2026-09-13.md`.
