---
rg: 2
id: infinite-prime-localizations-embed-in-no-fg-linear-group
kind: claim
title: For an infinite set P of primes, Z[1/P] embeds in no finitely generated linear group over any field, so neither do GL_n(Z[1/P]) and GL_n(Q)
distinct_from:
  gl-n-q-embeds-in-fp-simple-group: that root's obstruction O1 excludes residually finite overgroups of GL_n(Q), which covers finitely generated linear ones; this excludes finitely generated linear overgroups of GL_n(Z[1/P]) for every infinite P, including the residually finite groups with P missing a prime, where O1 says nothing.
  fg-piecewise-linear-hosts-omit-natural-gl-n-q: that concerns the natural derivative of piecewise linear hosts; this is an abstract statement about any embedding into a finitely generated linear group.
  rational-linear-groups-satisfy-boone-higman: that embeds the finitely generated subgroups of GL_n(Q), whose entries involve finitely many primes; this shows no finitely generated linear group reaches infinitely many primes' divisibility at once.
---

**ESTABLISHED** through `infinite-prime-localizations-embed-in-no-fg-linear-group-proof`.
Lane proof, not independently reviewed. The arguments (valuations, congruence
filtrations) are standard, and no priority is claimed.

**Statement.** Let `P` be an infinite set of primes and `Z[1/P]` the ring of
rationals whose denominators are products of primes in `P`. Let `F` be any field
and `Γ <= GL_N(F)` a finitely generated subgroup. Then the additive group
`(Z[1/P], +)` does not embed in `Γ` as an abstract group.

In positive characteristic the proof gives more: a finitely generated linear
group over a field of characteristic `p > 0` has no element of infinite order
with `q^j`-th roots for all `j`, for any single prime `q`.

**Consequences.**
1. For `n >= 2` the unipotent matrices `[[1,x],[0,1]]` give `Z[1/P] <= GL_n(Z[1/P])`.
   So for every infinite `P`, `GL_n(Z[1/P])` lies in no finitely generated linear
   group. In particular this holds for `GL_n(Q)` (`P` = all primes).
2. For every co-nonempty infinite `P` the group `GL_n(Z[1/P])` is residually finite
   (`aff-n-over-z-localized-at-ell-is-rf-and-self-similar`), so O1 of the root does
   not apply to it. It is still out of reach of every route that first embeds
   the input in a finitely generated linear group and then applies
   `char-zero-linear-groups-satisfy-boone-higman`,
   `positive-char-linear-groups-satisfy-boone-higman` or
   `quasi-linear-groups-satisfy-permutational-boone-higman`.
   The same holds for subgroups of finite products `Γ_1 x ... x Γ_r` of
   finitely generated linear groups (possibly over fields of different
   characteristics). Two nonzero subgroups of the rank-one torsion-free group
   `Z[1/P]` meet nontrivially: if `a in K_1` and `b in K_2` are nonzero, then
   `ma = nb != 0` for suitable integers `m, n`. So the kernels of the
   projections cannot all be nonzero while intersecting trivially, and some
   projection of an embedded `Z[1/P]` is injective.
3. Any finitely generated overgroup of `GL_n(Z[1/P])`, `P` infinite, is therefore
   non-linear. That includes the self-similar hosts asked for in
   `aff-n-z-localized-lies-in-fp-self-similar-group`.
