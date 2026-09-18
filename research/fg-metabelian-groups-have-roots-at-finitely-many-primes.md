---
rg: 2
id: fg-metabelian-groups-have-roots-at-finitely-many-primes
kind: claim
title: In a finitely generated metabelian group an element of infinite order in the derived subgroup has q-th roots for only finitely many primes q, so no Z[1/P] with P infinite embeds
distinct_from:
  fg-linear-groups-have-roots-at-finitely-many-primes: that is the same root statement for finitely generated linear groups over fields; this is for finitely generated metabelian groups, which need not be linear.
  infinite-prime-localizations-embed-in-no-fg-linear-group: that excludes Z[1/P] from finitely generated linear groups; this excludes it from finitely generated metabelian groups.
---

**ESTABLISHED** through `fg-metabelian-groups-have-roots-at-finitely-many-primes-proof`.
Lane proof, not independently reviewed. Folklore-type (generic freeness); no
priority is claimed.

## Statement

Let `G` be a finitely generated metabelian group, so `G'` is abelian.
1. If `x ∈ G'` has infinite order, then there are only finitely many primes `q`
   for which `y^q = x` for some `y ∈ G`.
2. For every infinite set `P` of primes, the additive group `Z[1/P]` embeds in no
   finitely generated metabelian group. This includes `Z_(l) = Z[1/(all primes ≠ l)]`
   and `Q`.

## Consequences

- **Self-similar affine hosts in rank one.** `Aff_1(Z_(l)) = Z_(l) ⋊ Z_(l)^×` is
  metabelian. By item 2, it lies in no finitely generated metabelian group. So a
  finitely presented self-similar overgroup, as sought in
  `aff-n-z-localized-lies-in-fp-self-similar-group` (n = 1) and in
  `rational-iwahori-group-lies-in-fp-self-similar-group`, is not metabelian.
  This rules out the rank-one versions of Zaremsky's affine hosts
  `Z[1/m] ⋊ <units>`, and every other metabelian construction.
- **With the linear case.** Together with
  `fg-linear-groups-have-roots-at-finitely-many-primes`, any finitely generated
  group containing `Z[1/P]`, with `P` infinite, is neither linear over a field
  nor metabelian.
