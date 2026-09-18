---
rg: 2
id: fg-metabelian-groups-have-roots-at-finitely-many-primes
kind: claim
title: In a finitely generated metabelian group an element of infinite order in the derived subgroup has q-th roots for only finitely many primes q, so no Z[1/P] with P infinite embeds
distinct_from:
  fg-linear-groups-have-roots-at-finitely-many-primes: that is the same root statement for finitely generated linear groups over fields; this is for finitely generated metabelian groups, which need not be linear.
  infinite-prime-localizations-embed-in-no-fg-linear-group: that excludes Z[1/P] from finitely generated linear groups; this excludes it from finitely generated metabelian groups.
artifacts:
  - research/artifacts/gq-referee-a-z-localized-tree-mapping-torus-metabelian.md
---

**ESTABLISHED** through `fg-metabelian-groups-have-roots-at-finitely-many-primes-proof`.
Lane proof. *Reviewed:* PASS by `gq-referee-a`, including the addendum
(`research/artifacts/gq-referee-a-z-localized-tree-mapping-torus-metabelian.md`, §3). Folklore-type (generic freeness); no
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

## Addendum (lane gq-infinite-primes, 2026-09-17)

Not independently reviewed.
- **Item 1 for every element of G.** Let `x in G` have infinite order and `y_q^q = x`
  for infinitely many `q`. Write `G/G' = Z^s ⊕ T` with `T` finite of exponent `ε`.
  - The `Z^s`-parts of `x̄` and of every `ȳ_q` vanish, since they are divisible by
    infinitely many primes, respectively killed by `q`.
  - So `z = x^ε in G'` has infinite order and the `q`-th roots `y_q^ε`.
  - Item 1 applies to `z` and gives a contradiction.
- **No metabelian Λ.** The Baumslag--Remeslennikov finitely presented metabelian
  envelopes are residually finite, but by item 2 they cannot supply the host `Λ` of
  `sl-2-z-localized-has-fp-hecke-overgroup` or a witness of
  `z-localized-embeds-in-fp-rf-group`.
