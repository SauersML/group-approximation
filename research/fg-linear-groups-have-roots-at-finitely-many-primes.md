---
rg: 2
id: fg-linear-groups-have-roots-at-finitely-many-primes
kind: claim
title: In a finitely generated linear group over a field, an element of infinite order has q-th roots for only finitely many primes q
distinct_from:
  piecewise-commutative-linear-hosts-miss-linear-gl-n-q: that uses residual finiteness to exclude divisible groups from finitely generated commutative-linear hosts; this excludes the residually finite group Z_(p), and every Z[1/P] with P an infinite set of primes, from finitely generated linear groups over fields.
  rational-iwahori-group-lies-in-fp-self-similar-group: that needs a finitely presented overgroup of Gamma_p, which contains Z_(p); by this lemma the overgroup cannot be linear over any field.
---

**ESTABLISHED** through `fg-linear-groups-have-roots-at-finitely-many-primes-proof`.
Lane proof, not independently reviewed. This is a folklore-type fact; no
priority is claimed.

## Statement

Let `K` be a field and `Λ <= GL_N(K)` finitely generated. Let `x ∈ Λ` have
infinite order. Then there are only finitely many primes `q` for which some
`y ∈ Λ` satisfies `y^q = x`.

## Consequences

- **No such Λ contains `Z_(p)`, `Z[1/P]` for an infinite set `P` of primes, or
  `(Q,+)`.** In each of these groups the element 1 has `q`-th roots for
  infinitely many primes `q`. So, for example, `GL_n(Z[1/P])` with `P` infinite
  lies in no finitely generated linear group over a field. This includes
  `n = 1`, where it concerns the additive group `Z[1/P]` inside the
  multiplicative group of a matrix algebra.
- **The rational Iwahori group.** `Γ_p` of
  `pgl2-q-in-rover-nekrashevych-group-of-rational-iwahori` contains the
  translations by `Z_(p)`. So a finitely generated overgroup of `Γ_p`, as sought
  in `rational-iwahori-group-lies-in-fp-self-similar-group`, is not linear over
  any field.
- **The case not already covered by O1.** `Z_(p)` is residually finite, so O1
  of `gl-n-q-embeds-in-fp-simple-group` does not exclude it. This lemma does,
  for linear groups.
