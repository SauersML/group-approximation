---
rg: 2
id: positive-char-polynomial-affine-groups-are-self-similar
kind: claim
title: Affine groups over F_p[s_1..s_k] act self-similarly, with s_1 as the uniformizer and the other variables as parameter coordinates
distinct_from:
  polynomial-parameter-affine-groups-are-self-similar: that is characteristic zero, over Z[1/m][t_1..t_k] acting on Z_p^n x Z_p^k, where the uniformizer is the constant p; this is characteristic p, over F_p[s_1..s_k] acting on F_p[[u]]^n x F_p[[u]]^(k-1), where the variable s_1 is sent to the uniformizer u.
  principal-ideal-affine-groups-are-self-similar: that is Zaremsky's criterion, which needs a finite-index principal ideal xR with ∩ x^j R = 0 and so forces Krull dimension at most one; F_p[s_1..s_k] with k >= 2 has no such ideal, and the parameter coordinates replace it.
  function-field-soluble-groups-embed-in-fp-self-similar-groups: that puts soluble groups over one-variable function fields in Kochloukova--Sidki's upper triangular hosts; this is an affine host over polynomial rings in any number of variables, with no solubility.
---

**ESTABLISHED (2026-09-13)** through
`positive-char-polynomial-affine-groups-are-self-similar-proof`. ~~Not independently
reviewed.~~ *Reviewed:* PASS in `research/artifacts/review-metabelian-bh-2026-09-13.md`
(item 2, 2026-09-13). Status line updated 2026-09-18 by lane `bh-linear-fields`; the
mathematics is unchanged.

**Setting.**
- Let `p` be a prime, `k >= 1`, `R = F_p[s_1, ..., s_k]` and `n >= 1`.
- Let `Γ = E_n(R)` or `Γ = SL_n(R)`.
- Let `O = F_p[[u]]`. For `P in R` and `a = (a_2, ..., a_k) in O^(k-1)` write
  `P<a> = P(u, a_2, ..., a_k) in O`, and apply this entrywise to matrices and vectors.

**Claim.** `R^n x| Γ` acts faithfully on `X = O^n x O^(k-1)` by

```text
(g,b) · (v,a) = (g<a> v + b<a>, a).
```

This action preserves the rooted `p^(n+k-1)`-regular tree of residues mod `u^j`,
and it is self-similar: every first-level state lies in `R^n x| Γ`.

**The states.**
- Fix a first-level vertex `(e,α)` with `e in F_p^n` and `α in F_p^(k-1)`.
- Let `σ_α` be the ring endomorphism of `R` with `s_1 -> s_1` and
  `s_i -> α_i + s_1 s_i` for `2 <= i <= k`.
- Let `c = g(0,α) e + b(0,α) in F_p^n`.

Then `(g,b)` sends `(e,α)` to `(c,α)`, and its state there is

```text
( σ_α(g), (σ_α(g) e + σ_α(b) - c) / s_1 ).
```

**Compare.** For `k = 1` there are no parameters, `σ_α` is the identity, and
this is Zaremsky's action with `J = s_1 F_p[s_1]`
(`principal-ideal-affine-groups-are-self-similar`). For `k >= 2` the
coordinate ring has Krull dimension `k`, beyond that criterion. The mechanism is
the one of `polynomial-parameter-affine-groups-are-self-similar`, with the
variable `s_1` in the role that the constant `p` plays there.
