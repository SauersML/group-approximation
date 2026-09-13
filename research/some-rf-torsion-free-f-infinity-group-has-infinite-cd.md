---
rg: 2
id: some-rf-torsion-free-f-infinity-group-has-infinite-cd
kind: claim
title: Some residually finite torsion-free group of type F_infinity has infinite cohomological dimension
distinct_from:
  some-torsion-free-f-infinity-group-of-infinite-cd-omits-f: that asks only that the group omit Thompson's group F; this asks for residual finiteness, which forces omitting F (thompson-f-is-not-residually-finite) and is strictly stronger
---

There is a residually finite torsion-free group `G` of type F_∞ with
`cd G = ∞`.

By `thompson-f-is-not-residually-finite` such a group contains no copy of `F`. So
this claim answers Zaremsky Problem 2.8 affirmatively, through the route
`tf-finf-infinite-cd-omits-f-via-residual-finiteness`.

## Attempts

- **Linear groups.** They are residually finite (Malcev), but torsion-free linear
  groups of type FP_∞ have finite cd. That follows from Kropholler's theorem for
  his class LH𝔉, which contains countable linear groups; the import is pending
  verification in this region. Dead.
  - The concrete case `SL_n(Z[t])`: congruence subgroups for the ideal `(p,t)` are
    torsion-free and have infinite cd (unipotent `⊕Z`), but `SL_n(Z[t])` is not
    FP_{n−1} (Bux–Mohammadi–Wortman, Comment. Math. Helv. 85 (2010)). So none of
    its finite-index subgroups is F_∞. Dead.
- **Elementary amenable groups.** Residually finite examples of infinite cd
  (`Z ≀ Z`) exist, but FP_∞ forces finite cd. Dead.
- **Self-similar groups.** They are residually finite
  (`self-similar-hosts-contain-only-residually-finite-groups`), and finitely
  presented self-similar hosts are large
  (`every-fp-rf-group-embeds-in-fp-self-similar-group`). But the known hosts
  contain torsion, and branch groups are not finitely presented. Open: a
  torsion-free self-similar group of type F_∞ containing `Z^n` for every `n`.
- **Consistency check.** Any group satisfying this claim is residually finite,
  of type FP_∞, torsion-free, and of infinite cd, so it lies outside LH𝔉. No
  residually finite group of that kind is known to this lane (bounded check,
  2026-09-13, literature access rate-limited).
