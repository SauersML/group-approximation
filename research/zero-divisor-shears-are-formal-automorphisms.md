---
rg: 2
id: zero-divisor-shears-are-formal-automorphisms
kind: claim
title: Shears built from a zero-divisor pair of the group algebra are formally invertible automata
distinct_from:
  structurally-reversible-automata-are-formalizable: that treats track shears, sitewise linear maps and translations; this uses any pair of matrices over the group algebra with BA = 0, which contains the track shears (matrix-unit zero divisors) and also gives one-track gates on groups with torsion.
artifacts:
  - research/artifacts/stable-formalizability-on-simple-hosts-2026-09-12.md
---

Let `G` be a group, `k = F_q`, and `L_u(x)(h) = sum_m u_m x(hm)` for `u in M_(r x n)(k[G])`.
Suppose `A in M_(n x r)(k[G])` and `B in M_(r x n)(k[G])` satisfy `BA = 0`, and let `Gamma` be any
automaton on `(k^r)^G`, with any polynomial representative. Then

```text
T(x) = x + L_A(Gamma(L_B x)),     T'(x) = x − L_A(Gamma(L_B x))
```

are two-sided formal inverses of each other.

**Proof.** Linear maps compose exactly as polynomials, `L_u L_v = L_(uv)`. So formally
`L_B(x ± L_A w) = L_B x`, and the two composites telescope to `x`.

**Consequences.**
- **Track shears** are the case where `A` and `B` are matrix units.
- **Words** in these gates and in units of `M_n(k[G])` are formally invertible, hence bijective. A strict
  automaton is never such a word.
- **Torsion.** Elements of order `char k` give zero divisors `N = 1 − s`, `N^(char k) = 0`. So groups
  with such torsion carry one-track nonlinear formal automorphisms
  (`non-central-involutions-carry-nonaffine-formal-involutions`).

Proof: artifact Section 3, Theorem 5, route `zero-divisor-shears-formal-inverse-proof`.
