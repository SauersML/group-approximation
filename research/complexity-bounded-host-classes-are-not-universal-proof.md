---
rg: 2
id: complexity-bounded-host-classes-are-not-universal-proof
kind: route
title: Transfer a host word-problem bound down an embedding and contradict the graph-shift hardness
target: complexity-bounded-host-classes-are-not-universal
requires:
  - graph-shift-groups-have-arbitrarily-hard-word-problem
artifacts:
  - research/artifacts/boone-higman-self-similar-and-complexity-2026-09-11.md
---

Put `T+(m) = m + max_(k<=m) T(k)`, which is recursive, monotone and at least
`T`. By `graph-shift-groups-have-arbitrarily-hard-word-problem` choose a
decidable `A` such that the word problem of `G_A` over `{a,b}` has no
algorithm within `C*T+(C*l) + C*l + C` for any `C`.

Suppose `G_A <= S in K`, with `a, b` written as words over the given
generating set of `S` of length at most `L`. A word of length `l` over
`{a,b}` becomes, by substitution in time `O(L*l)`, a word of length at most
`L*l` over the generators of `S`, trivial in `S` iff the original is trivial
in `G_A`. The host algorithm answers in time

```text
C_S*T(C_S*L*l) + C_S*L*l + C_S  <=  C'*T+(C'*l) + C'*l + C'
```

for the constant `C' = C_S*L + O(L) + C_S`, using monotonicity of `T+` and
`T <= T+`. Adding the substitution cost keeps the same form. That is a
word-problem algorithm for `G_A` within the excluded bound, a contradiction.
The embedding is not assumed effective; `L` is a constant once one is chosen.
`∎`
