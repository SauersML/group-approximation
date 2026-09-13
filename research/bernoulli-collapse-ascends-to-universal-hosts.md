---
rg: 2
id: bernoulli-collapse-ascends-to-universal-hosts
kind: claim
title: A Bernoulli entropy collapse over any countable group appears over a two-generator simple group, and over recursively presented groups on one fixed finitely presented host
distinct_from:
  bernoulli-entropy-counterexample-constraints: that proves a collapse passes to every supergroup; this combines that permanence with embedding theorems to place every collapse on explicit universal hosts.
  tester-host-has-positive-rokhlin-entropy-action: that is positive Rokhlin entropy on the tester host, which passes down to subgroups; this is Bernoulli entropy collapse, which passes up to supergroups and so gathers on the host from below.
---

**ESTABLISHED** by [[bernoulli-collapse-ascends-to-universal-hosts-proof]].

Let `D(G)` be the collapse subgroup of `bernoulli-isomorphism-collapse-set-is-a-subgroup`.

1. If `D(G) != {0}` for some countable group `G`, then `D(S) != {0}` for some two-generator simple group `S`.
   So `bernoulli-shift-entropy-classifies-for-every-group` is equivalent to its restriction to two-generator
   simple groups.
2. Let `U_*` be the two-generator finitely presented host of `whitehead-universal-finitely-presented-container`.
   If `D(K) != {0}` for some countably generated recursively presented group `K`, then `D(U_*) != {0}`. So
   base entropy classifies Bernoulli shifts over every such `K` as soon as it does over `U_*`.
3. For the binary Leavitt unit group `U = L_(F_2)(1,2)^x`, `D(U) ⊆ D(U_*)`.

**Reading.** For the negative direction, the first thing to decide is whether `D(U_*)` is nonzero. `U_*`
contains `U_* × U_*` and finite subgroups of every order. By item 8 of
`bernoulli-isomorphism-collapse-set-is-a-subgroup`, a collapse over `U_*` forces `h^Rok_sup(U_*) = 0`, which
is the negation of POS for `U_*`.
