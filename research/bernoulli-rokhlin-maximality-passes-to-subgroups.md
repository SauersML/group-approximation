---
rg: 2
id: bernoulli-rokhlin-maximality-passes-to-subgroups
kind: claim
title: Maximal Rokhlin entropy of uniform Bernoulli shifts passes to subgroups and up finite index
distinct_from:
  bernoulli-entropy-counterexample-constraints: that derives inheritance for failures of the base-entropy classification from Seward's imported computation; this proves inheritance of maximal uniform Bernoulli Rokhlin entropy directly, by restriction and transversal joins, with no import.
artifacts:
  - research/artifacts/gottschalk-rokhlin-entropy-route-2026-09-12.md
---

A countable group `G` is **Rokhlin-maximal at `q`** if
`h^Rok_G((A^k)^G, uniform) = k log q` for every `k >= 1`, where `|A| = q`.

1. For `H <= G` and a finite set `L`, `h^Rok_G(L^G) <= h^Rok_H(L^H)`. So every
   subgroup of a Rokhlin-maximal group is Rokhlin-maximal.
2. If `[G:H] = n` is finite, then `h^Rok_H(Y) <= n h^Rok_G(Y)` for every
   measure-preserving `G`-action `Y`, and `L^G` restricted to `H` is the uniform
   Bernoulli shift `(L^n)^H`. So `G` is Rokhlin-maximal when `H` is.

**ESTABLISHED 2026-09-12** by
[[bernoulli-rokhlin-maximality-passes-to-subgroups-proof]].
