---
rg: 2
id: resolvent-elementary-groups-are-not-fp
kind: claim
title: For every prime l and every N >= 3, the elementary group E_N(R_l) of the resolvent presentation ring is not finitely presented
distinct_from:
  resolvent-elementary-group-is-fp: that is the open claim that E_N(R_l) is finitely presented for some l and N >= 5; this is its negation, for every l and N >= 3.
  resolvent-ring-corner-symbols-survive-in-k2: that is the K_2 input; this is the group-theoretic consequence.
artifacts:
  - research/artifacts/gq-gq-k2-q-resolvent-corner.md
---

**ESTABLISHED (2026-09-18)** through `resolvent-elementary-groups-are-not-fp-proof`. Lane proof (gq-k2-q), not
independently reviewed. It refutes `resolvent-elementary-group-is-fp`, and so closes the route
`z-localized-fp-rf-via-fp-resolvent-elementary-group-over-r-l` to `z-localized-embeds-in-fp-rf-group`.

**Statement.** For every prime `l` and every `N >= 3`, `E_N(R_l)` is not finitely presented. Neither is
`E_N(R_l)/C` for any finite normal subgroup `C`.

**Reason.**
- The corner symbols `c(λ,μ)` lie in `K_2(N, R_l)`, and their stable classes generate a subgroup of `K_2(R_l)`
  that is not finitely generated (`resolvent-ring-corner-symbols-survive-in-k2`).
- If `E_N(R_l)` were finitely presented, the image of `K_2(N, R_l)` in `K_2(R_l)` would be finitely generated
  (`infinitely-generated-symbols-block-fp-elementary-groups`, part 1).
- These two facts are incompatible.
