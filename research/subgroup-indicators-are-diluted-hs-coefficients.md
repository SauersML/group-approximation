---
rg: 2
id: subgroup-indicators-are-diluted-hs-coefficients
kind: claim
title: Every subgroup indicator is a diluted Hilbert--Schmidt coefficient profile
distinct_from:
  spectator-dilution-hides-root-profile-from-hs-correction: that starts from an existing asymptotic coefficient profile and erases its ambient mass; this constructs the subgroup profile itself from a fixed two-dimensional block.
  thin-selected-leak-amplifies-to-codense-quasiregular-profile: that begins with a selected matrix-ultraproduct leak and obtains a proper stabilizer; this needs no leak and applies to every subgroup of every group.
---

For every group `G` and every subgroup `H<=G`, there are integers
`d_n->infinity`, maps `beta_n:G->U(d_n)`, and unit vectors `xi_n`
such that `beta_n(e)=1` and

```text
sup_(g,h in G) ||beta_n(gh)-beta_n(g)beta_n(h)||_(2,d_n) -> 0,
<beta_n(g)xi_n,xi_n> = 1_H(g)                    (all n,g).
```

Thus a single distinguished-vector coefficient in normalized
Hilbert--Schmidt microstates imposes no restriction on a subgroup.

**ESTABLISHED 2026-08-31** by
[[diluted-subgroup-indicator-proof]].
