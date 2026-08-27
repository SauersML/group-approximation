---
rg: 2
id: atlas-first-post-a10-edge-has-no-degree-ten-completion
kind: claim
title: The first post-A10 core edge has no internal degree-ten permutation completion
artifacts:
  - experiments/atlas_a4_a10_first_cycle_internal_search.py
  - research/artifacts/atlas-a4-first-cycle-s10-screen.json
  - research/atlas-first-post-a10-edge-has-no-degree-ten-completion-proof.md
distinct_from:
  atlas-forward-collision-has-faithful-a10-quotient: that constructs the minimal degree-ten carrier; this exhausts every possible extra involution on the same ten points for the next core edge.
  atlas-first-post-a10-core-edge-is-a-centralizer-double-coset: that allows arbitrary regular-amplified alignments in degree 1814400; this rules out only internal degree-ten completions, even in S10 rather than A10.
---

In the explicit degree-ten A10 carrier, let `F=<r,z,c>`, let `t` be the
second-chart order-three collision generator, and let `u` denote the missing
first-chart involution in the next core pair.  There is no `u in S10`
satisfying

```text
u^2=1,       [u,z]=[u,c]=1,       u r u=r^-1,
(u t)^3=1
```

or the inverse-oriented condition `(u t^-1)^3=1`.

The exact MSI audit enumerates all `10!` permutations.  Hence the first new
core edge cannot be added inside the degree-ten carrier, even by passing from
`A10` to `S10`.  A completion must use a genuine larger permutation overgroup
or the regular 288-block triangle construction.
