---
rg: 2
id: fpbs-uniqueness-pivotals-are-dangling-bridges
kind: claim
title: Under uniqueness every pivotal edge between two points of the infinite cluster cuts off a finite piece
artifacts:
  - research/artifacts/fpbs/docs/relative-susceptibility-reduction.md
---

**ESTABLISHED.** Let `G` be connected, locally finite and quasi-transitive,
and let `p in (0,1)` be a parameter with a unique infinite cluster `C` almost
surely. Then almost surely every open edge whose removal disconnects `C` leaves
exactly one infinite side. Consequently, for `o, x in C`, every open edge
pivotal for `{o <-> x}` is a bridge of `C` whose finite side contains `o` or
`x`, and

```text
N_(o <-> x) <= N_o + N_x,
```

where `N_v` counts the bridges of `C` having `v` on their finite side. The bound
does not depend on the distance between `o` and `x`.

Supporting structure for attempts on the collapse scenario: a hypothetical
`p_c = p_u` would need exponentially many pivotal edges, and under uniqueness
those can only be dangling bridges near the endpoints. The lemma alone does not
exclude collapse; see the attempts on
`fpbs-amenable-wq-normal-relative-subcriticality`.

DERIVATION
fpbs-uniqueness-pivotals-are-dangling-bridges-proof
