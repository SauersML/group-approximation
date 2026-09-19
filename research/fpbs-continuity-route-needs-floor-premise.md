---
rg: 2
id: fpbs-continuity-route-needs-floor-premise
kind: claim
title: The requirements of the weighted-surface continuity route hold on Z^2, so the route needs a floor premise equivalent to its conclusion
invalidates:
  - fpbs-dead-weighted-surface-continuity-l2
distinct_from:
  fpbs-weighted-surface-continuity-reduces-to-uniform-floor: that also invalidates the dead route, but it is established only by a route with the same two requirements as the dead route, and its every-path form is false; if it is ever refuted the dead route becomes live. This invalidator has a direct proof and does not depend on either requirement.
  fpbs-uniform-floor-equivalence-restricted-to-monotone-paths: that is one requirement of the dead route; this shows that the requirement, even when proved, supplies no floor.
  fpbs-one-edge-sprinkling-l2-lipschitz: that is the other requirement; this shows that its statement holds on every locally finite graph, amenable ones included.
  fpbs-fiid-finite-clusters-do-not-imply-dyadic-summability: that invalidates a different route to the same target, the invariant-cluster route.
---

**ESTABLISHED (direct proof in `fpbs-continuity-route-needs-floor-premise-proof`).**

The route `fpbs-dead-weighted-surface-continuity-l2` asserts

```text
fpbs-one-edge-sprinkling-l2-lipschitz  AND  fpbs-uniform-floor-equivalence-restricted-to-monotone-paths
    ==>  fpbs-critical-dyadic-projection-estimate.
```

Its own body calls it dead. The only obstruction that currently invalidates it
is `fpbs-weighted-surface-continuity-reduces-to-uniform-floor`. That obstruction
is established only through a route with exactly the same two requirements.
Its every-path statement is false by item 1 of
`fpbs-uniform-floor-equivalence-restricted-to-monotone-paths`.

**Why this matters.** A scratch copy of the graph was built with both
requirements forced true and a refuter of the reduction claim added. There,
`cairn why` derives `fpbs-benjamini-schramm-universal` ESTABLISHED via
`fpbs-universal-dyadic-route`. The only warning is one contradiction line among
the pre-existing lint errors. This claim removes that failure mode.

**Claim.** Write `phi(q) = 1/||T_q||_{2->2}`, with `1/infinity = 0`.

1. **Every statement in both requirements holds on `Z^2`.**
   * All four items of `fpbs-one-edge-sprinkling-l2-lipschitz` are stated for an
     arbitrary locally finite graph, or an arbitrary Cayley graph, and hold on
     `Z^2` whenever they hold at all.
   * Item 1 of `fpbs-uniform-floor-equivalence-restricted-to-monotone-paths`
     holds on every finitely generated group, and has a three-line proof given
     here.
   * Item 2 is a statement about the one group `F_2 x Z`, and it is negative:
     some certificates fail.
2. **Critical l2 fails on `Z^2`.** For `Z^2 = <a> x <t>` with `S = {a^±1, t^±1}`,
   the path `gamma(t) = t p_c(S) 1_S` from the good anchor `0` has
   `phi(gamma(1)) = 0`.
3. **The missing premise.** The open-closed argument of the dead route turns
   its requirements into critical l2 at `p_c(S) 1_S` only under the extra
   hypothesis `inf_t phi(gamma(t)) > 0`. That hypothesis is equivalent to
   critical l2 at the endpoint, by item 1 of the floor claim for monotone paths
   and trivially at `t = 1` for every path. Neither requirement asserts it for
   any nonamenable group.

So the implication asserted by the dead route is not justified. Its argument,
run verbatim, would prove critical l2 at `p_c` on `Z^2`, which is false.
