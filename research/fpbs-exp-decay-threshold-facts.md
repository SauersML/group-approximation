---
rg: 2
id: fpbs-exp-decay-threshold-facts
kind: claim
title: The exponential connectivity decay threshold p_exp lies between p_c and p_u, dominates p_(2->2), and equals p_u on one-ended planar nonamenable graphs
distinct_from:
  fpbs-hutchcroft-pan-tree-times-amenable-l2-threshold-is-pu: that imports p_(2->2) = p_u on T x A and LL(T) from arXiv:2412.15895; this imports the definition of p_exp and its basic comparisons (p_c <= p_exp <= p_u, p_(2->2) <= p_exp, Schonmann's planar equality) from Hutchcroft arXiv:1904.05804
  fpbs-worst-pair-connectivity-rate-positive-above-pc-universal: that is the open kernel "one exponentially rare pair per ball above p_c"; this imports facts about the stronger uniform decay sup_{d(u,v)>=n} tau_p(u,v) <= e^{-cn}
artifacts:
  - research/artifacts/fpbs/docs/replica-meet-exp-decay-threshold-2026-09-19.md
---

**ESTABLISHED (imported).** Proof route: `fpbs-exp-decay-threshold-facts-cite`.

**Definition.** For a connected, locally finite graph `G`, let

```text
xi_p  = - limsup_n (1/n) log sup{ tau_p(u,v) : d(u,v) >= n },
p_exp = sup{ p in [0,1] : xi_p > 0 }.
```

**Imported facts.** Let `G` be connected, locally finite and quasi-transitive.

1. `p_exp(G) <= p_u(G)`.
2. `p_c(G) <= p_exp(G)`.
3. `p_(2->2)(G) <= p_exp(G)` (Theorem 2.2; this needs only connected and
   locally finite).
4. `p_exp = p_u` for transitive, one-ended, nonamenable, planar graphs
   (Schonmann, Comm. Math. Phys. 225 (2002)). This is imported through
   Hutchcroft's survey paragraph, a secondary source; the primary paper was not
   re-read.

**Recorded, not imported as a claim.**

- Item 1 is strict on `Z^2 * (Z/2Z)` and saturated on trees (stated in the
  same source).
- Hutchcroft's Conjecture 2.1: `p_c < p_exp` for every connected, locally
  finite, quasi-transitive, nonamenable graph. It is open. Here it is
  `fpbs-pc-below-exp-decay-threshold-universal`.
