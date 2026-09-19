---
rg: 2
id: fpbs-replica-meet-limit-equals-exp-decay-threshold
kind: claim
title: On every nonamenable Cayley graph the limit of the replica meet thresholds equals the exponential connectivity decay threshold
distinct_from:
  fpbs-replica-meet-limit-sandwiched-by-exp-decay-threshold: that proves p_exp <= p_cap^(infty) everywhere, with equality where p_exp = p_u; this conjectures equality everywhere, including where p_exp < p_u
  fpbs-free-product-meet-limit-equals-exp-decay-threshold: that proves the equality on A * Z/2; this asks for it on every Cayley graph
  fpbs-pc-below-exp-decay-threshold-universal: that is p_c < p_exp; this is the identity p_cap^(infty) = p_exp, which would make [cap_fin] equivalent to it
artifacts:
  - research/artifacts/fpbs/docs/replica-meet-exp-decay-threshold-2026-09-19.md
---

**OPEN (conjecture).** Let `G` be a Cayley graph of a finitely generated
nonamenable group. Then

```text
sup_k p_cap^(k)(G) = p_exp(G).
```

The notation is that of `fpbs-replica-meet-threshold-sandwich` and
`fpbs-exp-decay-threshold-facts`.

**Evidence.** It holds on every class where `p_cap^(infty)` is computed:

- trees, one-ended planar graphs, `T x A` and `LL(T)`, by item 5 of
  `fpbs-replica-meet-limit-sandwiched-by-exp-decay-threshold`;
- `A * Z/2`, by `fpbs-free-product-meet-limit-equals-exp-decay-threshold`.

The inequality `>=` is established everywhere.

**What it gives.** Suppose it holds on `G`. If
`p_c < p_cap^(k)` for some `k`, then `p_c < p_cap^(infty) = p_exp`. The
converse is `fpbs-replica-meet-gap-from-exp-decay-gap`. So
`fpbs-replica-meet-threshold-gap-universal` on `G` would be *equivalent* to
Hutchcroft's Conjecture 2.1 (`fpbs-pc-below-exp-decay-threshold-universal`)
on `G`.

**How to refute it.** Find `G` and `p` with `p_exp < p` and `|M_k(o)| < infinity` a.s. for some
`k`. That needs a two-point function that fails uniform exponential decay at
`p`, while `k` independent clusters still meet in a finite set a.s.
A candidate would be a graph where `tau_p` fails to decay only along a sparse,
non-amenable-subgroup family of directions.

## Attempts

1. **Upper bound from a meet (2026-09-19, swarm-0917 w18c-bs-follow).** Fix
   `p > p_exp`. The aim was to show `|M_k(o)| = infinity` with positive
   probability for every `k`.
   - On free products this works: a positive-density amenable piece supplies
     an invariant infinite intersection (Lemma A).
   - **Where it dies.** In general, failure of uniform exponential decay
     gives only a sequence of pairs `(u_n, v_n)` with `tau_p(u_n, v_n)` not
     exponentially small. It gives no invariant set carrying all `k`
     replicas. The step from "two-point decay fails" to "infinite meet"
     needs an invariant witness, and none is known.
