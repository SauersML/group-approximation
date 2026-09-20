---
rg: 2
id: fpbs-pc-below-exp-decay-threshold-universal
kind: claim
title: On every nonamenable Cayley graph the two-point function still decays exponentially and uniformly in distance at some p above p_c (Hutchcroft's Conjecture 2.1)
distinct_from:
  fpbs-worst-pair-connectivity-rate-positive-above-pc-universal: that (K) asks for one exponentially rare pair per ball; this asks for uniform decay sup_{d(u,v)>=n} tau_p(u,v) <= e^{-cn}, which implies (K)
  fpbs-two-point-some-lq-above-pc-universal: that is [Q_fin], one finite k-th moment sum of tau_p above p_c; this is uniform exponential decay, which implies [Q_fin] with the full meet (k > gr/xi_p)
  fpbs-benjamini-schramm-universal: that is p_c < p_u; this is p_c < p_exp, which implies it since p_exp <= p_u, and is strictly stronger wherever p_exp < p_u
artifacts:
  - research/artifacts/fpbs/docs/replica-meet-exp-decay-threshold-2026-09-19.md
---

**OPEN.** This is Hutchcroft's Conjecture 2.1 (EJP 2020, arXiv:1904.05804),
recorded in `fpbs-exp-decay-threshold-facts`. Let `G` be a Cayley graph of a
finitely generated nonamenable group. Then some `p > p_c(G)` has

```text
xi_p = - limsup_n (1/n) log sup{ tau_p(u,v) : d(u,v) >= n }  >  0 ,
```

that is, `p_c(G) < p_exp(G)`.

**What it gives.** The replica meet gap `fpbs-replica-meet-threshold-gap-universal`
(route `fpbs-replica-meet-gap-from-exp-decay-gap`). Through it you get the
relative gap along every infinite amenable subgroup, and BS.

**Where it is known.**

- `p_c < p_(2->2)` holds on several classes, for example hyperbolic,
  nonunimodular and free-product graphs.
- One-ended planar graphs: Schonmann gives `p_exp = p_u`, and
  Benjamini–Schramm give `p_c < p_u`.
- Free products `A * Z/2`: `p_exp = p_c(A)`
  (`fpbs-free-product-meet-limit-equals-exp-decay-threshold`), and
  `p_c(G) < p_c(A)`.

**Why it is not just BS.** It implies BS. It is equivalent to BS wherever
`p_exp = p_u`, which includes the classes in item 5 of
`fpbs-replica-meet-limit-sandwiched-by-exp-decay-threshold`. On free products
it is strictly stronger.

## Attempts

1. **Through the replica meet (2026-09-19, swarm-0917 w18c-bs-follow).** The
   hope was to get `p_c < p_exp` back from an a.s. finite meet.
   - **Where it dies.** `p_cap^(infty) >= p_exp` is established, but the
     reverse inequality is only conjectured
     (`fpbs-replica-meet-limit-equals-exp-decay-threshold`).
   - So [cap_fin] gives `p_c < p_exp` only on graphs where that conjecture is
     known. Those are the equality classes, where `p_c < p_exp` was already
     known.
2. **Through `p_(2->2)`.** `p_c < p_(2->2)` implies this node, by Theorem 2.2
   in `fpbs-exp-decay-threshold-facts`.
   - **Where it dies.** `p_c < p_(2->2)` is itself open in general.
