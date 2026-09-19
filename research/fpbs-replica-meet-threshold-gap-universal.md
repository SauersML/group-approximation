---
rg: 2
id: fpbs-replica-meet-threshold-gap-universal
kind: claim
title: On every nonamenable Cayley graph some p above p_c and some finite k make the common intersection of k independent clusters of the origin almost surely finite
distinct_from:
  fpbs-two-point-some-lq-above-pc-universal: that is [Q_fin], finite MEAN of the k-fold intersection at one p > p_c; this asks only for a.s. finiteness, which [Q_fin] implies and which tolerates infinite means for every k (q_0 = infinity).
  fpbs-two-point-lq-threshold-gap-universal: that is [Q], every l^q with q > 2 just above p_c, a quantitative statement that implies this one with k = 3; this is qualitative and says nothing about l^q.
  fpbs-worst-pair-connectivity-rate-positive-above-pc-universal: that is (K), an exponentially rare worst pair; this is an a.s. statement about independent replicas, not a rate, and neither is known to imply the other.
artifacts:
  - research/artifacts/fpbs/docs/replica-meet-threshold-2026-09-18.md
---

**OPEN ([cap_fin]).** Let `G` be a Cayley graph of a finitely generated
nonamenable group. Then some `p > p_c` and some integer `k >= 1` satisfy

```text
P_p^(k)( |K^1(o) ∩ ... ∩ K^k(o)| = infinity ) = 0 ,
```

where `K^i(o)` is the cluster of `o` in the `i`-th of `k` independent copies
of `P_p`. Equivalently, `p_c < p_cap^(k)` in the notation of
`fpbs-replica-meet-threshold-sandwich`.

**What it gives.** `p_c < p_cap^(k) <= p_u`, which is BS (route
`fpbs-bs-via-replica-meet-threshold`).

**What gives it.**

- [Q_fin] (route `fpbs-replica-meet-gap-from-some-lq`), hence also [Q],
  `p_c < p_2` and `p_c < p_(2->2)`.
- Trees: take `k = 2` and any `p` in `(p_c, (d-1)^(-1/2)]`.

**Why it is new.** It is the first hole on this chain that is qualitative
(a.s.) rather than a moment bound. By item 1 of the sandwich, `tau` alone
fixes only the means `Z_k`. A proof may use a.s. tools such as mass transport,
indistinguishability and insertion tolerance.

**Where it is stuck.**

- The a.s.-finite set contains `[0, p_c]`, by BLPS through
  `fpbs-critical-no-infinite-cluster`. Openness at `p_c` is again the whole
  content.
- On trees the meet is a Bernoulli(`p^k`) cluster. In general, the multi-path
  set `M_k \ K_(∧omega)` must be controlled at `p_c + 0`.
- Pointwise decay of `tau` cannot suffice: see the toy in Section 4 of the
  artifact.
- The set `{p_c < p_cap^(k)}` is not lower semicontinuous along
  `F_2/F_2^(m) -> F_2`. See Section 3 of the artifact.

## Attempts

1. **Calibration against the companion question [cap_inf] (2026-09-19,
   swarm-0917 w14-bs-follow).** The hope was that `p_cap^(k) ↑ p_u`. Together
   with BS, that would make this hole equivalent to BS. It is false.
   - On `G = Cay(Z^2 * Z/2, {a^±1, b^±1, t})`, every `p_cap^(k) <= p_c(Z^2)`,
     and `p_c(Z^2) <= 9/10` by an exact Peierls count. Yet `p_u(G) = 1`
     (`fpbs-replica-meet-cap-inf-fails-free-products`, with artifact
     `research/artifacts/fpbs/docs/replica-meet-cap-inf-counterexample-2026-09-19.md`).
   - So any proof of this hole must find `p_c < p_cap^(k)` inside the relative
     window of a thick amenable piece, not the nonuniqueness window.
   - The hole itself stays **OPEN**, including on `Z^2 * Z/2`, where it needs
     `p_c(G) < p_cap^(k) <= p_c(Z^2)`.
   - [cap_inf] on one-ended graphs also stays open.
* **Push `p_cap^(k)` up to `p_u` ([cap_inf]), w14-bs-follow, 2026-09-19.**
  **Where it dies:** the meet thresholds are capped by every amenable
  subgroup. Lemma A of
  `research/artifacts/fpbs/docs/replica-meet-amenable-caps-2026-09-19.md`
  (node `fpbs-meet-threshold-capped-by-amenable-relative-threshold`) gives
  `p_cap^(k) <= p_c(H;G)` for every infinite amenable `H` and every `k`.
  - On `Z^3 * Z/2`, `lim_k p_cap^(k) = p_c(Z^3) <= 1/2 < 1 = p_u`
    (`fpbs-meet-thresholds-tend-to-pc-z3-below-pu-on-z3-free-z2`).
  - So [cap_inf] is false. Any route to this hole through a replica
    characterisation of nonuniqueness is dead. The named invariant is
    `c(G,S) = inf_H p_c(H;G)` over infinite amenable `H`.
* **What any proof must contain (same artifact, Corollary C).** This hole
  implies the relative gap `p_c(G) < p_c(H;G)` along *every* infinite
  amenable subgroup. That is the new OPEN node
  `fpbs-relative-gap-along-every-amenable-subgroup-universal`. It contains the
  wq-normal hole `fpbs-amenable-wq-normal-relative-subcriticality`.
  - A proof of this hole therefore solves the relative-gap lane along every
    cyclic subgroup at once.
  - It must separate `p_c(G)` from the subgroup thresholds, not from `p_u`.
* **Calibration, not a counterexample.** This hole *holds* on `Z^3 * Z/2`.
  There `p_c(G) < p_c(Z^3)`, by the l1 Aizenman–Barsky bound on `Z^3`, and
  every large-`k` meet threshold lies in `(p_c(G), p_c(Z^3)]`. The bridge
  mechanism that proves it there is special to free products.
* **Bound the meet limit from below by `p_exp` (2026-09-19, swarm-0917
  w18c-bs-follow).** Artifact:
  `research/artifacts/fpbs/docs/replica-meet-exp-decay-threshold-2026-09-19.md`.
  - Established: `p_exp <= sup_k p_k <= p_cap^(infty) <= p_c(H;G) <= p_u`
    for every infinite amenable `H`
    (`fpbs-replica-meet-limit-sandwiched-by-exp-decay-threshold`). The key
    step is `Z_k(p) < infinity` once `k xi_p > gr`, which is sharp on trees.
  - So [cap_inf] holds, and `p_c(H;G) = p_u` for every amenable `H`,
    wherever `p_exp = p_u`. That covers one-ended planar graphs (Schonmann),
    surface groups among them, and `T x A`. The wave-14 cyclic-subgroup spark
    is answered negatively.
  - On `A * Z/2` the limit is exactly `p_exp = p_c(A)`
    (`fpbs-free-product-meet-limit-equals-exp-decay-threshold`).
  - New route `fpbs-replica-meet-gap-from-exp-decay-gap`: Hutchcroft's
    Conjecture 2.1, `p_c < p_exp`
    (`fpbs-pc-below-exp-decay-threshold-universal`), implies this hole.
  - Open conjecture `fpbs-replica-meet-limit-equals-exp-decay-threshold`:
    `p_cap^(infty) = p_exp`. If it holds, this hole is *equivalent* to
    `p_c < p_exp`.
  - **Where it stops.** Nothing here proves `p_c < p_exp` on a new class, so
    the hole stays **OPEN**.
