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
