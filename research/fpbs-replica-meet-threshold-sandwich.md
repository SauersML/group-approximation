---
rg: 2
id: fpbs-replica-meet-threshold-sandwich
kind: claim
title: The threshold for k independent clusters of the origin to have a.s. finite common intersection lies between p_k and min(p_u, p_c^(1/k)), increases in k, and equals (d-1)^(-1/k) on trees
distinct_from:
  fpbs-lq-two-point-infinite-cluster-reduction: that computes the mean E|K^1 ∩ ... ∩ K^k| = Z_k and uses its finiteness; this studies a.s. finiteness of the same intersection, a qualitative threshold that is at least p_k and is bounded by p_u through uniqueness, which a mean statement does not see.
  fpbs-lq-threshold-power-monotonicity: that relates the l^q thresholds p_q to each other by thinning; this introduces the a.s. meet thresholds p_cap^(k) and places them between p_k and min(p_u, p_c^(1/k)).
artifacts:
  - research/artifacts/fpbs/docs/replica-meet-threshold-2026-09-18.md
---

**ESTABLISHED.** Proof in `fpbs-replica-meet-threshold-sandwich-proof`
(Section 1 of the artifact).

Let `G` be an infinite, connected, locally finite, transitive graph. Take `k`
independent Bernoulli(`p`) configurations and set
`M_k(o) = K^1(o) ∩ ... ∩ K^k(o)`. This is the class of `o` in the meet of the
`k` cluster partitions. Define

```text
p_cap^(k) = sup{ p : |M_k(o)| < infinity a.s. }.
```

1. `E|M_k(o)| = Z_k(p)`, so `p_c <= p_k <= p_cap^(k)`.
2. `p_cap^(k) <= p_c^(1/k)`, because the cluster of the edgewise minimum,
   which is Bernoulli(`p^k`), lies inside `M_k(o)`.
3. `p_cap^(k) <= p_u`.
   - Above `p_u` the unique infinite clusters meet in an invariant set that
     contains `o` with probability `theta^k`.
   - An invariant random set is a.s. infinite whenever it contains `o`.
4. `p_cap^(k)` is nondecreasing in `k`, and
   `p_cap^(infty) = sup_k p_cap^(k) <= p_u`.
5. On `T_d`, `M_k(o)` is the Bernoulli(`p^k`) cluster. So
   `p_cap^(k) = p_k = (d-1)^(-1/k)`, and `p_cap^(infty) = 1 = p_u`.
   In particular `p_c < p_cap^(2) < p_u`.

**Consequences.**

- `p_c < p_2` implies `p_c < p_cap^(2)`.
- [Q_fin] implies `p_c < p_cap^(k)` for some `k`, and [Q] implies it with
  `k = 3`.
- `p_c < p_cap^(k)` for some `k` implies `p_c < p_u`.
- So the hole `fpbs-replica-meet-threshold-gap-universal` sits strictly
  between [Q_fin] and BS in the chain of implications.
