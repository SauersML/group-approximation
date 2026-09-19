---
rg: 2
id: fpbs-replica-meet-cap-inf-fails-free-products
kind: claim
title: On A * Z/2 with A amenable and p_c(A) < 1 every replica meet threshold is at most p_c(A) while p_u = 1, so meet thresholds do not converge to p_u
distinct_from:
  fpbs-replica-meet-threshold-sandwich: that proves p_cap^(k) <= min(p_u, p_c^(1/k)) and equality p_cap^(infty) = p_u on trees; this shows the sandwich's upper bound p_u is not approached, by a bound uniform in k from an amenable free factor
  fpbs-replica-meet-threshold-gap-universal: that is [cap_fin], p_c < p_cap^(k) for some k; this refutes the companion question [cap_inf] (p_cap^(infty) = p_u), which the gap hole does not assert, and leaves [cap_fin] open
  fpbs-amenable-wq-normal-pu-is-relative-pc: that shows p_u = p_c(H;G) for amenable wq-normal H, which makes an amenable-subgroup bound on p_cap harmless; here H is a free factor, not wq-normal, and p_c(H;G) < p_u
artifacts:
  - research/artifacts/fpbs/docs/replica-meet-cap-inf-counterexample-2026-09-19.md
  - experiments/replica-meet-free-product-2026-09-17/peierls_bound.py
  - experiments/replica-meet-free-product-2026-09-17/peierls_bound.out
---

**ESTABLISHED.** Proof in `fpbs-replica-meet-cap-inf-fails-free-products-proof`
(Section 2 of the artifact).

Let `A` be an infinite, finitely generated, amenable group with finite
symmetric generating set `S_A`. Let `L = Cay(A, S_A)` and assume
`p_c(L) < 1`. Let `G = Cay(A * Z/2, S_A ∪ {t})`. Then:

1. `A * Z/2` is nonamenable;
2. `p_c(G) <= p_c(L) < 1 = p_u(G)`, because every `t`-edge is a bridge whose
   two sides are swapped by left multiplication by `t`;
3. `p_cap^(k)(G) <= p_c(L)` for every `k >= 1`, where `p_cap^(k)` is the
   a.s.-finite replica meet threshold of `fpbs-replica-meet-threshold-sandwich`.

Hence `sup_k p_k(G) <= p_cap^(infty)(G) <= p_c(L) < 1 = p_u(G)`.

**Instance.** For `G = Cay(Z^2 * Z/2, {a^±1, b^±1, t})`, a Peierls count with
exact arithmetic (script in the artifacts) gives `p_c(Z^2) <= 9/10`, so
`p_cap^(infty)(G) <= 9/10 < 1 = p_u(G)`.

**What it refutes.** Section 4 of
`research/artifacts/fpbs/docs/replica-meet-threshold-2026-09-18.md` asks:

> **Question [cap_inf].** Is `p_cap^(infty) = p_u` on every nonamenable Cayley
> graph? It holds on `T_d` (item 5).

The answer is no. It also rules out one route to BS ⇒ [cap_fin]. That route
runs `p_cap^(k) ↑ p_u > p_c`. The claim does not bear on BS itself, which holds
on `G`.

**Mechanism.** In each replica, the plane through `o` has a unique infinite
cluster by `fpbs-hp-relative-burton-keane`. The k-fold intersection of these
plane clusters is an invariant random subset of `A`. By Lemma 1.1 of the
sandwich it is infinite whenever it contains `o`, and it lies inside `M_k(o)`.

**Open.** [cap_inf] on one-ended nonamenable Cayley graphs. [cap_fin] on
`Z^2 * Z/2`, which needs `p_c(G) < p_cap^(k) <= p_c(Z^2)`.

## Attempts

1. **Bridge swap plus the meet of plane clusters (2026-09-19,
   swarm-0917 w14-bs-follow).** Complete proof in the artifact, Sections 2–3.
   It imports `fpbs-cluster-count-trichotomy` and `fpbs-hp-relative-burton-keane`,
   and uses Lemma 1.1 of `fpbs-replica-meet-threshold-sandwich`, which the
   artifact restates and reproves. Nothing is left for referee.
