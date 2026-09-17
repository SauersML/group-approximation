---
rg: 2
id: cluster-entropy-functionals-vanish-on-one-ended-bernoulli
kind: claim
title: Over a one-ended group every splitting-monotone cluster entropy functional certifies at most zero on every Bernoulli shift
distinct_from:
  bowen-f-invariant-is-a-measure-conjugacy-invariant: that is the positive theorem for free groups, where the tree has no fat digon; this is the obstruction for every one-ended group and every choice of windows and weights.
  window-entropy-deficits-are-not-isomorphism-invariant: that shows per-site window entropy depends on the generating partition over nonamenable groups; this kills every finite linear combination of window entropies that is monotone under splittings, amenable or not, and bounds its certified value on Bernoulli shifts by zero.
  weak-invariants-give-no-bernoulli-rokhlin-lower-bound: that kills weak-equivalence invariants; cluster functionals are computed from partitions and are not weak-equivalence invariants, so this is a separate class.
  cluster-entropy-certificates-fail-on-kazhdan-groups: that is the specialization to infinite property (T) groups, obtained through Stallings and Watatani.
artifacts:
  - research/artifacts/cluster-entropy-functionals-one-ended-obstruction-2026-09-17.md
  - experiments/cluster-entropy-functionals-2026-09-17/check_cluster_valuation.py
---

Let `G` be a finitely generated one-ended group with a finite symmetric generating set `S`,
and let `B_n` be the word-metric balls. A **cluster functional** is a finite family of finite
windows `W ⊆ G` with real weights `c_W`,

    F(Q) = sum_W c_W H( join_{w in W} w^-1 Q ),

evaluated on finite partitions of p.m.p. `G`-spaces. Suppose `F` is splitting-monotone on
Bernoulli coordinate partitions: `F(beta v t^-1 gamma) <= F(beta)` whenever `t in S`, `beta` is
a coordinate partition `Q_D` and `gamma = Q_{{d}}` for some `d in D`. Then, for every Bernoulli
shift over `G` (any base) and every connected finite `D` containing a suitable finite set
`B_1 u B_2` (up to translation),

    F(Q_D) <= 0,  and in particular  lim sup_n F(Q_{B_n}) <= 0.

So no such functional certifies `h^Rok >= log|A|` along the route `log|A| <= inf_n F(P^n) <=
F(P) <= H(P)` of Bowen's f-invariant, on any one-ended group.

**The invariant and the step where every member dies.**

- The invariant is the valuation `psi(B) = sum_W c_W |B W|`, with `F(Q_B) = H(p) psi(B)`.
- It satisfies exact inclusion–exclusion on pieces that are separated beyond the radius
  `max |w' w^-1|`.
- An `R`-fat digon is two connected sets meeting in two far-apart connected pieces, with their
  remainders far apart.
- Monotonicity gives `psi(B_i) <= psi(piece_i)`, and inclusion–exclusion then gives
  `psi(B_1 u B_2) <= 0`.
- A fat digon exists on every one-ended group: take a bi-infinite geodesic and a detour outside
  a large ball.

**ESTABLISHED 2026-09-17** by [[cluster-entropy-functionals-vanish-on-one-ended-bernoulli-proof]].
