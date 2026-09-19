---
rg: 2
id: fpbs-soft-collapse-kills-stationary-set-gap-proofs
kind: claim
title: Over invariant sparse spines the soft collapse family meets every independent walk range and every independent aperiodic subrelation class infinitely just above p_c, so no soft argument certifies finite visits along any stationary set
distinct_from:
  fpbs-soft-collapse-kills-relative-gap-proofs: that kills soft proofs of relative gaps along deterministic subgroups; this kills soft proofs of finite visits along every random set independent of the percolation, including walk ranges of any step law and classes of hyperfinite and other non-subgroup subrelations.
  fpbs-soft-collapse-iff-invariant-sparse-spines: that kills soft proofs of p_c < p_u itself; this kills them for the intermediate hole fpbs-stationary-set-relative-gap-universal, whose passage to p_c < p_u uses no Bernoulli property.
artifacts:
  - research/artifacts/fpbs/docs/stationary-set-recurrence-2026-09-19.md
---

**ESTABLISHED (class-killing obstruction).** Theorem 5 and Corollary 6 of
`research/artifacts/fpbs/docs/stationary-set-recurrence-2026-09-19.md`.

Let `G` carry a soft collapse family `(omega_t)`, meaning (S1)--(S4) of
`fpbs-soft-collapse-iff-invariant-sparse-spines`. Let `A` be any independent
stationary set in the sense of `fpbs-stationary-set-recurrence-separates`:
a walk range of any step law, or a class of any aperiodic subrelation of a
free pmp action. Then for every `t > p_c(G)`,

```text
P( V(omega_t) = infinity ) >= theta(t) > 0.
```

**Corollary (obstruction).** On every Cayley graph with invariant sparse spines
(for example `F_2 x Z`, `T_3 x Z` and `F_2 x F_2`, where the gap is true in the
second case), no argument using only (a) Bernoulli facts at `p <= p_c` and
(b) properties (S1)--(S4) proves `fpbs-stationary-set-relative-gap-universal`.
The same holds for any member of it: finite visits of any walk, or along any
subrelation class, at some `p > p_c`.

* **Invariant:** invariant sparse spines, as in the subgroup case.
* **Failing step:** the passage from data at `p_c` to `V < infinity` at
  `p_c + delta`.

The proof is one line: (S4) gives a unique infinite cluster, and
`fpbs-stationary-set-recurrence-separates` makes it meet `A` infinitely often.
So freeing the random set from being a subgroup does not buy a soft proof.
Any proof of the hole must use a supercritical Bernoulli property: BK or Russo
above `p_c`, deletion tolerance, Harris--FKG, or the product structure.
