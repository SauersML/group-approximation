---
rg: 2
id: stw22-chern-l2-small-unbounded-commutator-width
kind: claim
title: Chern obstructions give trace-zero contractions that are uniformly 2-small but have unbounded self-commutator width
artifacts:
  - research/artifacts/stw22-chern-commutator-width-audit-2026-08-31.md
distinct_from:
  stw22-fixed-replication-blocks-infinite-dimensional-selection: that obstruction concerns homotopy of weighted-copy selection fibres; the present theorem is an operator-norm obstruction to bounded self-commutator decompositions and is strong enough to survive a corona quotient.
---

For every integer `s>=1`, let

```text
X_s = CP^(s^2),
L_s -> X_s the tautological complex line bundle,
E_s = 1 + L_s^(+s),
D_s = Gamma(End(E_s)).
```

Let `p_s` be the bundle projection onto the trivial line and `q_s` the
projection onto the first copy of `L_s`, and put `h_s=p_s-q_s`. Then

```text
||h_s|| = 1,
 tau(h_s)=0                    for every tau in T(D_s),
||h_s||_(2,T(D_s)) = sqrt(2/(s+1)) -> 0.                 (CW-1)
```

Nevertheless, if `ell<=s`, then for every `z_1,...,z_ell in D_s`,

```text
|| h_s - sum_(j=1)^ell (z_j^* z_j - z_j z_j^*) || >= 1. (CW-2)
```

Thus the same sequence is asymptotically invisible to every normalized
fibre trace while its distance from sums of any fixed finite number of
self-commutators stays uniformly one on a tail.
