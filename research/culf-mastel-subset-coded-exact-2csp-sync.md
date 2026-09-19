---
rg: 2
id: culf-mastel-subset-coded-exact-2csp-sync
kind: claim
title: Proposition 8.9 admits an exact subset-coded defect-preserving strengthening
artifacts:
  - research/artifacts/culf-mastel-sync-normal-form-2026-08-23.md
distinct_from:
  culf-mastel-exact-projection-synchronization: that identifies the source c-v incidence energy; this gives a family of homogeneous 2-CSP encodings with the same defect.
  culf-mastel-oracular-2csp-perfect-gap-family: that uses the published all-2-CSP target; this restricts every edge to one explicit two-block relation and preserves defect in both directions.
---

**ESTABLISHED.**  Fix `k>=3` and a nonempty proper subset
`B subset Z_k`.  For every `j in Z_k`, define

```text
D_(j,B)
 = ({j} x B) union ((Z_k\{j}) x (Z_k\B))
 = {(a,b): [a=j] iff [b in B]}.                         (SCS1)
```

Given a positive exactly-one-`k` constraint-variable instance, introduce a
`k`-outcome variable `y_i` for each context.  For the incidence in position
`j`, use one edge carrying `D_(j,B)`.  If `Q_(i,j)=Pi_j(y_i)` and

```text
P_B(x)=sum_(b in B) Pi_b(x),                            (SCS2)
```

then, for arbitrary noncommuting endpoint PVMs, the complete losing energy
of that edge is

```text
sum_((a,b) notin D_(j,B)) ||Pi_a(y_i)Pi_b(x)||_2^2
 = tau(Q_(i,j)(1-P_B(x))) + tau((1-Q_(i,j))P_B(x))
 = ||Q_(i,j)-P_B(x)||_2^2.                              (SCS3)
```

The correspondence preserves defect in both directions.  From source to
target, choose `b_1 in B`, `b_0 notin B`, and put

```text
Pi_(b_1)(x)=P_x,    Pi_(b_0)(x)=1-P_x,
Pi_b(x)=0           otherwise.                         (SCS4)
```

From target to source, retain the context PVM and set

```text
P_x=P_B(x).                                             (SCS5)
```

Both operations stay in the same tracial algebra.  They preserve exactness,
finite dimensionality, Connes embeddability, and every weighted defect.

Culf--Mastel Proposition 8.9 is the special case `B=Z_k\{0}`.  The singleton
choice `B={0}` instead compares one atom with one atom, removing the coarse
`(k-1)`-atom marginal from the target language.
