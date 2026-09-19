---
rg: 2
id: spherical-single-relation-near-perfect-packing
kind: claim
title: Every one spherical multiplication relation admits a near-perfect exact partial Schreier packing
distinct_from:
  hypergraph-near-perfect-schreier-packing: This solves one multiplication relation at a time by one 3-partite matching; the global node must choose the same partial generator maps simultaneously across every tested relation.
artifacts:
  - research/spherical-near-perfect-local-package.md
---

Fix one tested relation `gh=k`.  Let the radius-one candidate graphs be

```text
A_w(i,j)=1[||U_w x_i-x_j||<=1]
```

on an iid uniform spherical cloud.  Along any sequence of unitary tables with

```text
||U_g U_h-U_k||_2 -> 0,
```

one can choose the cloud sizes so that, with probability tending to one, there
are partial bijections `sigma_h,sigma_g,sigma_k` whose domains and ranges omit
only `o(N)` vertices, every selected graph edge is a radius-one candidate,
and

```text
sigma_g(sigma_h(i)) = sigma_k(i)
```

for every root in the common domain.

Thus the near-perfect packing problem is already solved for each relation in
isolation.  The unresolved content of `hypergraph-near-perfect-schreier-packing`
is **simultaneous compatibility**: when a generator occurs in several tested
relations, all of those one-relation matchings must induce the same partial
bijection for that generator.
