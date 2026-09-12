---
rg: 2
id: two-generator-frattini-universal-containers
kind: claim
title: Fixed two-generator finitely presented groups are Frattini-universal
distinct_from:
  whitehead-universal-finitely-presented-container: that records Whitehead injectivity for all recursively presented inputs; this records conjugacy reflection for the same fixed all-group host.
  two-generator-fp-torsion-free-universal-whitehead-container: that records connective Whitehead injectivity in the torsion-free lane; this records conjugacy reflection for the same fixed torsion-free host.
  whitehead-injective-torsion-order-preserving-higman-embedding: that chooses a new host after one finitely generated recursive input; this chooses each host before every input in its lane.
---

An embedding `i:K->H` is **Frattini** if

```text
i(x) is conjugate to i(y) in H
  =>
x is conjugate to y in K.
```

There are fixed two-generator finitely presented groups `U` and `E` with
the following properties.

1. Every countably generated recursively presented group admits a Frattini
   embedding into `U`, and

   ```text
   Tord(U)={2,3,4,...}.
   ```

2. `E` is torsion-free, and every countably generated recursively
   presented torsion-free group admits a Frattini embedding into `E`.

The choices can be made to be exactly the hosts in
[[whitehead-universal-finitely-presented-container]] and
[[two-generator-fp-torsion-free-universal-whitehead-container]],
respectively. Thus their previously recorded Whitehead-injectivity is
retained. Both hosts can also be chosen nonsofic and non-MF.

**ESTABLISHED 2026-08-31** by
[[two-generator-frattini-universal-containers-proof]].
