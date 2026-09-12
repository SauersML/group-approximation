---
rg: 2
id: approximate-to-asymptotic-via-central-paths
kind: claim
title: Controlled central paths upgrade approximate to asymptotic unitary equivalence
---

Let `A` be separable and unital, let `B` be unital, and let
`phi,psi:A->B` be unital homomorphisms which are approximately unitarily
equivalent.  Assume the following central path property for `phi`:

For every finite `F subset A` and `epsilon>0`, there are a finite
`G subset A` and `delta>0` such that every `w in U(B)` with

```text
max_(g in G) ||[w,phi(g)]|| < delta
```

can be joined to `1` by a norm-continuous path `v:[0,1]->U(B)` satisfying

```text
max_(f in F),s in [0,1] ||[v(s),phi(f)]|| < epsilon.
```

Then `phi` and `psi` are asymptotically unitarily equivalent.
