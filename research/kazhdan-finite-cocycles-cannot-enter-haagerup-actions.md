---
rg: 2
id: kazhdan-finite-cocycles-cannot-enter-haagerup-actions
kind: claim
title: Regular finite-range cocycles of infinite Kazhdan groups cannot enter Haagerup actions
distinct_from:
  haagerup-actors-cannot-host-property-t-algebraic-envelope: that excludes arbitrary embeddings of a property-T II1 factor by Popa rigidity; this needs no factoriality of the represented group algebra but treats the narrower orthogonal-normalizer ansatz through equivalence-relation Haagerup property.
  orthogonal-finite-fourier-reps-are-orbit-cocycles: that classifies the ansatz and shows support orthogonality alone does not collapse it; this adds property T of the represented group and the Haagerup property of the actor to exclude every regular-trace solution.
  non-ce-relation-is-not-treeable: that is the free-actor/treeability obstruction for the fixed non-CE relation; this works for every Haagerup actor, including the non-treeable product `F_m times F_m`, and applies directly to a quotient-group cocycle.
---

Let `Q` be an infinite countable property-`(T)` group, let a countable
Haagerup group `G` act trace-preservingly on a probability space `(X,mu)`,
and put `M=L^infinity(X) rtimes G`.  There is no representation
`a |-> V_a` of `Q` in `M` of the orthogonal finite-Fourier form `(OFC2)`
whose trace is the regular character:

```text
tau(V_a)=0                         for every a!=e.       (KFC1)
```

Equivalently, the finite partition equations `(OFC1)`--`(OFC3)` have no
solution with `mu(p_(a,e))=0` for all `a!=e`.  The conclusion allows every
finite support in `G`; it does not assume that labels lie in one subgroup or
that their two coordinates separate.

For the Mihailova candidate, choose `Q` to be the infinite property-`(T)`,
finitely presented nonsofic Fournier--Facio group and take
`G=F_m times F_m`, which is Haagerup.  Then **no** regular-trace orthogonal
finite-range orbit cocycle representing `Q` exists in its left-right
Bernoulli crossed product.  Hence the full normalizer branch isolated by
`orthogonal-finite-fourier-reps-are-orbit-cocycles` is closed.  A surviving
Fourier-mixing embedding must use nonnormalizing coefficients, such as the
Hadamard matrix cells, and therefore lies back in the full algebraic-envelope
problem rather than in a finite-valued orbit-cocycle subproblem.
