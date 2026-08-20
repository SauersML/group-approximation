---
rg: 2
id: pure-abelian-ascending-hnn-transport-is-amenable
kind: claim
title: A pure abelian ascending-HNN transport group is amenable and hyperlinear
distinct_from:
  ascending-hnn-action-iff-iterated-cosets: that characterizes soficity of a coset action for a general ascending HNN extension; this treats the whole group when the base is abelian.
  transport-polynomial-witnesses-replay: that checks two specific endomorphisms; this is independent of their formulas.
---

Let `A` be a discrete abelian group and let `phi:A->A` be injective.  The
ascending HNN group

```text
G=<A,t | t a t^(-1)=phi(a), a in A>                         (PAH1)
```

is isomorphic to `A_infinity semidirect Z`, where `A_infinity` is the direct
limit of the chain under `phi`.  Hence `G` is metabelian, amenable, and
hyperlinear.

Consequently a stable-letter construction with no genuinely nonabelian or
nonamenable additional structure cannot be a non-hyperlinear group.  This is
the rigorous scoped replacement for the stronger unsupported assertion that
Pontryagin duality alone supplies finite microstates for every abelian-core
construction with arbitrary extra controllers.

