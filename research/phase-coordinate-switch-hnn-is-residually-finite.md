---
rg: 2
id: phase-coordinate-switch-hnn-is-residually-finite
kind: claim
title: Switching between two full phase coordinates by HNN is residually finite
artifacts:
  - research/artifacts/signed-hecke-common-type-normalization-2026-08-20.md
distinct_from:
  symmetric-free-support-hnn-remains-hyperlinear: that identifies two full commuting factors with no auxiliary phase data and proves hyperlinearity from a path-RAAG kernel; this permits arbitrary auxiliary phase homomorphisms and proves the stronger residual-finiteness conclusion.
  partial-phase-graph-hnn-is-residually-finite: that keeps one faithful free coordinate fixed and permits graph data on a proper subgroup; this moves the faithful coordinate between two different full direct factors.
  finite-free-phase-product-embedding-has-an-injective-coordinate: that finds some faithful coordinate in each finite-layer embedding; this fences the case where the two faithful coordinates are full copies of the same abstract support group.
---

Let `A` and `P` be finitely generated residually finite groups, let `A_0,A_1`
be two copies of `A`, and let `Theta_0,Theta_1:A -> P` be arbitrary
homomorphisms.  In

```text
B=A_0 times A_1 times P
```

put

```text
G_0={(a,1,Theta_0(a)):a in A},
G_1={(1,a,Theta_1(a)):a in A}.                          (PCS1)
```

Then

```text
E=<B,t | t(a,1,Theta_0(a))t^(-1)
             =(1,a,Theta_1(a)), a in A>                (PCS2)
```

is residually finite.

Thus moving the faithful signed-Hecke support from one whole fresh free-phase
factor to another does not evade the finite-quotient fence, even after
arbitrary old and new commuting phase words are attached.  The conclusion
also applies to finite direct products of free support factors by taking their
product as `A`.
