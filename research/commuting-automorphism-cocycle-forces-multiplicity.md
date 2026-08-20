---
rg: 2
id: commuting-automorphism-cocycle-forces-multiplicity
kind: claim
title: A commuting automorphism square turns projective packet holonomy into exact multiplicity divisibility
artifacts:
  - research/artifacts/schur-clifford-predicate-rank-compiler-2026-08-19.md
distinct_from:
  predicate-rank-gate-doubles-restriction-multiplicity: that obtains a factor-two restriction multiplicity from commutation-form rank; this obtains an external multiplicity divisibility law from the projective cocycle of two commuting packet automorphisms.
  fixed-holonomy-on-overlap-pays-relator-energy: that charges a fixed nontrivial finite-factor holonomy on a positive-density matrix corner; this first proves the exact representation-theoretic divisibility law and records why it has no ambient-normalized gap at fixed cocycle order.
---

Let `B` be a finite group, let `alpha,beta in Aut(B)` commute, and let `T` be
an irreducible `B`-module fixed up to equivalence by both automorphisms.  Choose
unitary implementers `U_alpha,U_beta` on `T`.  Their commutator is scalar; write

```text
U_alpha U_beta = zeta U_beta U_alpha,
```

and suppose `zeta` has order `r`.

In any representation of

```text
< B,u,v |
    u b u^(-1)=alpha(b),
    v b v^(-1)=beta(b),
    [u,v]=1 >                                           (CAC1)
```

whose `T`-isotypic subspace is invariant under `u,v` and is
`T tensor C^m`, one has

```text
r divides m.                                             (CAC2)
```

In particular a cocycle `zeta=-1` forces even external multiplicity.  This is
an exact finite-presentation holonomy transducer.  At fixed `r` it is **not**
a normalized-HS obstruction: a nondivisible multiplicity can be repaired by
changing fewer than `r` copies, a vanishing fraction as `m` grows.  A
hyperlinearity obstruction must therefore force a positive density of
independent cocycle squares or activate an order `r` exceeding the current
model capacity.

