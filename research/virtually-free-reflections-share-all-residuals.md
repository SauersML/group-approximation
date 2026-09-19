---
rg: 2
id: virtually-free-reflections-share-all-residuals
kind: claim
title: Every classical finite-dimensional residual of an internal virtually free reflection is the same base
root: true
artifacts:
  - research/virtually-free-reflections-share-all-residuals-proof.md
---

Let `Q` be a countable virtually free group and let

```text
W_Q=U^(Q) semidirectProduct Q<=U
```

be its internal Leavitt reflection.  Put `B_Q=U^(Q)`.  Then one subgroup is
simultaneously all of the following residuals:

```text
Rad_MF(W_Q)
 =Rad_fin(W_Q)
 =Rad_compact(W_Q)
 =Rad_fd-unitary(W_Q)
 =Rad_linear,k(W_Q)
 =B_Q                                                   (UVR1)
```

for every field `k`.  Here each residual is the intersection of kernels of
all homomorphisms into the indicated target class.  Consequently the quotient
map `W_Q->Q` induces canonical isomorphisms

```text
profiniteCompletion(W_Q)~=profiniteCompletion(Q),
Bohr(W_Q)~=Bohr(Q).                                     (UVR2)
```

The same map identifies the complete finite-dimensional representation
functor of `W_Q`, over every field and in every unitary dimension, with that
of `Q`.  Thus exact finite-dimensional representation theory and MF
representation theory erase precisely the same large, singly normally
generated subgroup, even though `W_Q` itself is non-MF.

If `Q` is finitely generated, then `W_Q` is finitely generated and

```text
W_Q has property (T)  iff  Q is finite.                 (UVR3)
```

Therefore one fixed simple finitely generated Kazhdan group contains both
Kazhdan and non-Kazhdan finitely generated non-MF subgroups with completely
prescribed virtually free finite-dimensional shadows.
