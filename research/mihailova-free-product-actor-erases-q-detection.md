---
rg: 2
id: mihailova-free-product-actor-erases-q-detection
kind: claim
title: Replacing the Mihailova direct-product actor by a free product erases all Q-detection
distinct_from:
  mihailova-free-rounding-projective-cross-fence: that keeps the direct-product actor and isolates its projective lifting obstruction; this removes the obstruction by deleting cross relations and proves that doing so also deletes the detecting coefficient.
  mihailova-left-right-local-models-do-not-see-q: that concerns finite local metric models for the direct-product action; this is an operator-representation no-go for the free-product replacement.
---

Let `pi:F_m->Q` be any epimorphism.  Instead of the direct-product actor
`F_m x F_m`, let

```text
G_tilde=F_m * F_m = F_(2m)                            (MFP1)
```

act on `Q` by sending the first factor to left multiplication and the second
to right multiplication.  The action factors through `F_m x F_m`, but the
cross commutators remain nontrivial actor words which act trivially on the
base.

This makes the actor lifting problem vacuous: any choice of matrices for the
`2m` free generators is already an exact finite-dimensional representation
of `G_tilde`.  However it also makes the centered-lamp coefficient vacuous.
For every group `Q`, the quasi-regular representation

```text
lambda_(G_tilde/Stab(e))                              (MFP2)
```

is weakly contained in finite-dimensional representations of `G_tilde`.
Indeed `C*(F_(2m))` is residually finite-dimensional.  The direct sum of all
finite-dimensional representations is therefore faithful, hence weakly
equivalent to the universal representation; every representation, including
`(MFP2)`, is weakly contained in it.

Consequently the coefficient argument of
`mihailova-actor-liftable-ce-forces-q-hyperlinear` cannot be run with
`G_tilde`: its conclusion holds for every `Q`, including a hypothetical
nonhyperlinear one.  Equivalently, the kernel relations

```text
[(u,1),(1,v)]=1                                       (MFP3)
```

are not dispensable bookkeeping.  They are exactly what turns finite-
dimensional approximation of the quasi-regular coefficient into
hyperlinearity of `Q`--and, by Ioana's theorem, exactly what destroys
Hilbert--Schmidt stability of the actor.

Thus the Mihailova route has a sharp stability--detection tradeoff:

- with the direct product, the lamp coefficient detects `Q`, but actor
  exactification is a new projective cross-stability theorem;
- with the free product, actor exactification is automatic, but the lamp
  coefficient detects nothing about `Q`.

Keeping the free actor while asking its cross-commutator kernel merely to fix
the lamp does not evade the tradeoff.  At finite levels it asks an almost
invariant lamp vector to be moved to the exact invariant subspace of that
kernel.  The kernel has no uniform spectral gap, so this is the same missing
relative-stability step in invariant-vector form, not a consequence of
freeness.

