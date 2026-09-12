---
rg: 2
id: simple-t-augmentation-module-is-aperiodic
kind: claim
title: The binary augmentation module of a simple property-T group has no nonzero finite character orbit
distinct_from:
  infinite-character-actor-kills-fd-mark: that gives the abstract character-orbit criterion; this supplies its canonical algebraic actor and module.
---

Let `A` be an infinite finitely generated simple group with property `(T)`,
and put

```text
M=I_A=ker(epsilon:F_2[A]->F_2),                         (STA1)
```

with the left regular `A`-action.  Then every nonzero character of the
elementary abelian group `M` has an infinite `A`-orbit.

If a character has finite orbit, its stabilizer is finite index.  Infinite
simplicity implies that `A` has no proper finite-index subgroup: the core of
one would be a finite-index normal subgroup, and the resulting finite
permutation action cannot inject the infinite simple group.  Hence a finite
orbit character is actually `A`-invariant.

The invariant characters are dual to the coinvariants `(I_A)_A`.  The
augmentation exact sequence and the beginning of the homology exact
sequence give

```text
(I_A)_A ~= H_1(A;F_2).                                    (STA2)
```

An infinite simple group is perfect, so `(STA2)` is zero.  Thus the only
finite-orbit character is zero.

The module is finitely generated over `F_2[A]`: for any finite generating
set `S` of `A`, the elements `s-1`, `s in S`, generate the augmentation
ideal by

```text
gh-1=(g-1)+g(h-1).                                       (STA3)
```

Property `(T)` supplies one uniform `ell^2` spectral gap on every nonzero
character orbit.  Consequently `(A,I_A)` is an explicit algebraic instance
of the infinite actor in `infinite-character-actor-kills-fd-mark`.
