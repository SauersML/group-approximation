---
rg: 2
id: class-finite-normal-subgroup-from-torsion-free-fcc
kind: route
title: A torsion-free finitely presented group with finitely many classes is its own centralizer-free class-finite normal subgroup
target: some-fp-group-has-centralizer-free-class-finite-normal-subgroup
requires:
  - some-infinite-fp-torsion-free-group-has-finitely-many-classes
---

Let `T` be infinite, finitely presented and torsion-free with finitely many
conjugacy classes. Take `N = T`.

- `N` is finitely generated, since `T` is finitely presented.
- `T/N = 1` is of type `F_infinity`, hence of type `F_3`.
- `N` has finitely many `T`-classes, since these are the conjugacy classes of `T`.
- `C_T(N) = Z(T) = 1`. If `z in Z(T)` and `z != 1`, then `z` has infinite order,
  so `z, z^2, z^3, ...` are pairwise distinct. Each is central, so each is the
  only element of its conjugacy class. That gives infinitely many classes, a
  contradiction.

So `(T, N)` witnesses the target. `∎`
