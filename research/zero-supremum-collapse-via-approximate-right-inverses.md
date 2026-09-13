---
rg: 2
id: zero-supremum-collapse-via-approximate-right-inverses
kind: route
title: Approximate right inverses for two finite-base Bernoulli shifts of different entropy give a collapse at zero supremum
target: zero-rokhlin-supremum-forces-bernoulli-collapse
requires:
  - zero-supremum-endomorphisms-have-approximate-right-inverses
  - bernoulli-isomorphism-from-approximate-right-inverses
---

Let `G` be countably infinite with `h^Rok_sup(G) = 0`. Take `κ` uniform on 6 points and `λ` uniform on 2 points.

1. By the first prerequisite, `X_κ` and `X_λ` both have approximate right inverses.
2. By item 6 of `bernoulli-isomorphism-from-approximate-right-inverses`, `X_κ ≅ X_λ`. That item also supplies the
   factor maps in both directions, because a group with supremum zero is not sofic, hence nonamenable.
3. So `log 3 = log 6 − log 2 ∈ D(G) \ {0}`.

The same item gives the strong form restricted to finite bases: all finite-base Bernoulli shifts over `G` are
isomorphic.

This route is a strict weakening of `zero-supremum-collapse-via-dense-iid-generators` in its input. That route needs
generating i.i.d. partitions to be dense in the partition metric. Here only approximate right inverses by
endomorphisms are needed, one shift at a time, and the category argument runs in the space of joinings.
