---
rg: 2
id: finite-root-algebra-forces-steinberg-triviality
kind: claim
title: One finite root von Neumann algebra forces a binary-Leavitt Steinberg representation to be trivial
artifacts:
  - research/artifacts/hilbert-hotel-character-rigidity-seam-audit-2026-08-21.md
distinct_from:
  steinberg-cover-fd-triviality: that assumes the whole representation space is finite dimensional; this allows an arbitrary finite von Neumann target and assumes only that one root subgroup generates a finite-dimensional algebra.
  steinberg-hyperfinite-hs-stable: that concerns approximate representations with amenable limiting algebra; a diffuse hyperfinite root algebra is fully compatible with that theorem and is not covered here.
  affine-leavitt-steinberg-mark-is-fd-invisible: that kills one active relative root by passing to a finite coefficient quotient; this is the simple full-Leavitt root-faithfulness dichotomy.
---

Let `L=L_(F_2)(1,2)`, let `n>=3`, and let

```text
pi:St_n(L)->U(M)
```

be a unitary representation in an arbitrary von Neumann algebra.  Exactly one
of the following occurs:

1. `pi` is trivial; or
2. for every `i!=j`, the root map
   `a |-> pi(x_ij(a))` is injective.

Consequently, if `pi(x_ij(L))''` is finite dimensional for even one root,
then `pi` is trivial.  In particular this applies to a representation into a
finite factor, but factoriality alone is not enough: the hypothesis concerns
the dimension of the abelian **root algebra**, not the ambient algebra.

For the canonical regular representation the root algebra is instead

```text
L((L,+)) ~= L^infinity(dual(L,+)),
```

which is diffuse because `(L,+)` is an infinite countable-dimensional
`F_2`-vector space.  Thus the theorem strictly extends exact
finite-dimensional triviality while also locating why it cannot touch the
regular character.
