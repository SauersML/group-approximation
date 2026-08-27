---
rg: 2
id: property-t-must-upgrade-global-augmentation-rounding
kind: claim
title: Property T must supply the missing global augmentation-module rounding
distinct_from:
  infinite-character-actor-word-energy-interface: that controls actor transport after a global spectral PVM has been decoded; this asks for the global PVM itself.
---

OPEN.  Let a finitely presented property-`(T)` group `A` act transitively on
a countable set `X`, with finitely many diagonal orbits and finitely generated
stabilizers, and let

```text
M={f in direct_sum_X F_2: sum_x f(x)=0}.
```

Prove a normalized-HS rounding theorem which, from the finite presentation
relators of `M rtimes A`, extracts one exact finite-support spectral PVM for
the whole `M` action on the same (or boundedly amplified) Hilbert space,
preserving a fixed nonzero lamp with a modulus independent of the number of
virtual sites.

`finitary-alternating-augmentation-lamp-global-rounding-no-go` shows that
high transitivity and finite diagonal-orbit combinatorics are insufficient.
The proof must use a quantitative property absent from the locally finite
actor, such as a relative Kazhdan projection which synchronizes all point
lamps simultaneously.  Glebsky's finite-family simultaneous commuting
theorem has a modulus depending on the family size and does not supply this.

## Attempts

- **Round every finite site window.**  The constants depend on its size and
  the resulting PVMs need not be compatible as the window grows.
- **Use only conjugacy of pair relations.**  The finitary-alternating model
  has exactly the same bounded equality-pattern orbit symmetry and still
  defeats global exactification.
- **Invoke property `(T)` of the actor without a relative module estimate.**
  Ordinary `(T)` controls almost invariant vectors in actor
  representations; it does not directly make an unbounded family of almost
  commuting involutions jointly diagonal.
- **Form the obvious relative-Kazhdan Hilbert--Schmidt bimodule.**
  `relative-kazhdan-bimodule-requires-whole-module-covariance` shows that its
  semidirect-product relators are precisely the full family of covariance
  identities one is trying to prove.  Before global covariance it is only a
  free-product representation, so the relative Kazhdan projection cannot
  yet be applied.
