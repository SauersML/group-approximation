---
rg: 2
id: mf-relation-closure-proof
kind: route
title: Closure axioms from the universal quotient and functoriality
target: mf-relation-closure
requires: [universal-mf-quotient, mf-radical-functoriality]
---

## Why sufficient

First, for every countable group `G'`,

```text
Rad_MF(G')  =  intersection of ker(f) over f : G' -> M, M countable MF.   (*)
```

Indeed `mf-radical-functoriality` puts `Rad_MF(G')` inside the kernel of
every homomorphism to an MF group, and `universal-mf-quotient` makes
`G' -> G'/Rad_MF(G')` itself a homomorphism to a countable MF group with
kernel exactly the radical.

Homomorphisms from `G` killing `N` correspond bijectively to homomorphisms
from `G/N`, so by `(*)` applied to `G/N`,

```text
mfroot(N)  =  q^{-1}( Rad_MF(G/N) ),        q : G -> G/N,
```

which is item 2.  The closure axioms:

- **Extensive:** `N` lies in every kernel over which the intersection runs.
- **Monotone:** enlarging `N` shrinks the family of admissible `phi`, hence
  enlarges the intersection.
- **Idempotent:** any `phi` to a countable MF group with `N <= ker(phi)` has
  `mfroot(N) <= ker(phi)` by definition of the intersection, so the
  admissible families for `N` and for `mfroot(N)` coincide, and the two
  intersections are equal.

Item 3: `G/mfroot(N)` is isomorphic to `(G/N)/Rad_MF(G/N)`, which is MF by
`universal-mf-quotient`.  Item 4: `N = mfroot(N)` iff `Rad_MF(G/N)` is
trivial iff `G/N` is MF, again by `universal-mf-quotient`.
