---
rg: 2
id: nonzero-diagonal-clifford-cycle-proof
kind: route
title: Use a Cartan character fixed by coweights and permuted by Weyl charts
target: nonzero-diagonal-clifford-type-closes-all-six-local-cycles
requires:
  - sl3-depth-two-clifford-fiber-has-thirty-six-types
---

Using the nondegenerate trace pairing, write the character as

```text
chi_X(1+2^(a-2)Y)=exp(2 pi i tr(XY)/4).                 (DCT2)
```

It is nontrivial because `X!=0`.  More sharply, take an even diagonal
`Y=2Z` with `tr(Z)=0` and `tr(XZ)` odd.  Then `1+2^(a-2)Y` lies in the
depth-`a-1` kernel and `(DCT2)` is `-1` there.  If an irreducible above
`chi_X` factored through level `a-1`, it would be trivial on that element,
a contradiction.  Thus its minimal conductor is `a`.

For a coweight diagonal `d`, `dXd^(-1)=X`.  Transporting `(DCT2)` through
the associated parahoric identification therefore returns the same
character.  For a signed Weyl matrix `w`, the transported character is
`chi_(wXw^(-1))`, which represents the same coadjoint orbit `f_*`.
Products of the directional transports act on `X` by the corresponding
product of coweight and Weyl conjugations; every defining inverse, triangle,
or hexagon product is the identity, proving exact closure of all local type
cycles.
