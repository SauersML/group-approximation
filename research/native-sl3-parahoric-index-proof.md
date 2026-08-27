---
rg: 2
id: native-sl3-parahoric-index-proof
kind: route
title: Read the root depths from h and count Smith-type sublattices
target: native-sl3-edge-parahoric-has-index-forty-two
requires: []
---

The condition `g in hCh^-1` is `h^-1gh in M_3(Z)`.  Its three upper
entries are `g_12/2,g_23/2,g_13/4`, while its lower entries are multiplied
by `2,2,4`; this proves `(NSP2)`.  Multiplying `hZ^3` by the harmless scalar
two gives `(NSP3)`.

The `C`-orbit of `L` is the set of sublattices with quotient
`Z/4 directSum Z/2`.  Such a sublattice is the kernel of a surjection

```text
Z^3 -> Z/4 directSum Z/2
```

modulo an automorphism of the target.  A triple generates this finite
two-group exactly when its image generates its Frattini quotient `F_2^2`.
There are

```text
(2^3-1)(2^3-2)=42
```

surjective triples in the quotient and `2^3=8` lifts of each, while
`|Aut(Z/4 directSum Z/2)|=8`.  Hence the orbit, and therefore the index, is
`42`.  Weyl conjugation gives `(NSP5)`; maximizing the depth difference over
the six permutations gives depth two for every off-diagonal position,
proving `(NSP6)`.  The atom statement follows because `P` commutes with `C`
and `Q_w` commutes with `h_w C h_w^-1`.
