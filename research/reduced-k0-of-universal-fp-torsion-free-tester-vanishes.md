---
rg: 2
id: reduced-k0-of-universal-fp-torsion-free-tester-vanishes
kind: claim
title: "The fixed finitely presented torsion-free universal Whitehead tester has vanishing reduced projective class group"
distinct_from:
  higher-whitehead-universal-finitely-presented-torsion-free-group: that is the established universal embedding injecting every connective Whitehead group into one fixed group; this is the open computation that the degree-zero Whitehead group of that fixed group vanishes.
  hsiang-reduced-k0-of-torsion-free-group-rings-vanishes: that quantifies over every torsion-free group; this concerns one fixed finitely presented group, and the two are equivalent through the universal embedding.
  full-farrell-jones-for-fixed-fp-torsion-free-tester: that asks for the whole Full Farrell--Jones package for the tester; this asks only for vanishing of its reduced projective class group with integer coefficients.
---

Let `U` be the finitely presented torsion-free group constructed in
[[whitehead-universal-group-via-effective-hnn-and-rope]], the witness of
[[higher-whitehead-universal-finitely-presented-torsion-free-group]]. Then

```text
K̃_0(Z[U]) = Wh_0(U) = 0.
```

Consequences:

- **Problem 1.21.** By
  [[f-infinity-finite-cd-groups-type-f-via-universal-tester]], this claim
  gives a positive answer. Conversely, a group `G` of type `F_∞` with finite
  cd that is not of type F has a nonzero Wall class in `K̃_0(Z[G])`
  ([[fp-type-fp-group-is-type-f-iff-wall-class-vanishes]]), and the universal
  embedding carries it to a nonzero element of `K̃_0(Z[U])`.
- **Hsiang's conjecture.** This claim is equivalent to
  [[hsiang-reduced-k0-of-torsion-free-group-rings-vanishes]], by
  [[hsiang-reduced-k0-via-universal-tester]] and
  [[universal-tester-reduced-k0-from-hsiang]].

## Attempts

- **Compute from the construction.** `U` is built from a countable free
  product `Q` of all countably generated recursively presented torsion-free
  groups, then `Q * F(a,b)`, an HNN extension with free edge group, and a
  Higman-rope HNN extension whose edge is a free-group double. The edge
  Whitehead spaces are contractible, so `Wh_0` of the vertex group injects
  into `Wh_0(U)`. That is the tester's whole point. It also means
  `K̃_0(Z[U])` contains `K̃_0(Z[K])` for every such `K`. So computing
  `K̃_0(Z[U])` from the construction contains the whole problem, and there is
  no shortcut.
- **Farrell–Jones for `U`.** The open claim
  [[full-farrell-jones-for-fixed-fp-torsion-free-tester]] would give this
  claim. It is the same one-group question with the full coefficient package.
