---
rg: 2
id: thompson-clifford-central-product-tape
kind: claim
title: A finitely presented Thompson orbit carries a self-similar central-product Clifford tape
artifacts:
  - research/artifacts/thompson-clifford-central-product-tape-2026-08-20.md
distinct_from:
  finite-bi-index-clifford-tape-presentation: that uses one complete-graph anticommuting lamp orbit for a capacity contradiction; this uses two Pauli species with same-site commutator and off-site commutation, giving a genuine CAR tensor tower.
  thompson-v-central-extensions-split: that excludes central classes on bare V; this puts the nontrivial class in the lamp kernel while the V prefix mixers act without projective holonomy.
---

There is an explicit finitely presented group

```text
VCl=K_X semidirect V
```

where `V` is Thompson's group on one rational Cantor orbit and `K_X` is the
central product of one-qubit Pauli groups over that orbit.  It fits into a
non-split central extension by `<J>~=C_2`, contains two conjugate commuting
child copies intersecting exactly in `<J>`, has an internal sibling swap, and
contains one newly addressed Pauli pair at every binary depth.  It has a
faithful tracial crossed-product representation with `J=-I`.

The exact tape does not admit a hidden uniformly bounded full-table naming.
For every finite presentation and every choice of word representatives, the
maximum filling area in its natural rank-`N` Pauli multiplication table is at
least linear in `N`; see
`thompson-clifford-table-area-grows-linearly-in-rank`.  This sharper
crossed-Fox obstruction uses the `p`-lamp quotient and is independent of the
choice of word representing the identity.
