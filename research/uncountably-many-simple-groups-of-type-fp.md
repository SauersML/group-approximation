---
rg: 2
id: uncountably-many-simple-groups-of-type-fp
kind: claim
title: "There are uncountably many pairwise non-isomorphic simple groups of type FP"
distinct_from:
  uncountably-many-simple-groups-of-type-fp2: that claim asks for type FP_2 (a finitely generated relation module); this asks for type FP, a finite projective resolution, which is strictly stronger and forces the groups to be torsion-free
---

There is a family of simple groups of type FP (over `Z`) containing
uncountably many isomorphism types.

This is the affirmative answer to the second part of Zaremsky's Problem 1.20,
and it implies the affirmative answer to the first part
(`uncountably-many-simple-fp2-groups-from-type-fp`).

## Attempts

- 2026-09-13 (lane z1-20-simple-fp2): all but countably many members of a
  witnessing family would be simple groups of type FP that are not finitely
  presented, and none is known in the sources checked. Groups of type FP have
  finite cohomological dimension, hence no torsion. That excludes
  Röver–Nekrashevych groups, topological full groups and every group containing
  a Higman–Thompson group, and with them the constructions of Llosa
  Isenrich–Schesler–Wu, arXiv:2510.01952.
- Model to imitate: Leary's Theorem 1.3 (arXiv:1512.06609), Morse theory on
  branched covers of CAT(0) cube complexes with acyclic links. A torsion-free
  simple analogue needs a simple group acting on a CAT(0) complex with a Morse
  function whose level sets can be branched; candidate hosts are torsion-free
  simple lattices in products of trees (Burger–Mozes), whose 1-dimensional
  links are graphs and so are never acyclic. No candidate yet.
