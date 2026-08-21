---
rg: 2
id: bffhz-envelope-exact-actor-proof
kind: route
title: Put a two-point Pauli seed in one free property-T translation orbit
target: bffhz-envelope-closes-exact-actor-host
requires:
  - bffhz-action-image-is-finitely-presented
  - relative-automorphism-action-is-highly-transitive
  - infinite-character-actor-kills-fd-mark
---

High transitivity and finitely generated stabilizers give the two finiteness
hypotheses in the permutational-wreath presentation criterion.  The assumed
finite presentation of the faithful action image gives the third.

The embedded simple group `S` acts freely.  A finite orbit of a coloring
under `B` restricts to a finite orbit under `S`, hence is fixed by `S`.
Choosing both seed points in one free `S`-orbit makes every fixed coloring
trivial on their binary difference.  Property `(T)` supplies the uniform
gap on every remaining orbit, and the abstract one-seed theorem finishes the
exact finite-dimensional collapse.
