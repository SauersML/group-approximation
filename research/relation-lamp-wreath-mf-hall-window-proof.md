---
rg: 2
id: relation-lamp-wreath-mf-hall-window-proof
kind: route
title: Hall-separable finite windows of the relator subgroup give exact lamp permutation models, and Malcev kills the augmentation in finite dimensions
target: relation-lamp-wreath-is-mf-with-nontrivial-fd-radical
requires: []
---

## Proof

The complete proof is the `## Proof` section of the target claim.  It uses
only classical theorems, cited there: M. Hall's separability of finitely
generated subgroups of free groups, and Malcev's residual finiteness of
finitely generated linear groups.

- **MF.**  At level `L`, the finitely generated window `H_L = <R cap S_L>`
  is contained in a finite-index `K_L` that misses the finite set of short
  non-relator quotients `u^-1 v`.
  - `F` permutes `F/K_L`, and `z` acts diagonally with a single phase at the
    base coset.
  - Every relator of `W` then holds exactly, at every level `L` at least its
    length, and every nonzero lamp keeps a fixed-size phase at one coset.
  - A regular-representation block separates the elements of `F`.
- **Finite-dimensional radical.**  In a finite quotient of a linear image, `R`
  acts trivially on the lamp image.  That action therefore factors through a
  finite quotient of `G`, which is trivial.  So `I_G ZG` dies, and it dies in
  the linear image because that image is residually finite by Malcev.
- **Cover.**  `[R,R]` is normal in `W` and acts trivially on `ZG`.  The dummy
  Fox derivative identifies the normal closure of `z` in `F_(n+1)/[R',R']`
  with `ZG`, which gives `E' = ZG x| E = W/[R,R]`.
