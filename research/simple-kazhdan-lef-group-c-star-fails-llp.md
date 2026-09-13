---
rg: 2
id: simple-kazhdan-lef-group-c-star-fails-llp
kind: claim
title: The full C*-algebra of the simple Kazhdan LEF subshift group fails the local lifting property
distinct_from:
  kac-moody-lattice-is-non-hyperlinear-or-llp-failure: that dichotomy says a hyperlinear Kac--Moody lattice would give an LLP failure from hyperlinearity of a simple group with no finite-dimensional representations; this realizes that kind of failure for an explicit infinitely presented simple Kazhdan group.
  llp-non-rf-kazhdan-group-is-non-hyperlinear: that is the general theorem for non-residually-finite Kazhdan groups; this applies it to one explicit simple example.
---

Let `S = EL_3(LC(X,F_q) ⋊ Z)/Z` for an infinite minimal subshift `X`. Then `C*(S)` does not have
Kirchberg's local lifting property. `S` also lacks Kirchberg's factorization property.

This is Ozawa's remark in *About the QWEP conjecture* (arXiv:math/0306067): "It is unknown whether
there exists a simple property (T) group Γ which is hyperlinear. By the above theorem, the full
C*-algebra C*Γ of such a group Γ cannot have the LLP." It is now realized by an explicit group.
Earlier LLP failures for full group C*-algebras came from nonsimple groups: Thom's LEF non-RF
Kazhdan groups, and Ioana--Spaas--Wiersma's cohomological examples.

## Attempts

- **Contrapositive of the LLP dichotomy (2026-09-12).** `S` is infinite and simple, so it is not
  residually finite. It is Kazhdan and hyperlinear (`simple-kazhdan-lef-group-from-minimal-subshift`,
  reviewed PASS 0efeac410). By `llp-non-rf-kazhdan-group-is-non-hyperlinear`, LLP for `C*(S)` would
  make `S` non-hyperlinear. Hence `C*(S)` fails the LLP. The route is
  `simple-kazhdan-lef-group-c-star-fails-llp-proof`.
