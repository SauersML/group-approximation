---
rg: 2
id: nonsofic-witness-modular-finiteness-proof
kind: route
title: Fold each witness onto a free or free abelian kernel over its vertex group
target: nonsofic-witness-finiteness-over-modular-division-rings
requires:
  - free-kernel-extensions-keep-modular-stable-finiteness
  - kt-pair-group-double-is-nonsofic
  - kun-thom-nonsofic-wreath
  - free-wreath-over-an-amenable-action-can-be-nonsofic
  - fp-torsion-free-nonsofic-group-of-cd-at-most-three
  - integer-lamp-leavitt-cover-wreath-is-torsion-free-nonsofic
---

Items 1–4 of `free-kernel-extensions-keep-modular-stable-finiteness` are cited as (FK1)–(FK4).

**Item 1.**
- `kun-thom-nonsofic-wreath` (Theorem E) makes `G` residually finite.
- A residually finite group is sofic: for finite `S`, a finite quotient injective on `S` acting on
  itself by left translation is an exact permutation model.
- So `D[G]` is stably finite by (FK3), and (FK4) gives the double and the centralizing HNN
  extension.
- `kt-pair-group-double-is-nonsofic` gives nonsoficity of the double.

**Item 2.**
- `free-wreath-over-an-amenable-action-can-be-nonsofic` gives nonsoficity and a sofic actor `H`.
- The kernel `*_X Z` is free on `X`, and `H` permutes its basis.
- (FK3) makes `D[H]` stably finite, and (FK4) finishes.

**Item 3.**
- `fp-torsion-free-nonsofic-group-of-cd-at-most-three` defines `D_3` as the double of `G_OW` over
  `Gamma_hat`.
- (FK4) gives both equivalences.

**Item 4.**
- `integer-lamp-leavitt-cover-wreath-is-torsion-free-nonsofic` defines `W_hat` as the permutational
  integer-lamp wreath over `G_hat`.
- Its kernel is free abelian, and `G_hat` is a retract.
- (FK4) gives both equivalences. `QED`
