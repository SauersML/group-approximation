---
rg: 2
id: balanced-cylinder-commutator-decoder-proof
kind: route
title: Balance cylinder products and use a diagonal implementing coefficient shifts
target: binary-subshift-language-has-quadratic-group-witnesses
requires:
  - unit-idempotent-elementary-group-has-three-torsion-generators
artifacts:
  - research/artifacts/pestov91-marked-subshift-encoding-2026-09-13.md
---

Sections 2 and 3 give the full proof. Length-`l` matrix words have
coefficients supported on coordinate windows `[-l,l]`. For the reverse
direction, recover the fixed elementary roots and constant swaps from
the idempotent decoder. Construct `V=diag(u,u,u^{-2})` and concatenate
two cylinder roots by a commutator after shifting the second coefficient
using conjugation by a power of `V`.

Pad by neutral letters to a power of two and balance the product tree.
The explicit fixed-word bounds give
`L(m)<=4L(m/2)+25252m+15756`, `L(1)<=277`, hence
`L(m)<=30781m^2` and output length at most `2^17 n^2`.
The output evaluates to the elementary matrix of the input cylinder.
