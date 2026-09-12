---
rg: 2
id: propagate-leavitt-tail-vanishing-across-two-faces
kind: route
title: Propagate one vanishing tail through its face and the opposite face
target: leavitt-packet-kernel-is-normally-generated-by-each-cycle
requires:
  - leavitt-finite-wreath-targets-have-eight-tail-normal-form
  - leavitt-has-an-explicit-finite-c-killing-certificate
artifacts:
  - research/artifacts/leavitt-eight-tail-full-support-and-normal-generation-2026-09-08.md
---

The coordinate system works over an arbitrary group `G`: a solution
defines `Q->G^E semidirect E`, and projection of `N` to coordinate
zero recovers the prescribed images of its eight generators. This
also proves the asserted finite presentation of `N`.

At each coordinate the anchor and retained relations define the
authenticated Thompson presentation, with `D_x A_x=z_x`. Simplicity
of `V` therefore gives `z_x=1 => A_x=B_x=D_x=d_x=1`; the converse
`d_x=1 => z_x=1` follows from the square and cube anchors.

On an `e_1,e_2` face the four `d` values have forms `pq`, `(pq)^-1`,
`qp`, and `(qp)^-1`, so vanishing at one vertex propagates across
that face. On an inactive face, the full mixed-coordinate formula
reduces to `B_x=z_(x+e_3)z_(x+e_1+e_3)^-1`. Its vanishing makes
the opposite face invariant under `e_1`; its four `d` values then
vanish as well. Thus any vanishing tail kills all eight.

Apply this to `N/<<c_x>>_N` to prove internal normal generation.
Every nontrivial image retains every `c_x`, so its restriction to
each local Thompson copy is nontrivial and therefore injective.
The native cycle is nontrivial, authenticating the copies inside
`N` itself. No simplicity conclusion about `N` is used or inferred.
