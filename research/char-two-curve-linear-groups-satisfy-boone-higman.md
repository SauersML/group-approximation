---
rg: 2
id: char-two-curve-linear-groups-satisfy-boone-higman
kind: claim
title: Finitely generated linear groups over characteristic-two fields of transcendence degree at most one satisfy Boone--Higman
distinct_from:
  char-two-laurent-linear-groups-satisfy-boone-higman: that treats the coefficient rings F_q[t,1/t] and free algebras; this treats every field of characteristic two with transcendence degree at most one over F_2, contains the Laurent case, and says nothing about free algebras.
  fp-self-similar-groups-embed-in-fp-simple-groups: that source proves Boone--Higman for finitely generated subgroups of GL_n(Q), a characteristic-zero statement through self-similar affine groups; this is a characteristic-two statement through one finitely presented simple Leavitt unit group.
artifacts:
  - research/artifacts/boone-higman-self-similar-and-complexity-2026-09-11.md
---

**ESTABLISHED (conditional on the imported finite presentation of
`L_(F_2)(1,2)^x`).** Let `K` be a field of characteristic `2` whose
transcendence degree over `F_2` is at most `1`, and let `n >= 1`. Every
finitely generated subgroup of `GL_n(K)` embeds in the finitely presented
simple group `L_(F_2)(1,2)^x`, and so satisfies the Boone--Higman conjecture.

In particular this covers every finitely generated subgroup of `GL_n(F_q(t))`
for `q` a power of two, and of `GL_n` over every global function field of
characteristic two: `SL_n(F_q[t])`, the S-arithmetic groups `SL_n(O_S)` in
characteristic two, and the lamplighters.

The method stops at transcendence degree one. Any commutative subring of
`M_d(C)` with `C` a commutative ring of Krull dimension one is integral over
`C` by Cayley--Hamilton, hence of Krull dimension at most one. So the
regular-representation step below cannot place `F_2[t_1,t_2]` inside
`M_d(F_2[g,g^-1])`. Other embeddings into `L_(F_2)(1,2)` are not excluded.

DERIVATION
char-two-curve-linear-groups-proof
