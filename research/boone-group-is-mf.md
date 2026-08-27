---
rg: 2
id: boone-group-is-mf
kind: claim
title: Every Rotman-Boone group is operator-MF with MF full group C-star algebra
distinct_from:
  boone-instruction-twists-extend-to-base-automorphisms: that is the structural reduction; this is the target statement it reduces.
  finitely-presented-amenable-undecidable-word-problem: that supplies an amenable, hence MF, finitely presented group with undecidable word problem by a different (Minsky-machine) engine; this asks it for the Boone engine, whose commutation detector the Aanderaa compiler needs.
---

For every Turing machine `T`, the Boone group `G_nb(T)` of Rotman Ch. 12 is
operator-MF, and `C*(G_nb(T))` is MF.

If true, this is a finitely presented group with undecidable word problem
and MF full group C-star algebra, of a shape (commutation detector `[k_0,
w^-1 t_0 w] = 1 iff w in R`) that the Aanderaa proof of the Higman embedding
theorem can consume directly.

## Attempts

The tower reduction of
[[boone-instruction-twists-extend-to-base-automorphisms]] puts `G_nb(T)`
inside three central HNN extensions over `B x| F_I`; the only missing input
is [[boone-base-has-corona-inner-instruction-automorphisms]].  A direct
Britton-based approximate-representation construction was not attempted.
