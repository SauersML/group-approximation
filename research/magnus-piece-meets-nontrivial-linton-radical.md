---
rg: 2
id: magnus-piece-meets-nontrivial-linton-radical
kind: claim
title: A nontrivial Linton radical meets every Magnus piece and dies in every residually rationally solvable quotient
distinct_from:
  linton-radical-has-a-short-weinbaum-marker: that finds a proper subword of the relator inside the radical; this shows the radical meets the whole Magnus piece of every zero-exponent basis, through the Bass--Serre tree, and constrains fold targets rather than packet quotients.
  rigid-magnus-groups-have-sofic-separating-quotients: that asks for separating quotients with sofic coset actions; this is a necessary condition on any such quotient when the radical is nontrivial.
---

ESTABLISHED. Let `G = <a,t | w>` be a torsion-free one-relator group with Linton
radical `R = G_Q^(omega) != 1`. For every zero-exponent basis with Magnus piece
`B_0`:

1. `R ∩ B_0 != 1`;
2. every homomorphism `rho: G -> H` with `H_Q^(omega) = 1` kills `R ∩ B_0`. This
   covers free `H`, residually torsion-free nilpotent `H`, and rationally
   solvable amenable `H`.

So the fold input [[rigid-magnus-groups-have-sofic-separating-quotients]] needs,
whenever `R != 1`, a sofic target with nontrivial rationally perfect radical,
and `rho` must be nontrivial on `R`. Groups with `R = 1` need no fold, since
they are already sofic by [[residually-rationally-solvable-one-relator-sofic]].
