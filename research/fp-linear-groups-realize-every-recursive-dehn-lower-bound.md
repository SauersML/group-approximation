---
rg: 2
id: fp-linear-groups-realize-every-recursive-dehn-lower-bound
kind: claim
title: For every recursive function some finitely presented subgroup of GL_n(Q) has Dehn function at least that function
distinct_from:
  fp-simple-dehn-functions-realize-every-recursive-lower-bound: that asks for finitely presented simple groups; this asks for finitely presented linear groups over Q, which would supply them through the Llosa Isenrich--Schesler--Wu quasi-retract theorem.
  kms-arbitrarily-hard-fp-rf-groups: that realizes arbitrarily hard word problems (and, in the source, large Dehn functions) by finitely presented residually finite solvable groups not claimed linear; this requires linearity over Q.
---

**OPEN, conjectured false.** For every recursive `f: N -> N` there are `n` and a
finitely presented subgroup `H <= GL_n(Q)` with `f ≼ delta_H`.

By `fp-simple-large-dehn-via-linear-quasi-retracts` it would answer Zaremsky
Problem 1.16 affirmatively. The best known case is exponential, e.g.
`BS(1,2) <= GL_2(Q)` (exponential Dehn function, [Ger92] as cited in
arXiv:2305.15176v2). Llosa Isenrich–Schesler–Wu, arXiv:2510.01952v1, p. 4: "no
recursive upper bound on Dehn functions of finitely presented linear groups is known
so far, though conjectured to exist by Gersten and Riley [GR05, Conjecture 8.7], the
fastest known Dehn function of a linear group is exponential."

## Attempts

1. **Distortion towers.** Superexponential Dehn functions usually come from towers
   of distorted cyclic subgroups: Baumslag–Gersten, iterated Baumslag–Solitar
   relations, hydra doubles. The basic tower pattern `b a b^-1 = a^2`,
   `c b c^-1 = b^2` with `a` of infinite order has no linear model over any field
   (`baumslag-solitar-towers-have-no-faithful-linear-image`). *Dead for linear
   inputs.* Other mechanisms are not excluded.
2. **Subgroups of arithmetic and S-arithmetic groups.** Every finitely generated
   subgroup of `GL_n(Q)` lies in some `GL_n(Z[1/N])`. Finitely presented subgroups
   need not inherit Dehn upper bounds from it, so nothing blocks a large Dehn function
   a priori, but no example beyond exponential is known (LISW p. 4). *Not attempted
   here.*
3. **Refutation side.** A recursive upper bound for all finitely presented linear
   groups (Gersten–Riley) would kill this claim and with it this route to Problem
   1.16. It would not decide Problem 1.16. *Not attempted.*
