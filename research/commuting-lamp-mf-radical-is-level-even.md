---
rg: 2
id: commuting-lamp-mf-radical-is-level-even
kind: claim
title: The MF radical of the commuting-lamp quotient is the level-even lamp subgroup
root: true
distinct_from:
  commuting-lamp-quotient-not-mf: That established claim exhibits one nontrivial radical element; this one asks for the exact value of the whole radical.
  corona-hs-radical-is-finite-residual: That established claim computes the tracial-shadow set as `L_0`; this one asks whether the operator-norm radical is all of `L_0`, i.e. whether the two coincide on this group.
  commuting-lamp-quotient-structure: That established claim identifies the isomorphism type of the group; this one computes its MF radical.
  universal-mf-quotient: That is the generic existence theorem for the universal MF quotient; this one computes that quotient explicitly for one concrete group.
  commuting-lamp-quotient-mf: That resolved claim asked whether the group has an injective corona representation; this one asks for the exact radical now that non-MF-ness is established.
---

`Rad_MF(W/<zeta>) = L_0`, the level-even lamp subgroup; equivalently, the
universal MF quotient of `W/<zeta>` is the explicit residually finite
level quotient `(sum_{n in Z} Z/2) semidirect V`.

## Ideas

**Upper bound — established.**  `Rad_MF <= L_0` because operator-norm
invisibility implies tracial invisibility and
`corona-hs-radical-is-finite-residual` computes the tracial-shadow set as
exactly `L_0`.

**Lower bound — the iterated collapse.**  Stage one is
`commuting-lamp-quotient-not-mf`: the involutive collapse identifies the
eight lamps of each affine block, placing the block-difference lamps in
the radical.  The proposed iteration: quotient by the stage-one
identifications; the block set is `V`-equivariantly the original site set
again, so the same `(Gbar, tau)` compression rule applies in the
quotient, identifying depth-two dyadic blocks; transfinitely iterating
and taking unions stays inside the radical by
`sound-rule-transfinite-closure`, and the union over all depths is
exactly the even-parity condition on every level, i.e. `L_0`.

**What is missing.**  The self-similarity step needs a verified
group-theoretic statement: that the stage-`r` quotient is again a
commuting-lamp wreath over a `V`-isomorphic site space with the induced
compression pair, and that the stage-`r` collapse defect maps onto the
depth-`(r+1)` parity identifications.  Stage one is verified; deeper
stages are not yet.  Once they are, the claim follows by
`sound-rule-transfinite-closure` (completeness direction: the level
quotient is residually finite, hence MF), and this becomes the first
exact radical computation of the program with a genuinely transfinite
inference chain.
