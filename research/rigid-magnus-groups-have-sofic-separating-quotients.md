---
rg: 2
id: rigid-magnus-groups-have-sofic-separating-quotients
kind: claim
title: Rigid Magnus groups have sofic quotients with sofic coset actions separating finitely many base syllables
distinct_from:
  no-magnus-hierarchy-one-relator-groups-sofic: that asks for soficity of the rigid class; this asks for separating quotients with sofic coset actions, which imply soficity through the HNN fold but are not known to follow from it.
  hnn-folds-into-free-coset-wreath: that is the general embedding theorem; this is the specific separation input it needs for Magnus HNN extensions.
artifacts:
  - research/artifacts/hnn-fold-free-coset-wreath-2026-09-11.md
---

OPEN. Let `G = HNN(B_0; F_- -> F_+)` be a group of the rigid class
[[no-magnus-hierarchy-one-relator-groups-sofic]], with its Magnus shift. Take any
finite lists `b_j in B_0 \ F_-`, `b'_j in B_0 \ F_+` and `b''_j in B_0 \ {1}`.
Claim: there are a sofic group `H` and a homomorphism `rho: G -> H` such that
`H action H/rho(F_-)` is sofic, `rho(b_j)` is not in `rho(F_-)`, `rho(b'_j)` is not
in `rho(F_+)`, and `rho(b''_j) != 1`.

## Attempts

1. **Finite `H`.** *Certifies only residual finiteness.* The fold target is then
   free-by-finite, so the conclusion is that `G` is residually finite. Any rigid
   group that is not residually finite needs infinite `H`.
2. **Amenable or free `H`.** *Coset soficity is free; separation is the wall.*
   Every action of an amenable or free group is sofic (GKP arXiv:2401.04945,
   Theorems 2.17 and 2.19). The remaining obstruction is separation. Each
   nontrivial element of `B_0` must survive in some amenable (respectively free)
   quotient of `G`. If the Linton radical meets `B_0`, every rationally solvable
   quotient kills that intersection
   ([[rational-solvable-weinbaum-visibility-boundary]]). So amenable targets
   must be genuinely non-solvable, as in the Weinbaum packet problem. This is
   now exact: by [[magnus-piece-meets-nontrivial-linton-radical]], whenever
   `R != 1` the radical meets `B_0` and dies in every target with trivial
   rationally perfect radical. So free targets never work, and amenable targets
   must have a nontrivial rationally perfect radical.
3. **`H = G`.** *Circular.* It needs `G` sofic and the coset action
   `G action G/F_-` sofic, which is at least the target.
4. **Virtually special hyperbolic pieces.** *Defined on the wrong group.* Then
   `B_0 action B_0/F_+-` is sofic by separability, but `rho` must be defined on
   `G`, including the stable letter. Finite quotients of `B_0` compatible with the
   shift are the classical residual-finiteness condition, which is attempt 1
   again.
