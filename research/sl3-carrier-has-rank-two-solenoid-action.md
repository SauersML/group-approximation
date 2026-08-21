---
rg: 2
id: sl3-carrier-has-rank-two-solenoid-action
kind: claim
title: Every trace restricts on the metabelian core to a rank-two invariant measure on the joint two-solenoid
distinct_from:
  far-sector-is-solenoid-measure-rigidity: that identifies the SL_2 far sector with approximate rigidity for ONE hyperbolic solenoid automorphism and records that single-map rigidity is unavailable (only the x4 direction exists there); this exhibits, inside SL_3(Z[1/2]), a rank-TWO abelian action with independent expansions, dissolving that structural obstruction at higher rank.
  odd-congruence-lambda-exact-sector-collapses: that closes the odd Lambda-exact sector by the Weyl evaluation; this equips the surviving (2-adic/outlier) sector with the measure-rigidity toolkit that the closure proof never needed.
  hnn-carrier-enemy-moment-splitting: that pins single-t-block moments of carrier characters; this pins the restriction of ANY trace of Gamma itself to the solvable core, a constraint that composes with the moment splitting on two-block words.
---

Let `Gamma = SL_3(Z[1/p])`, let `D = {diag(p^a, p^b, p^(-a-b))} iso
Z^2` be the diagonal subgroup, `U` the upper unipotent subgroup and
`U^-` the lower one, each root subgroup `R_alpha iso Z[1/p]`.  Then:

1. **The metabelian core.**  `Q = D ltimes U iso Z^2 ltimes
   Z[1/p]^3`, with `x in Z^2` acting on `R_alpha` by multiplication
   by `p^(<alpha, x>)`; the three positive roots give pairing vectors
   `<alpha, .>` spanning the dual of `Z^2`.  By SNAG, a unitary
   representation of `Q` is a projection-valued measure on
   `hat(Z[1/p]^3)`, the threefold product of `p`-adic solenoids,
   together with a `Z^2`-action by the dual automorphisms — a
   RANK-TWO abelian action with (at least) two multiplicatively
   independent expanding directions, since the root pairings are
   linearly independent.

2. **Traces give invariant measures.**  For ANY trace `tau` of
   `Gamma` (or of the carrier `H`, restricted to `Gamma`),
   conjugation invariance of `tau` makes the spectral measure of
   `tau|_U` on the joint solenoid invariant under the `Z^2`-action:
   `tau(pi(x) u pi(x)^(-1)) = tau(x u x^(-1))` is again a value of
   `tau|_U`.  For the regular trace the measure is joint Haar; for an
   enemy character of the carrier, the two-block leak data couples to
   this invariant measure through the moment-splitting frame.

3. **The rank-one obstruction dissolves.**  The recorded reason the
   `SL_2` far sector cannot be closed inside its solvable subgroup
   (`far-sector-is-solenoid-measure-rigidity`: a single hyperbolic
   solenoid map has too many invariant measures, and Furstenberg-type
   rigidity needs two independent maps) does not exist here: the
   `Z^2`-action on the joint solenoid is exactly the higher-rank
   abelian setting of Katok--Spatzier/Einsiedler--Katok--Lindenstrauss
   measure rigidity, where invariant measures with positive entropy
   along coarse directions are algebraic.  The enemy's restriction to
   `Q` is therefore constrained by a genuine rigidity theory, not by
   a single-map phenomenology.

## Attempts

- **What this does and does not give.**  Parts 1-2 are elementary
  (proof route) and unconditional; part 3 is a toolkit unlock, not a
  proof: the enemy is constrained by MORE than invariance of one
  measure (mixed words couple `Q` to `Lambda`-noncommutativity and to
  the letter), and the zero-entropy branch of higher-rank rigidity is
  genuinely hard.  The right next theorem is an entropy computation:
  the regular trace forces maximal entropy along every root
  direction, which is exactly the positive-entropy regime where
  EKL-type classification applies — so the enemy's `Q`-data should
  be provably ALGEBRAIC (Haar on a closed invariant subgroup), and
  the remaining freedom finite-dimensional.  Making that precise is
  the measure-rigidity attack on the surviving 2-adic sector.
- **Composition with the closed sector.**  On odd-congruence
  Lambda-exact microstates nothing survives
  (`odd-congruence-lambda-exact-sector-collapses`); the enemy is
  confined to 2-adic/outlier data, where its `Q`-restriction is a
  rank-two invariant measure by part 2.  The two structure theorems
  see complementary parts of the enemy: the Weyl evaluation kills the
  `h`-slot given exact `Lambda`-structure; the solenoid action
  constrains the unipotent spectral data when the `Lambda`-structure
  is inexact.
