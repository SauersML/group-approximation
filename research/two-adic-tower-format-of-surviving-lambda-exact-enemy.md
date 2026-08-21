---
rg: 2
id: two-adic-tower-format-of-surviving-lambda-exact-enemy
kind: claim
title: The surviving Lambda-exact enemy is an S3-interlocked depth-shifting tower system over the two-adic congruence quotients
distinct_from:
  odd-congruence-lambda-exact-sector-collapses: that closes the odd-level sector by the Weyl evaluation; this gives the exact data format of what survives at 2-power levels, where the exact slot does not exist and the evaluation cannot run.
  bs14-unitary-representations-are-periodic-cycle-packets: that classifies finite-dimensional BS(1,4) representations as periodic solenoid cycle packets -- one shift direction, and the SL_2 enemy adds one involution; this is the higher-rank format: three S3-interlocked shift directions with a sharp depth-two corner shift, over SL_3 congruence towers.
  sl3-carrier-has-rank-two-solenoid-action: that pins the Q-marginals of any trace (all Haar); this assembles the full finite-level data an enemy's 2-adic microstates must carry, marginals included.
---

Let `Gamma = SL_3(Z[1/2])`, `Lambda = SL_3(Z)`, `h = diag(2,1,1/2)`,
`Lambda_(-+) = Lambda cap h^(-+1) Lambda h^(+-1)`.  Suppose an enemy
of `(RC3)` has `Lambda`-exact microstates at 2-power levels:
`sigma_m` genuine representations factoring through
`G_(a_m) = SL_3(Z/2^(a_m))`, with `V_m` approximating `pi(h)`.  Then
the data `(sigma_m, V_m)` satisfies, exactly in the ultraproduct:

1. **Intertwining with a sharp depth-two shift.**  `V pi(lambda)
   V^(-1) = pi(h lambda h^(-1))` for `lambda in Lambda_-`, and
   conjugation by `h` shifts congruence depth by at most two:
   `Ad(h)(Lambda(2^b) cap Lambda_-) subseteq Lambda(2^(b-2))`, sharp
   at the corner root (`lambda = 1 + 2^b X` with `4 | lambda_31`
   gives `(h lambda h^(-1))_31 = 2^(b-2) X_31` with `X_31`
   unconstrained for `b >= 2`).  So `V` implements a depth-`<= 2`
   renormalization shift of the congruence tower, trivial exactly on
   the levels `sigma_m` does not see.
2. **The S3 interlock.**  `pi(w_13) V pi(w_13)^(-1) = V^(-1)`, and
   with `V_(h') = pi(w_12) V pi(w_12)^(-1)`, `V_(h'') = pi(w_23) V
   pi(w_23)^(-1)`: `V V_(h'')^(-1) = V_(h')` and all three commute
   (`[h_x, h_y] = e` in `Gamma`) -- three interlocked shift
   directions carrying the coweight lattice, in contrast to the
   single shift plus involution of the `SL_2`/BS(1,4) picture.
3. **Forced marginals.**  By
   `sl3-carrier-has-rank-two-solenoid-action` and the regular trace:
   the joint spectral measure of the commuting tuple
   `(V, V_(h'))` on the 2-torus is exactly Haar, as is the joint
   solenoid measure of the unipotent tower, and the two are coupled
   by the exact expansion relations `V pi(e_alpha(r)) V^(-1) =
   pi(e_alpha(2^(<alpha, mu_h>) r))`.

Consequently the surviving `Lambda`-exact enemy is precisely a
regular-trace, `S_3`-interlocked, depth-shifting solenoidal tower
system over `{SL_3(Z/2^a)}` -- every marginal forced, all freedom in
the joint realization.  The named finite-level question this
isolates: does the `S_3`-interlocked system of parts 1-2 admit
asymptotic closure over towers of genuine `SL_3(Z/2^a)`
representations with the regular trace profile?  A NO at any
uniformity closes the entire `Lambda`-exact sector (combining with
the odd and mixed-level analyses), pushing the enemy fully into the
non-exact uniform-outlier regime; a YES would be a structured
candidate enemy and would need to be tested against the
`43/168` fingerprint and the two-block moment constraints.

## Attempts

- **Why the odd-sector mechanism fails here, precisely.**  There is
  no exact slot: `h` has no image mod `2^a`, so no `V'` exists and
  the corrector calculus never starts; property (T) lifting still
  applies to `Lambda`-central elements (the conjugation action is
  genuine), so `pi(Lambda)' cap M` is still the congruence commutant
  tower -- the enemy `V` acts on it by part 1 as a depth-two shift,
  which is exactly what the Weyl evaluation cannot reach without the
  slot.  The residual constraint is the interlock of part 2 plus the
  trace; whether they pin `Ad(V)` on the tower is the open point.
- **Relation to the Iwahori lane.**  Part 1 restricted to one level
  is the `SL_3`-at-`2` version of the `B_+/B_-` compatibility of
  Dogon--Vigdorovich Question 1.4; the interlock adds two more
  compatibilities the `SL_2` question does not have.  Any
  quantitative progress on the DV question transports here as the
  single-direction subproblem.
