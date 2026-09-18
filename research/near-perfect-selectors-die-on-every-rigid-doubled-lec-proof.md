---
rg: 2
id: near-perfect-selectors-die-on-every-rigid-doubled-lec-proof
kind: route
title: Proof that near-perfect branch selectors on any rigid doubled LEC with tight outer soundness put the source problem in RP
target: near-perfect-selectors-die-on-every-rigid-doubled-lec
requires:
  - high-advantage-selector-witnesses-decode-good-outer-labellings
  - orientation-lifts-sandwich-2to1-game-values
  - near-perfect-selectors-on-rigid-dkkms-instances-put-np-in-rp
artifacts:
  - experiments/ugc-rigid-lec-2026-09-17/check_bitfree_branch_identity.py
---

Notation is that of the target. The proof follows the four steps of
`near-perfect-selectors-on-rigid-dkkms-instances-proof`, with every use of
DKKMS structure replaced by a hypothesis of the target.

## Lemma (bit-free branch identity)

Fix `o`, `H0 = (sigma_p, tau_q)` and `b`. Suppose `(H0, b)` satisfies the
oriented constraint of `e = (p, q)`. The constraint of `U_o` on `e` is the
bijection `sigma -> (pi_e(sigma), o_e(sigma))`, so
`(tau_q, b_q) = (pi_e(sigma_p), o_e(sigma_p))`. Hence `sigma_p` is the unique
preimage of `(tau_q, b_q)`, and by definition
`G_e(tau_q, b_q) = ev_e(sigma_p)`.

Now let `H0` be `lambda`-honest with dirt `d`, and put
`Cl := { e : ev_e(sigma_(p_e)) = <lambda_(a_e), x_e> }`, so `mu(Cl) >= 1 - d`.
For `e in Cl` with `(H0, b)` satisfying the oriented `e`,

```text
G_e( (H0, b)_(w_e) ) = G_e(tau_q, b_q) = ev_e(sigma_p) = <lambda_(a_e), x_e>.
```

This is (B_d) of Theorem 3 with seed `w_e = q_e`. Nothing about `o` or `b` was
used, which is the point: the witness may carry the selector's own bits.
(Part (2) of the artifact checks the identity on every labelling, bit assignment
and orientation of 40 random toy instances.)

## Theorem S\*

**Step 1 (forget the bit).** Fix a YES input `x` and an outcome `o = S(x)` with
`val(U_o) >= 1 - xi`, and an optimal lift labelling `W = (sigma_p, (tau_q, b_q))`.
Every lifted constraint implies the 2-to-1 constraint: the lifted one accepts
`(sigma, (tau, b))` only if `tau = pi_e(sigma)`. So `F := (sigma_p, tau_q)` has
`val_G(F) >= val_(U_o)(W) >= 1 - xi`. (Artifact part (1). It is the upper
half of the sandwich in `orientation-lifts-sandwich-2to1-game-values`.)

**Step 2 (rigidity).** By (Rig(xi, zeta, eps, d)) there are `lambda` with
`val_Phi(lambda) >= 1 - eps` and a `lambda`-honest `H0` with dirt `<= d` that
agrees with `F` at both endpoints outside a constraint set `Z`, `mu(Z) <= zeta`.

**Step 3 (lift back with the bits of W).** Put `H := (H0, b)` with the bits `b`
of `W`. Off `Z`, `H0` and `F` agree at both endpoints, and `H` and `W` carry the
same bit at `q_e`. So `H` and `W` agree at both endpoints of every `e notin Z`
(artifact part (3)). By the Lemma, `H` is honest for `lambda` with dirt `d` in
the sense (B_d). So `W` is a witness for `lambda` at distance `zeta`, of lift
value `>= 1 - xi`. This holds for every outcome of `S` with
`val(U_o) >= 1 - xi`, so with probability `>= theta`.

**Step 4 (decode).** The data `(Phi, U_o, mu, (q_e, a_e, x_e), G_e)` form an
LEC in the sense of `efficient-branch-selectors-list-decode-honest-outer-labels`:

* the seed alphabet `Sigma_q x {0,1}` has size `<= 2^l`;
* `2^m` is polynomial;
* (E) holds at `tau = 1/16`, and (M=) holds.

Its orientation lift is `U_o` itself, which is a unique game. Theorem 3 of
`high-advantage-selector-witnesses-decode-good-outer-labellings` uses only
(E), (M=), (B_d), the seed alphabet bound and the polynomial size of `2^m`
(Steps 1' to 3' of its proof). It applies to the selector `x -> S(x)`:

* on YES inputs, by Step 3, with `c1 = 1 - 2 eps - 8K'(xi + zeta + d) > 0`;
* on NO inputs, by (S).

So `Lang in RP`, with success `>= theta p0^2 c1 / 2` per trial. `square`

## Corollary (DKKMS)

Take `G = G_folded`, `P` the folding classes, `Q` the B-vertices, and
`ev_e(sigma)` the unfolding of `sigma` at the member `(U, L)` of `e`, evaluated
at `x_e`. Then `G_e` is the bit function of the DKKMS section of the decoder
node. A labelling `H0 = hon_kappa(lambda)` is `lambda`-honest with dirt
`d_kappa(lambda)`, because a copy is clean exactly when
`ev_e(hon_kappa(lambda)_C) = lambda_U|_L (x_e) = <lambda_U, x_e>`. So (Rig)
with `(10^(-5), 1/128, 1/16, 1/64)` is Steps 2 and 3 of
`near-perfect-selectors-on-rigid-dkkms-instances-proof` (Theorem R in the
regime). (E), (M=) and (S) are its Steps 0 and 4. Here `c1 >= 5/8`.

## The four failures

Theorem S\* has exactly the hypotheses (E), (M=), (Rig) and (S), plus the
format. A reduction realising H1 at every `eta'` gives, for each fixed `xi`, a
selector meeting the hypothesis of Theorem S\* with `theta = 1` once
`eta' <= xi`. So under `NP not in RP` one hypothesis fails. The format together
with (E) is (F1), (M=) is (F2), (S) is (F3) and (Rig) is (F4).
