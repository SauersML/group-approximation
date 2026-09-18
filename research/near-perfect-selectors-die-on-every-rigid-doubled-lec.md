---
rg: 2
id: near-perfect-selectors-die-on-every-rigid-doubled-lec
kind: claim
title: On any linearly encoded composed 2-to-1 reduction with near-uniform directions, comparable marginals, 99 percent local rigidity and outer soundness below p0^2 c1 / 2, every polynomial-time branch selector with YES lift value 1 - xi puts the source problem in RP, so the non-DKKMS survivor of the parity-leaking selector hole needs one of four named failures
distinct_from:
  near-perfect-selectors-on-rigid-dkkms-instances-put-np-in-rp: that is Theorem S for the DKKMS construction only, with Theorem R supplying rigidity; this is the instance-free version, with rigidity, uniform directions, marginals and outer soundness as hypotheses, and it turns the survivor "instances that are not DKKMS" into four failable prerequisites.
  high-advantage-selector-witnesses-decode-good-outer-labellings: that decodes from a witness already near a locally honest patchwork (Theorem 3), and its Corollary B is DKKMS-only; this derives the witness from a plain 99 percent rigidity hypothesis on any doubled LEC, via a bit-free branch identity that holds for every orientation and every bit assignment.
  dkkms-grassmann-2to1-test-is-locally-99-percent-rigid: that is the DKKMS rigidity question; this treats rigidity as one hypothesis (F4) of an arbitrary composed reduction.
  parity-leaking-branch-selectors-reach-near-perfect-completeness: that is the OPEN hole; this refutes it, under NP not in RP, on every reduction satisfying the four hypotheses, whatever the inner test and outer game.
artifacts:
  - experiments/ugc-rigid-lec-2026-09-17/check_bitfree_branch_identity.py
---

**ESTABLISHED.** Route: `near-perfect-selectors-die-on-every-rigid-doubled-lec-proof`.

## Setting (doubled LEC)

A *doubled LEC* with parameters `(l, m)` is a polynomial-time map `x -> D(x)`
producing the following.

1. **Outer game.** A projection game `Phi = (A, B, rho, pi)` with `A`-labels in
   `F_2^m` and `2^m <= poly(|x|)`, exactly as in
   `efficient-branch-selectors-list-decode-honest-outer-labels`.
2. **Inner 2-to-1 game.** A game `G` with left vertices `P` and right vertices
   `Q`, a constraint law `mu`, and on each constraint `e = (p_e, q_e)` a 2-to-1
   onto map `pi_e : Sigma_(p_e) -> Sigma_(q_e)`, with `|Sigma_q| <= 2^(l-1)`.
3. **Annotations.** Each `e` has a target `a_e in A`, a direction
   `x_e in F_2^m`, and an *evaluation* `ev_e : Sigma_(p_e) -> F_2`. It is meant
   to be "the left label read at the direction `x_e`". The seed is `w_e := q_e`.

An *orientation* `o` gives each `e` a map `o_e : Sigma_(p_e) -> {0,1}` that is
injective on every fibre of `pi_e`. The *doubled lift* `U_o` is the unique game
with right alphabet `Sigma_q x {0,1}` and the bijective constraint
`sigma -> (pi_e(sigma), o_e(sigma))`. This is the lift of
`orientation-lifts-sandwich-2to1-game-values`. Its bit function is
`G_e(tau, b) := ev_e(sigma)` for the unique `sigma` sent to `(tau, b)`.

**Local honesty.** For an outer labelling `lambda`, a labelling `H0` of `G` is
*`lambda`-honest with dirt `d`* if

```text
mu{ e : ev_e(H0_(p_e)) != <lambda_(a_e), x_e> }  <=  d.
```

For DKKMS, `P` is the set of folding classes, `Q` the B-vertices `(V, L')`, and
`ev_e(sigma)` the unfolding of `sigma` at the member `(U, L)` evaluated at
`x_e`. Then `lambda`-honesty is exactly the patchwork condition
`d_kappa(lambda) <= d` of `high-advantage-selector-witnesses-decode-good-outer-labellings`,
where `kappa` is the member choice that defines `H0`.

**Hypotheses.** They are required on YES inputs only, except (S).

* **(E)** For every `(q, a)` in the support of `(w_e, a_e)`, the law of `x_e`
  is `1/16`-close to uniform on `F_2^m` in total variation.
* **(M=)** `rho_A(a) <= K' nu_A(a)` and `nu_A(a) <= K rho_A(a)`, where `nu_A`
  is the `mu`-law of `a_e`.
* **(Rig(xi, zeta, eps, d)), 99% local rigidity.** Every labelling of `G` of
  value `>= 1 - xi` agrees at both endpoints, outside `mu`-mass `zeta`, with
  some labelling `H0` that is `lambda`-honest with dirt `d` for some outer
  labelling `lambda` with `val_Phi(lambda) >= 1 - eps`. No efficiency is asked
  of `H0` or `lambda`.
* **(S)** On NO inputs, `val(Phi) <= s < p0^2 c1 / 2`, where

```text
p0 = 2^(-l) / 192,        c1 = 1 - 2 eps - 8 K' (xi + zeta + d)  > 0.
```

## Statement

**Theorem S\*.** Let `x -> D(x)` be a doubled LEC for a promise problem `Lang`,
satisfying (E), (M=), (Rig(xi, zeta, eps, d)) and (S). Let `S` be any randomized
polynomial-time algorithm that outputs an orientation `o = S(x)` of `G(x)`. It
may be global, adaptive and parity-leaking, and it may read the whole input.
Suppose that for every YES input `x`,

```text
Pr_S [ val( U_(S(x)) ) >= 1 - xi ]  >=  theta(|x|)  >=  1/poly(|x|).
```

Then `Lang in RP`, with one-sided success probability at least
`theta p0^2 c1 / 2` per trial.

**Lemma (bit-free branch identity).** For every orientation `o`, every
labelling `H0 = (sigma_p, tau_q)` of `G` and every bit assignment
`b : Q -> {0,1}`, the lift labelling `(H0, b) = (sigma_p, (tau_q, b_q))` has
this property on every constraint `e`: if `(H0, b)` satisfies the oriented
constraint of `e` in `U_o`, then `G_e(tau_(q_e), b_(q_e)) = ev_e(sigma_(p_e))`.
So if `H0` is `lambda`-honest with dirt `d`, then `(H0, b)` is honest for
`lambda` with dirt `d` in the sense (B_d) of Theorem 3, for every `o` and `b`.

**Corollary (DKKMS).** The DKKMS construction at a parameter point in the
Theorem S regime satisfies all four hypotheses, with `xi = 10^(-5)`,
`zeta = 1/128`, `eps = 1/16`, `d = 1/64`, `K = K' = 1`, `c1 >= 5/8`. So Theorem S
is the DKKMS case of Theorem S\*, and by
`dkkms-certified-parameters-lie-in-the-selector-kill-regime` this covers every
certified point.

## What it does to the hole (impact type 2)

`parity-leaking-branch-selectors-reach-near-perfect-completeness` (H1) asks for
a reduction `x -> D(x)` from a gap-3LIN source to Grassmann 2-to-1 instances,
and a selector with YES lift value `1 - eta'`, where `eta' -> 0`. Its recorded
survivor after the DKKMS kill was "non-DKKMS `D(I)`, meaning another inner test
or another outer game".

Assume `NP not in RP`. By Theorem S\*, any `D` that realises H1 must, at every
fixed `xi > 0` that `eta'` eventually undercuts, fail at least one of the
following. Each is a separate statement that can fail on its own.

* **(F1) No linear read-out.** There is no annotation `(a_e, x_e, ev_e)` into an
  outer game with `F_2^m` labels (`2^m` polynomial) whose directions are
  `1/16`-uniform given `(w_e, a_e)`. This is a structural condition on the
  inner test. DKKMS has one (item 3 of
  `dkkms-2to1-instances-satisfy-selector-decoding-hypotheses`).
* **(F2) Marginal blow-up.** `K'` is so large that
  `8 K' (xi + zeta + d) >= 1 - 2 eps` for every admissible rigidity constants.
* **(F3) Loose outer soundness.** `val(Phi)` on NO inputs is not below
  `p0^2 c1 / 2 = Theta(4^(-l))`. The composed game is then sound through an
  analysis that never needs the outer game to beat a `2^(-l)`-per-prover random
  list. DKKMS is not of this kind: its certified points force
  `eps_k <= p0^2 / 4`.
* **(F4) 99% non-rigidity.** For every `(zeta, eps, d)` with `c1 > 0`,
  (Rig(xi, zeta, eps, d)) fails on YES instances. So there are YES labellings of
  value `>= 1 - xi` that are `zeta`-far from every locally honest labelling of
  every good outer labelling. This is a 99%-regime statement about the inner
  test alone. It mentions no selector and no complexity assumption.

H1 near completeness `1` therefore requires, unless `NP in RP`,
building a new value-sound 2-to-1 reduction in which (F1), (F2), (F3) or (F4)
holds and then orienting it. No such reduction is on record: see
`kms-2to2-reduction-is-sound-only-for-colorings` for why the other
Grassmann reduction credited in this graph, KMS TR16-124, does not supply one.

## Not covered

* **Moderate completeness.** Lift value between `1/2` and `1 - xi`. This is the
  constant-bias cell, as in Theorem S.
* **2-to-2 inner games.** Their orientations pick matchings inside `K_(2,2)`
  blocks. The doubled lift and the bit-free identity are stated here for 2-to-1
  constraints only. The KMS/DKKMS 2-to-2 instances need a separate rigidity
  statement.
* **Which of (F1) to (F4) is hopeless.** Nothing here shows that a value-sound
  reduction with (F3) or (F4) cannot exist. (F4) is the natural next target: a
  proof that 1%-soundness of a Grassmann 2-to-1 test forces 99% local rigidity
  would close H1 for every Grassmann composition with a linear read-out and
  tight outer soundness.

This neither proves nor refutes UGC.

## Attempts

* **Abstraction (2026-09-18).** Theorem 3 of
  `high-advantage-selector-witnesses-decode-good-outer-labellings` is already
  instance-free. Theorem S used DKKMS only through Theorem R, the regime
  inequalities and the class-label bit function. The bit-free branch identity
  replaces the last of these for every doubled LEC. The artifact checks the
  forgetful step, the identity and the witness step exhaustively on toy 2-to-1
  games (10440 configurations, all pass).
