---
rg: 2
id: dense-link-square-selectors-reduce-to-base-orientations-proof
kind: route
title: Pivot proof of the square transfer Q, its converse Q', and the RP kill of 2-to-2 selectors on dense-link squares of rigid doubled LECs
target: dense-link-square-selectors-reduce-to-base-orientations
requires:
  - near-perfect-selectors-die-on-every-rigid-doubled-lec
  - orientation-lifts-sandwich-2to1-game-values
  - dkkms-certified-parameters-lie-in-the-selector-kill-regime
artifacts:
  - experiments/ugc-square-transfer-2026-09-17/check_square_transfer.py
---

Notation is as in the target claim. Only elementary counting is used, apart from
Theorem S\* (for Q1) and its DKKMS corollary with the certified-point closure
(for Q2).

## Proof of Theorem Q

Fix a left labelling `A`. For `e` write `sigma_e = A(p_e)`,
`tau_e = pi_e(sigma_e)` and `beta_e = r_e(sigma_e)`. Fix `q`, and let `xi_q` be
the `J_q`-mass of pairs `(e1, e2)` that `U_kappa` rejects under `A`. Then
`E_(q ~ nu) xi_q = xi`. All the quantities below live in `star(q)`. It is
enough to find a right label `B(q)` whose rejected `mu_q`-mass in `U_o` is at
most `13 xi_q / alpha^3`, and then average over `q`.

**Step 1 (one block).** Let `p_tau = mu_q{ e : tau_e = tau }`, let `tau_q`
maximise `p_tau`, and let `bad = { e : tau_e != tau_q }`. Pairs with
`tau_(e1) != tau_(e2)` are rejected, and all of them are off the diagonal. So

```text
xi_q  >=  J_q{ tau_(e1) != tau_(e2) }  >=  alpha (1 - sum_tau p_tau^2)
      >=  alpha (1 - max_tau p_tau)  =  alpha mu_q(bad),
```

using `sum p_tau^2 <= max p_tau`. Hence `mu_q(bad) <= xi_q / alpha`.

**Step 2 (the bits beta are nearly a kbar-potential).** Write
`kb = kbar^(tau_q)`. Call a pair *beta-bad* if
`beta_(e1) xor beta_(e2) != kb(e1, e2)`. Diagonal pairs are never beta-bad,
because `kb(e, e) = 0`. An off-diagonal pair with both ends good is beta-bad
only if `U_kappa` rejects it, since there `kb = kappa^(tau_q)`. A pair with a
bad end has `J_q`-mass at most `2 mu_q(bad)`, because both marginals are
`mu_q`. So

```text
J_q(beta-bad)       <=  xi_q + 2 xi_q / alpha  <=  3 xi_q / alpha,
(mu_q x mu_q)(beta-bad)  <=  J_q(beta-bad) / alpha  <=  3 xi_q / alpha^2,
```

where the second line uses density off the diagonal and the absence of diagonal
beta-bad pairs.

**Step 3 (a good pivot exists, and the chosen one is as good).** For a pivot
`e*`, let `D(e*) = { e : g_(e*)(e) != beta_(e*) xor beta_e }`, with
`g_(e*) = g^(tau_q)_(e*)`. Then `e in D(e*)` iff `(e*, e)` is beta-bad. So

```text
E_(e* ~ mu_q) mu_q(D(e*))  =  (mu_q x mu_q)(beta-bad)  <=  3 xi_q / alpha^2,
```

and some `e*` has `mu_q(D(e*)) <= 3 xi_q / alpha^2`. Outside `D(e*)`,
`g_(e*)(e) = beta_(e*) xor beta_e`. So for a pair with both ends outside
`D(e*)`, `g_(e*)(e1) xor g_(e*)(e2) = beta_(e1) xor beta_(e2)`. Such a pair is
`g`-bad (that is, `g(e1) xor g(e2) != kb(e1, e2)`) iff it is beta-bad. Hence

```text
J_q(g_(e*)-bad)  <=  J_q(beta-bad) + 2 mu_q(D(e*))  <=  3 xi_q/alpha + 6 xi_q/alpha^2  <=  9 xi_q / alpha^2.
```

The algorithm picks the pivot that maximises `V`, that is, the one minimising
`J_q(g-bad)`. It does not need to know `A`. So the chosen `g = g_(q, tau_q)`
also has `J_q(g-bad) <= 9 xi_q / alpha^2`.

**Step 4 (the orientation bits are nearly constant).** Put
`f(e) = beta_e xor g(e)`. If `f(e1) != f(e2)` then
`beta_(e1) xor beta_(e2) != g(e1) xor g(e2)`, so the pair is beta-bad or
`g`-bad. Thus `J_q{ f(e1) != f(e2) } <= 12 xi_q / alpha^2`. Diagonal pairs
never disagree, so by density
`(mu_q x mu_q){ f(e1) != f(e2) } <= 12 xi_q / alpha^3`. With
`p = mu_q{ f = 1 }`, the left side is `2 p (1 - p) >= min(p, 1 - p)`. So some
`b* in {0,1}` has `mu_q{ f != b* } <= 12 xi_q / alpha^3`.

**Step 5 (right label).** For a good `e`, `pi_e(sigma_e) = tau_q`, so
`o_e(sigma_e) = r_e(sigma_e) xor g_(q, tau_q)(e) = f(e)`. Put
`B(q) = (tau_q, b*)`. `U_o` accepts `e` iff `e` is good and `f(e) = b*`. The
rejected `mu_q`-mass is at most

```text
xi_q / alpha + 12 xi_q / alpha^3  <=  13 xi_q / alpha^3      (alpha <= 1).
```

Averaging over `q ~ nu` gives `val_(U_o)(A, B) >= 1 - 13 xi / alpha^3`. Taking
`A` optimal for `U_kappa` gives the `opt` form. QED.

## Proof of Theorem Q'

In each block `tau` of the pair `(e1, e2)`, the two elements of each fibre have
different `o`-bits. So "match the elements with equal `o`-bit" is a perfect
matching of the block, and `kappa(o)` is a matching selection. Its unique game
accepts `(sigma1, sigma2)` iff
`pi_(e1)(sigma1) = pi_(e2)(sigma2)` and `o_(e1)(sigma1) = o_(e2)(sigma2)`.

Let `(A, B)` be optimal for `U_o`, with `B(q) = (tau_q, b_q)`, and let `eta_q`
be the rejected `mu_q`-mass at `q`. Call `e` *agreeing* if
`(pi_e(sigma_e), o_e(sigma_e)) = (tau_q, b_q)`. If both ends of a pair agree,
`U_(kappa(o))` accepts it under `A`. The marginals of `J_q` are `mu_q`, so the
pairs with a disagreeing end have `J_q`-mass at most `2 eta_q`. Averaging,
`val_(U_(kappa(o)))(A) >= 1 - 2 (1 - opt(U_o))`. QED.

The map `o -> kappa(o)` is computed in polynomial time, and it needs no density.
So Q' holds for every coupling.

## Proof of Corollary Q1

Let `S2` be the 2-to-2 selector. Define the orientation selector `S` on input
`x`: compute `D(x)` and `J(x)`, run `S2` to get `kappa`, and output the pivot
orientation `o(kappa)` of `G(x)`. It runs in randomized polynomial time,
because the pivot is deterministic and polynomial.

On a YES input, with probability at least `theta`,
`opt(U_kappa) >= 1 - alpha^3 xi / 13`. By Theorem Q, on that event
`opt(U_(S(x))) >= 1 - 13 (alpha^3 xi / 13) / alpha^3 = 1 - xi`. So `S` meets the
selector hypothesis of Theorem S\* in
`near-perfect-selectors-die-on-every-rigid-doubled-lec` with the same `xi` and
`theta`. The hypotheses (E), (M=), (Rig) and (S) are hypotheses on `D` alone,
and they are assumed. Theorem S\* gives `Lang in RP`, with one-sided success
probability at least `theta p0^2 c1 / 2` per trial. QED.

## Proof of Corollary Q2

The derived 2-to-2 constraint of the folded DKKMS game, as described in
`grassmann-composed-2to2-coarsenings-are-satisfiable`, joins two members sharing
a B-vertex `(V, L')` and accepts iff their unfolded labels agree on `L'`. The
2-to-1 constraint `pi_e` of `G_folded` is exactly "restrict the unfolded label
to `L'`". So the derived constraint at `(e1, e2)` is
`pi_(e1)(sigma1) = pi_(e2)(sigma2)`, the square constraint. With the natural law
(a B-vertex, then two independent constraints at it) the coupling is
`mu_q x mu_q`. Its marginals are `mu_q`, and it has `alpha = 1`.

By the DKKMS corollary of Theorem S\*, the folded DKKMS doubled LEC satisfies
(E), (M=), (Rig(10^(-5), 1/128, 1/16, 1/64)) and (S) with `K = K' = 1` at every
point of the Theorem S regime. By `dkkms-certified-parameters-lie-in-the-selector-kill-regime`,
every DKKMS-certified point with soundness below `1/16` lies in that regime.
Corollary Q1 with `alpha = 1` and `xi = 10^(-5)` gives the claim. For another
coupling with marginals `mu_q` that is alpha-dense, the threshold becomes
`10^(-5) alpha^3 / 13`. QED.

## Obstruction remark (no proof obligation)

The subdivision `Sub(H)` in the target is a dense-link presentation with
`alpha = 1` of every 2-to-2 game `H`. For it, Theorem Q holds, but (E) fails,
since each star has two edges. So nothing about general 2-to-2 hardness follows
from Q alone. The kill needs the base to satisfy the rigid-LEC hypotheses.

## Artifact

`experiments/ugc-square-transfer-2026-09-17/check_square_transfer.py` checks Q
and Q' by brute force. It exhausts all left labellings on 3000 random
instances, and it exits 0 with
`all 241467 checks pass; worst observed alpha^3 (1-val_o)/xi at xi<0.1: 1.333 (bound 13)`.
