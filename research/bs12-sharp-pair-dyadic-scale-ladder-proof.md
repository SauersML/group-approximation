---
rg: 2
id: bs12-sharp-pair-dyadic-scale-ladder-proof
kind: route
title: Telescoping Livsic gauge exp(-is sum_{k<K} H_(2^k)) turns A_s into W e^(isH_(2^K)) and moves D by 4 pi s(2^K-1)/N; functional calculus of an exact base gives colouring twists
target: bs12-sharp-pair-dyadic-scale-ladder
requires: []
artifacts:
  - experiments/bs12-twistfree-base-census-2026-09-17/ladder_check.py
  - experiments/bs12-twistfree-base-census-2026-09-17/ladder_check_out.txt
  - experiments/bs12-twistfree-base-census-2026-09-17/census_tf.py
---

This is a lane proof (swarm-0917-w16, 2026-09-19), not reviewed. It is
self-contained, and its notation is that of the target.

**Item 1.**

1. **Conjugating by W.** `W^* e_k = e_(2k)`, so `W^* V W = V^2`, and
   therefore `W^* f(V) W = f(V^2)`.
2. **The gauge.** Put `Y = -s sum_{k<K} H_(2^k)` and `h = e^(iY)`. Functions
   of `V` commute, so
   ```text
   h^* A_s h = W e^(-iY(V^2)) e^(isH_1) e^(iY(V)) = W e^(isH_(2^K)),
   ```
   because the exponent telescopes.
3. **The base moves little.** From `D V D^* = wV` we get
   `||h^*Dh - D|| = ||e^(iY(wV)) - e^(iY(V))|| <= ||Y(wV) - Y(V)||`.
   This is at most `(2pi/N) sup|y'|`, where
   `y(t) = -2s sum_{k<K} cos(2^k t)`, and `sup|y'| <= 2s(2^K - 1)`.
4. **Comparing distances.** Conjugation by `h` is an isometric bijection of
   the set of exact pairs, which gives the inequality
   `|d - d_R| <= 4 pi s (R-1)/N`.
5. **The second identity.** Let `sigma_R e_j = e_(Rj)`. It is unitary for odd
   `N`, it commutes with `W`, and it satisfies `sigma_R^* V^R sigma_R = V`
   and `sigma_R^* D sigma_R = D^R`.

**Item 2.**
- **Colouring twists exist.** Suppose `C Z C^* = Z^2`. Then
  `spec Z = spec Z^2`, so squaring permutes the finite set `spec Z`. For a
  colouring `f`, functional calculus gives
  `C f(Z) C^* = f(CZC^*) = f(Z^2)`. Since `f(lambda^2) = f(lambda)^2` on
  `spec Z`, we get `f(Z^2) = f(Z)^2`. Also `f(Z)^3 = 1`.
- **Existence on an orbit.** Take an orbit `lambda, lambda^2, ...` of length
  `L`. A colouring on it is determined by `c = f(lambda)`, and it closes up
  if and only if `c^(2^L) = c`. For `c != 1` this holds if and only if
  `2^L = 1 (mod 3)`, that is, if and only if `L` is even.
- **The listed orders.** The orbit lengths on `Z/M` are `ord_d(2)` for
  `d | M`, `d > 1`. For the examples in the claim:
  - `ord_25 = 20` and `ord_5 = 4`;
  - `ord_11 = 10` and `ord_13 = 12`;
  - `ord_7 = 3`, `ord_23 = 11`, `ord_31 = 5`, `ord_47 = 23`, `ord_73 = 9`.

**Item 3** is the computation recorded in the target. Every reported pair
is exact up to 4e-14, so each number is an upper bound for its base class.
