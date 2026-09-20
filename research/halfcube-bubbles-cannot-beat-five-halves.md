---
rg: 2
id: halfcube-bubbles-cannot-beat-five-halves
kind: claim
title: Undecoded half-cube bubble adversaries (i, tau independent of xi, common flip radius t with any law on [0, K/2)) cannot beat the five-halves cap - their optimum is exactly 5/2 - 2^(1-k) for k = 3, 4, 5, attained by the uniform law on t < K/4, because multi-pin equidistant points charge every radius beyond K/4 at full rate
distinct_from:
  hadamard-gadget-deletion-ratio-window: that proves R*(k) <= 5/2 - 2^(1-k) with one explicit adversary; this shows that the whole one-parameter-law family containing it, with flip radii up to K/2, has the same optimum at k = 3, 4, 5, so no radius law improves the cap without decoding.
  hadamard-crossing-needs-folding-gap: that bounds R*(k) above by relaxed value plus folding gap; this is a lower bound on a family of folded adversaries and says nothing about R*(k) itself.
  hadamard-gadget-crosses-padding-line: that is the open statement R*(k) > 2; this kills one candidate route to refuting it (an undecoded adversary below 2), not the statement.
artifacts:
  - experiments/ugc-hadamard-halfcube-bubbles-2026-09-17/halfcube_price.py
  - experiments/ugc-hadamard-halfcube-bubbles-2026-09-17/halfcube_price.c
  - experiments/ugc-hadamard-halfcube-bubbles-2026-09-17/halfcube_price_ld.c
  - experiments/ugc-hadamard-halfcube-bubbles-2026-09-17/brute_check.py
  - experiments/ugc-hadamard-halfcube-bubbles-2026-09-17/crosscheck.py
  - experiments/ugc-hadamard-halfcube-bubbles-2026-09-17/cert_dual.py
  - experiments/ugc-hadamard-halfcube-bubbles-2026-09-17/lp_file.py
  - experiments/ugc-hadamard-halfcube-bubbles-2026-09-17/limit_model_lp.py
  - experiments/ugc-hadamard-halfcube-bubbles-2026-09-17/limit_binding.py
  - experiments/ugc-hadamard-halfcube-bubbles-2026-09-17/results-2026-09-19.txt
---

**ESTABLISHED for k = 2, 3, 4, 5** (exact rational certificates plus the
five-halves theorem). **Numerical only for k = 6, 7.** The limit statement
is OPEN.

## Setting

Notation is that of `hadamard-gadget-deletion-ratio-window`: `K = 2^k`,
characters `chi_a` on `F_2^k`, Walsh coefficients `W_a(x) = sum_z x_z chi_a(z)`,
length-one edges `(x, x^j)`, where `x^j` flips coordinate `j`. The cost of a
distribution `A` is `max_e K Pr[A cuts e]`, and `R*(k)` is the least cost of a
folded `A` that is random on the pins, meaning `A(sigma chi_a) = sigma xi_a`
with `xi` uniform.

**The family.** Draw `i` uniform in `F_2^k`, `tau` uniform in `{+-1}` and a
uniform random subset `B` of the characters, all independent. Put
`xi_a = tau chi_a(i)` for `a` not in `B` and `xi_a = -tau chi_a(i)` for `a`
in `B`, so `xi` is uniform. Let

    e_a(x) = (K - x_i chi_a(i) W_a(x)) / 2.

This is the distance from `x` to the signed pin `x_i chi_a(i) chi_a`, which is
the pin of index `a` that lies in the half-cube `{z : z_i = x_i}`. For a
radius `t` with `0 <= t < K/2`, set

    H_t(x) = -tau x_i   if  min_{a in B} e_a(x) <= t,
    H_t(x) =  tau x_i   otherwise.

A law `q` on `{0, ..., K/2 - 1}` gives the mixture `H_q`. Write `HC(k)` for
the least cost of `H_q` over all laws `q`.

* **Folded.** `e_a(-x) = e_a(x)`, so `H_t(-x) = -H_t(x)`.
* **Random on the pins.** At `x = sigma chi_a` we get `e_a = 0`, and
  `e_b = K/2 > t` for `b != a`. So `H_t` flips exactly when `a` is in `B`,
  which gives `H_t(sigma chi_a) = sigma xi_a`.
* **Undecoded.** The pair `(i, tau)` is independent of `xi`, so the
  disagreement rate is `delta = 1/2`. This is the regime of item 3 of the
  window node with `delta = 1/2`.
* **Price.** Fix an edge `(x, y = x^j)` and a coordinate `i`. Put
  `S_x = {a : e_a(x) <= t}`, the same set for `y`, and `U = S_x ∪ S_y`.
  Then `Pr[cut | i]` is
  * `2^-|S_x| + 2^-|S_y| - 2 * 2^-|U|` when `i != j`, where exactly one
    endpoint flips;
  * `1 + 2 * 2^-|U| - 2^-|S_x| - 2^-|S_y|` when `i = j`, where `x_i != y_i`,
    so the edge is cut when both or neither flip.

  The price `C_t(e) = K Pr[H_t cuts e]` is `sum_i Pr[cut | i]`, and
  `K Pr[H_q cuts e] = sum_t q_t C_t(e)`.
  * These formulas and the two properties above are checked against the bare
    definition at `k = 3` by `brute_check.py`. It enumerates every `t`,
    every `x`, every edge and every `(i, tau, B)`.
  * The integer C pricer agrees with the Fraction pricer on every edge class
    at `k = 2, 3, 4`, by `crosscheck.py`.

## Theorem

1. **The five-halves adversary is a member.** The uniform law on
   `t in {0, ..., K/4 - 1}` is the adversary of the window node's item 2. So
   `HC(k) <= 5/2 - 2^(1-k)` for every `k`.
2. **Exact optimum for k = 3, 4, 5.** `HC(3) = 9/4`, `HC(4) = 19/8` and
   `HC(5) = 39/16`. That is, `HC(k) = 5/2 - 2^(1-k)`: no law on radii up to
   `K/2` improves on the five-halves law. At `k = 2`, `HC(2) = 13/8`, attained
   at `t = 1 = K/4` (there `5/2 - 2^(1-k) = 2`). This case is degenerate,
   since every `x` in `{-1,1}^4` is within distance 1 of a pin.
3. **Numerics for k = 6, 7.** The cutting-plane LP at `k = 6` and the
   fixed-edge LP at `k = 7` give the values recorded in
   `results-2026-09-19.txt` and summarized under "Evidence beyond k = 5"
   below. They are lower bounds on `HC(k)` up to floating-point error. They
   approach `5/2 - 2^(1-k)`, and no law beating it was found.

## Proof of items 1 and 2

**Item 1.** The window node's item-2 adversary has `tau = +1`, with `i`
uniform and independent of `xi`, and a threshold `s` uniform on `[0, K/4]`.
`x` is corrected toward its closest signed pin `sigma chi_p` exactly when
`d(x, sigma chi_p) < s` and `xi_p != chi_p(i)`. Otherwise it outputs `x_i`
(see `check_five_halves_adversary.py`).

* **The near pin is unique.** Two distinct signed characters are at distance
  `K/2` or `K`. So at most one pin has `e_a(x) < K/4`.
* **The correction matches.** The corrected output is `sigma xi_p = -x_i`
  when the pin lies in `x`'s half, and it equals `x_i` otherwise. This is
  exactly a flip of `H_t` with `p` in `B`.
* **The flip probabilities match.** `Pr_s[d < s] = (K/4 - d)/(K/4)`, which
  equals `Pr_t[d <= t]` for `t` uniform on `{0, ..., K/4 - 1}`.
* **The sign of tau does not matter.** Replacing `tau` by `-tau` maps a law
  to its negation composed with `xi -> -xi`. That map preserves every cut
  probability and the uniformity of `xi`.

So the two adversaries have identical edge prices, and the window node's
item 2 gives `HC(k) <= 5/2 - 2^(1-k)`.

**Item 2 (lower bound).** Weak duality for the minimax LP: if `y` is a
probability vector on edge classes with `sum_e y_e C_t(e) >= z` for every `t`,
then for every law `q`,

    max_e sum_t q_t C_t(e)  >=  sum_e y_e sum_t q_t C_t(e)  >=  z.

`cert_dual.py` builds such a `y` in exact rationals, from integer prices
(`K Pr[cut]` times `2^K`, which is exact). It verifies
`min_t (y C)(t) = z` in `Fraction` arithmetic.

| `k` | `z` | support | edge classes used |
|---|---|---|---|
| 2 | `13/8` | 1 | the single class (all `x` equivalent) |
| 3 | `9/4` | 2 | exhaustive (`halfcube_price.c` mode `all`) |
| 4 | `19/8` | 5 | exhaustive (mode `all`) |
| 5 | `39/16` | 13 | structured and near-pin classes (modes `struct`, `near`) |

The weights are printed in `results-2026-09-19.txt`. Together with item 1,
this gives `HC(k) = 5/2 - 2^(1-k)` for `k = 3, 4, 5` and `HC(2) = 13/8`.

* **How far the certificate depends on the pricer.** Each weight sits on a
  price vector that `halfcube_price.c` printed for a concrete edge. The
  closed form behind that pricer is checked against the bare definition at
  `k = 3` (`brute_check.py`: 0 folding violations, 0 pin violations and 0
  price mismatches over all `t`, `x`, `j`, `i`, `tau` and `B`). The C and
  Fraction pricers also agree class for class at `k <= 4`.

## The obstruction (named failing step)

The failing step of "extend the radius law past `K/4` to buy a lower cost"
is the **equidistant multi-pin invariant**.

* **Where the dual mass sits.** The `k = 5` certificate puts its weight on
  points `x` whose Fourier mass lies on the span of `m <= 4` characters,
  that is `x_i = f(i mod 2^m)`, and on points near one pin.
* **Codimension-m cosets.** A pin with a codimension-`m` coset flipped has
  one pin at distance `d = K/2^m` and `2^m - 1` pins at distance `K/2 - d`.
* **Bent points.** A bent point on a 2-dimensional span has 4 pins, all at
  distance `K/4`.
* **Why such points are expensive.** At such an `x`, a radius `t` above the
  common pin distance makes `Pr[some bad pin is active] = 1 - 2^-(#pins)`
  close to 1. The flip of `H_t` is then decided by the edge crossing the
  common distance level, and every `t` beyond that level is paid at full
  rate `~ K/2` times its mass, on the edges that move `x` across it.
* **The consequence.** Combined with the single-pin edges, which force
  `q_t <= ~2/K` pointwise below `K/4`, this leaves no room. The optimum is
  the uniform law on `[0, K/4)`, with every other radius at `0`.
* **The same picture in the K -> infinity model.** The heuristic limit LP
  (`limit_model_lp.py`, `limit_binding.py`) has binding configurations with
  pin-distance multisets
  * `(3/16, 5/16 x3, 7/16 x12)`;
  * `(1/8, 3/8 x7)`;
  * `(1/4 x4)`;
  * `(1/16, 7/16 x15)`;
  * a single pin.

  Its value climbs `1.63, 1.81, 2.53` for `m <= 2, 3, 4`. This is only
  heuristic, since the grid step is `h = 1/16`.

## Evidence beyond k = 5

* **k = 6.** A cutting-plane LP was run with the long-double pricer. It
  alternates the minimax LP with a hill-climbing separation oracle
  (`halfcube_price_ld.c` mode `climb`). It converged to `2.46875 = 79/32 =
  5/2 - 2^(1-6)` on 6608 edge classes, with `q` uniform on `t < 16 = K/4`,
  and further climbs found no violating edge. This is numerical only: the
  exact-integer rerun had reached `2.4413` when this node was written, and
  no rational certificate was completed.
* **k = 7.** A fixed edge set of 12700 classes gives only `2.0778`. It is a
  weak lower bound, the cutting plane did not converge, and it decides
  nothing.
