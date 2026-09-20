---
rg: 2
id: priority-ball-carvings-cannot-refute-hadamard-crossing
kind: claim
title: Random-priority pin-ball adversaries for Had_k -> Max-2Lin(2) have max-edge value K max_e Pr[cut] >= C* - o(1) with C* in (2.052, 2.053), so this whole adversary class cannot refute a Hadamard crossing of the padding line
distinct_from:
  hadamard-gadget-crosses-padding-line: that is the open statement R*(k) > 2; this rules out one natural class of adversaries (the extension of bubble/threshold carvings past radius K/4) as a refutation of it, and does not prove R*(k) > 2.
  hadamard-gadget-deletion-ratio-window: that proves upper bounds on R*(k) by explicit decoded adversaries; this proves a lower bound on the value of every adversary in a different class, as k -> infinity.
  hadamard-crossing-needs-folding-gap: that bounds R*(k) - K z_U by the folding gap of an optimal relaxed adversary; this concerns folded adversaries of a fixed shape and says nothing about z_U.
artifacts:
  - experiments/ugc-hadamard-priority-balls-2026-09-17/rigorous_threshold.py
  - experiments/ugc-hadamard-priority-balls-2026-09-17/equal_distance_ode.py
  - experiments/ugc-hadamard-priority-balls-2026-09-17/continuum_explore.py
  - experiments/ugc-hadamard-priority-balls-2026-09-17/continuum_minimax.py
  - experiments/ugc-hadamard-priority-balls-2026-09-17/results-2026-09-20.txt
---

**ESTABLISHED** (class obstruction). The proof is complete below. The only
numerical input is the exact-rational bracket of `C*` in
`rigorous_threshold.py`.

## Setting

The notation is that of `hadamard-gadget-deletion-ratio-window`.

* `K = 2^k` and `Q = {-1,1}^K`, with Hamming distance `d`.
* The pins are the `2K` points `+-chi_a`.
* Edges are `e = (x, x + e_j)`.
* The value of a distribution `mu` over folded assignments that is random on
  `P` is `val(mu) = K max_e Pr_mu[cut e]`.
* `R*(k)` is the least value. `hadamard-gadget-crosses-padding-line` is
  refuted exactly when some such `mu` has `val(mu) <= 2` for every `k`.

## The class `P_eta(k)`

Fix `eta` in `(0, 1/4)` and a law of a radius `r` on `{1, 2, ...}`.

* **Radius law.** Write `G(d) = Pr[r > d]`, so `G(0) = 1`. The support must
  satisfy `r <= (1/2 - eta) K`.
* **Sampling.** Sample independently:
  * a uniform sign `sigma_a` for each `a`;
  * a radius `r_a` of that law and a uniform priority `p_a` in `[0,1]` for
    each `a`, shared by the pins `chi_a` and `-chi_a`;
  * a backbone `(i, tau)`, uniform on `[K] x {+-1}`.
* **The ball.** The ball of pin `y = eps chi_a` is `B_y = {x : d(x, y) < r_a}`.
* **The label.** `A(x) = eps sigma_a` if `y = eps chi_a` is the
  top-priority pin whose ball contains `x`. If no ball contains `x`, then
  `A(x) = tau x_i`.

This is the natural continuation, beyond radius `K/4` and with random
overlaps, of the bubble and threshold carvings tried on the target node.
Those include common-radius half-cube bubbles and threshold adversaries.

**Lemma 0 (well defined, folded, random on P).**

* Two distinct characters are at distance `K/2 > r`. So `chi_a` lies only in
  its own ball, and `A(chi_a) = sigma_a` is uniform on `{-1,1}^P`.
* `x` lies in `B_{-y}` exactly when `-x` lies in `B_y`, which gives
  `A(-x) = -A(x)`.
* For `K > 1/eta`, no edge has one endpoint in `B_y` and the other in
  `B_{-y}`, because `d(x, y) + d(x', -y) >= K - 1 > 2r`.

## Theorem

Define the following.

* `y0(C) = 1 - C (1 - e^{-1/2})`.
* `phi(g) = (C - (1-g)^4) g / (1 - (1-g)^4)`, extended by `phi(0) = (C-1)/4`.
* `T(C) = int_0^{y0(C)} dy / (2 phi(y))`.

`T` is continuous and strictly decreasing on `[3/2, 2.5]`. Let `C*` be its
root of `T(C*) = 1/4`, and let `C_eta` be the root of `T(C_eta) = 1/4 - eta`,
so `C_eta > C*`.

**Theorem.** For every `eta`,
`liminf_{k -> infinity} inf_{mu in P_eta(k)} val(mu) >= C_eta > C*`.
Moreover `2.052 < C* < 2.053`, certified by exact rational arithmetic.
High-precision quadrature (mpmath) gives `C* ~ 2.052575`.

**Corollary.** No family of priority-ball adversaries, with any radius law
per `k` and any fixed `eta > 0`, has `val <= 2` for all large `k`. So this
class cannot refute `hadamard-gadget-crosses-padding-line`. The same holds
when `eta = eta_k -> 0` slowly (see Remark 2).

## Proof

### Lemma 1 (cut lower bound)

Take an edge `(x, x')`. For each pin pair `a`, fix the sign `eps` with
`d(x, eps chi_a) <= K/2`. Let `d_a^-` and `d_a^+` be the smaller and larger
of `d(x, eps chi_a)` and `d(x', eps chi_a)`; they differ by exactly `1`.
Then

    K Pr[cut] >= (K/2) sum_a (G(d_a^-) - G(d_a^+)) int_0^1 prod_{l != a} (1 - u G(d_l^-)) du
                 + prod_a (1 - G(d_a^-)).

*Proof.* Condition on the radii and priorities. By Lemma 0 the endpoint
labels are:

* independent uniform signs when the tops differ, where "top" is the
  top-priority claiming pin or the backbone. Distinct pairs carry
  independent `sigma` values, and `tau` is independent of all `sigma`;
* equal when the top is the same pin;
* `tau x_i` and `tau x'_i` when neither endpoint is claimed. These differ
  with probability exactly `1/K`.

So `Pr[cut] = (1/2) Pr[tops differ] + (1/K) Pr[no claim at either end]`.

* **The second term.** The union of the claim sets is `{a : r_a > d_a^-}`.
  So `Pr[no claim] = prod (1 - G(d_a^-))`.
* **The events `E_a`.** Let `E_a` be the event that `r_a` lies in
  `(d_a^-, d_a^+]` and that `p_a` exceeds `p_l` for every `l` with
  `r_l > d_l^-`.
  * On `E_a`, pin `a` is the top at its nearer endpoint, and it is absent at
    the farther one. So the tops differ.
  * The events `E_a` are disjoint, because `a` is then the top of the union
    of the claim sets.
  * Integrating over `p_a = u` gives the displayed term. QED.

### Lemma 2 (two families of edges)

Call a pin *far* from `x` when `d(x, eps chi_a) >= (1/2 - eta) K + 1` for both
signs. A far pin has `G(d^-) = 0` at every edge through `x`. Let
`Delta = 4 sqrt(K log(4K))`, and assume `K` is so large that
`Delta + 2 < eta K`.

* **(a) One near pin.** For every `a` and every `d <= (1/2 - eta) K`, there
  is an edge with `d_a^- = d`, `d_a^+ = d + 1`, and all other pins far.
* **(b) Four near pins.** Fix any `L : F_2^k -> F_2^2` onto, and write
  `f(u) = (-1)^{u_1 u_2}`. Put `x(i) = f(L i)`.
  * **The four near characters.** By the Walsh expansion
    `f = (1 + chi_{e1} + chi_{e2} - chi_{e1+e2})/2`, the vector `x` is at
    distance `K/4` from four pins:
    `chi_0`, `chi_{L^T e1}`, `chi_{L^T e2}` and `-chi_{L^T(e1+e2)}`.
  * **All other characters.** `x` is at distance exactly `K/2` from every
    other character.
  * **The fibers.** On each fiber `L^{-1}(u)`, of size `K/4`, exactly one of
    the four pins disagrees with `x`. Indeed `f(u)` is half the sum of the
    four `+-1` values there, so three of them agree with `f(u)`.
  * **The flips.** Flip `s` coordinates in each fiber, with
    `1 <= s <= K/4 - 1`, to get `x~`. Each of the four pins loses `s` in its
    own fiber and gains `3s` elsewhere. So all four are at distance
    `D = K/4 + 2s`.
  * **Type U.** An edge `(x~, x~ + e_j)` with `j` unflipped in some fiber
    moves three of the four pins `D -> D+1` and one `D -> D-1`.
  * **Type F.** An edge with `j` flipped moves one pin `D -> D+1` and three
    `D -> D-1`.
  * **The other pins.** For `D <= (1/2 - eta) K + 1`, the flip sets can be
    chosen so that every other pin is far from `x~`.

*Proof of the far claims.*

* **In (a).** Take `x = chi_a + F` with `F` a uniform `d`-subset. For
  `b != a`, `d(x, chi_b) - K/2 = |F cap Agr_b| - |F cap Dis_b|`, where the
  agreement set `Agr_b` of `chi_a` and `chi_b` has size `K/2`. This is a
  centred hypergeometric deviation. By Hoeffding's inequality for sampling
  without replacement, it exceeds `Delta/2` in absolute value with
  probability below `1/(2K)`.
  * A union bound over `b` leaves some `F` with all `|d - K/2| <= Delta/2`.
  * Add a direction `j` not in `F`. This moves every distance by exactly `1`.
* **In (b).** For `b` outside the image of `L^T`, `chi_b` is balanced on
  every coset of `ker L`, while `x` is constant there. So `x` agrees with
  `chi_b` on exactly half of each fiber.
  * Choose the flip set as independent uniform `s`-subsets of the four
    fibers. The deviation is then a sum of four independent centred
    hypergeometric deviations, and the same Hoeffding and union bound apply.
  * Both flipped and unflipped directions exist in every fiber, because
    `1 <= s <= K/4 - 1`. QED.

### Lemma 3 (discrete rate constraints)

Let `C = val(mu)`. Since every constraint below weakens as `C` grows, we may
assume `C >= 3/2`. Then:

* **(S)** For `0 <= d <= (1/2 - eta) K`:
  `G(d) - G(d+1) <= (2/K) (C - 1 + G(d))`.
* **(Q)** For `D = K/4 + 2s` with `s >= 1` and `D - 1 <= (1/2 - eta) K`:
  `G(D-1) - G(D+1) <= (4/K) phi(G(D-1))`.

*Proof.*

* **(S).** Apply Lemma 1 to edge (a). The integral is `1` and the product
  is `1 - G(d)`.
* **(Q).** Put `g = G(D-1)`. On both edge types, every near pin has `d^-` in
  `{D-1, D}`, so `G(d^-) <= g`. Each integral is therefore at least
  `J = int_0^1 (1 - u g)^3 du = (1 - (1-g)^4)/(4g)`, and the product is at
  least `(1-g)^4`.
  * **Type U** gives
    `C >= (K/2) J [3(G(D) - G(D+1)) + (G(D-1) - G(D))] + (1-g)^4`.
  * **Type F** gives
    `C >= (K/2) J [(G(D) - G(D+1)) + 3(G(D-1) - G(D))] + (1-g)^4`.
  * Averaging the two telescopes to `C >= K J (G(D-1) - G(D+1)) + (1-g)^4`.
    Rearranged, this is (Q). QED.

### Lemma 4 (facts about phi)

For `C >= 1` and `g` in `[0,1]`:

* **The form of phi.** `phi(g) = (C - (1-g)^4) / p(g)`, where
  `p(g) = 4 - 6g + 4g^2 - g^3`. `p` decreases from `4` to `1`.
* **Monotone and Lipschitz.** `phi` is nondecreasing, smooth and Lipschitz,
  with `phi >= (C-1)/4`.
* **Below the one-pin rate.** `phi(g) <= C - 1 + g`, because
  `(1 - (1-g)^4)(C - 1 + g - phi) = (C-1)(1 - (1-g)^4 - g) >= 0`.

Consequently, in (Q) the four-pin rate is the binding one. Two steps of (S)
would only give `(4/K)(C - 1 + G(D-1))`.

### Lemma 5 (descent time), and the proof of the theorem

Suppose `C` lies in `[3/2, 5/2]`; the case `C > 5/2` is trivial. The
constants `c_i` below depend on nothing but this range.

**Step 1: the one-pin phase, `d < K/4`.**

* Let `F1(g) = int_g^1 dy / (2(C - 1 + y)) = (1/2) ln(C/(C - 1 + g))`.
* By (S) and the monotonicity of the rate, each step satisfies
  `F1(G(d+1)) - F1(G(d)) <= (G(d) - G(d+1)) / (2(C - 1 + G(d+1)))`.
* This is at most `(1/K)(C - 1 + G(d)) / (C - 1 + G(d+1))`, which is at most
  `(1/K)(1 + 6/K)`.
* Summing over `K/4` steps gives `F1(G(K/4)) <= 1/4 + 2/K`.
* Hence `G(K/4 + 1) >= y0(C) - c1/K`.

**Step 2: the four-pin phase.**

* Let `n_j = K/4 + 1 + 2j`, and let `J` be the first `j` with `G(n_j) = 0`.
  It exists because `G` vanishes from `(1/2 - eta) K` on.
* For each `j < J`, (Q) applies with `D - 1 = n_j`.
* Let `F(g) = int_g^1 dy / (2 phi(y))`. By Lemma 4 (`phi` nondecreasing,
  Lipschitz, and at least `1/8`):
  `F(G(n_{j+1})) - F(G(n_j)) <= (2/K) phi(G(n_j)) / phi(G(n_{j+1})) <= (2/K)(1 + c2/K)`.
* Telescoping, and using `2J <= (1/4 - eta) K + 1`, gives
  `int_0^{G(n_0)} dy / (2 phi) <= 1/4 - eta + c3/K`.

**Step 3: combining the phases.** The integrand is at most `2/(C-1) <= 4`.
With Step 1 this gives `T(C) <= 1/4 - eta + c4/K`.

**Conclusion.** `T` is continuous and strictly decreasing: `y0` decreases in
`C`, and `phi` increases in `C`. So
`val(mu) >= T^{-1}(1/4 - eta + c4/K) -> C_eta` as `K -> infinity`,
uniformly over `P_eta(k)`.

**The value of `C*`.** `rigorous_threshold.py 2.052 2.053 3000` certifies
`T(2.052) > 1/4 > T(2.053)`. It uses exact rational Riemann sums, with the
monotone integrand `1/(2 phi)` summed by left and right endpoints, and a
rational bracket of `e^{-1/2}`. The output is in `results-2026-09-20.txt`.
QED.

## Remarks

1. **Where the class dies.** The invariant is the Parseval-tight plateaued
   point `x = f o L`, with `f = u1 u2` bent on `F_2^2`, together with its
   uniform per-fiber flips.
   * These points keep four pins exactly equidistant along the whole range
     `D` in `[K/4, K/2)`, with every other pin out of reach.
   * Priority sharing among the four pins then caps the radius hazard at
     `-g'/2 <= phi(g)`, where `phi(0) = (C-1)/4`. That is four times slower
     than the one-pin cap `C - 1 + g`.
   * The radius law cannot die out before `K/2` unless `C >= C* > 2.052`.
2. **Letting `eta` shrink.** The proof needs only
   `eta_k K > 4 sqrt(K log 4K) + 2`. So it also covers `eta_k -> 0` with
   `eta_k >> sqrt(log K / K)`, and gives `liminf val >= C*`.
3. **Stronger heuristic values.** These are floating point and not claimed.
   * With `M = 4^m` pins, from bent `f` on `F_2^{2m}` (all equidistant),
     `equal_distance_ode.py pow4` gives a threshold of about `2.2528`.
     Rigorously, the flip lattice for `m >= 2` has step `2^m`, so the
     constraint then covers only some consecutive pairs.
   * Allowing all `M <= (1-2s)^{-2}` gives about `2.3` to `2.4`.
   * The continuum minimax (`continuum_minimax.py`) finds a best profile of
     about `2.64`.
4. **Not covered by this node.** It says nothing about:
   * pin-dependent radius laws, radii correlated across pins, or
     non-uniform priorities;
   * radius laws that depend on `x` beyond distance;
   * decoders or list decoders mixed with balls;
   * any adversary with `eta = 0` in an essential way.
   * It also does not prove `R*(k) > 2`.
   * The natural next target is the per-pin version: in (Q), average over
     the four fibers and control the average of the four laws by the
     largest one.
