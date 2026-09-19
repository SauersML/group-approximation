---
rg: 2
id: hadamard-certificates-blind-below-planes
kind: claim
title: Pin-moment hierarchy for the Hadamard minimax - certificates for R*(k) that use only t-wise statistics of the adversary's pin pattern cap at R_t(k), with R_3(k) <= 1 for every k (signed dictators are 3-wise uniform on the pins), R_{2^{r+1}-1}(k) <= min over RM(r,k)-cosets, and at k = 3 exactly R_4 = ... = R_7 = 21/16 < 11/8 = R*(3), so the whole k = 3 gain over 21/16 comes from the global 8-pin parity
distinct_from:
  hadamard-crossing-needs-folding-gap: that measures folded versus unfolded f; this is orthogonal, since the hierarchy is defined for folded adversaries and relaxes the law of the pin pattern xi instead of f (unlike the w17 odd-walk / metric cap and the w19 half-cube bubble kill, which concern f and adversary families).
  hadamard-gadget-crosses-padding-line: that is the open statement R*(k) > 2; this says which certificates cannot prove it and splits R*(k) over code cosets.
artifacts:
  - experiments/ugc-hadamard-pin-moment-hierarchy-2026-09-17/pin_moment_k3.py
  - experiments/ugc-hadamard-pin-moment-hierarchy-2026-09-17/scan_k3.py
  - experiments/ugc-hadamard-pin-moment-hierarchy-2026-09-17/verify_k3.py
  - experiments/ugc-hadamard-pin-moment-hierarchy-2026-09-17/results-2026-09-19.txt
---

**ESTABLISHED.** Items 1 to 4 are proved below. Item 5 is an exact
computation: `verify_k3.py` checks the certificate and the adversary
in rational arithmetic, with integer min cuts.

## Setting

The notation is that of `hadamard-gadget-deletion-ratio-window`.

* `K = 2^k` and `Q = {-1,1}^K`.
* The pins are `chi_a(j) = (-1)^(a.j)` for `a, j` in `F_2^k`.
* The edges are the length-one edges `e = (x, x + e_j)`.
* A folded adversary is a random folded `f : Q -> {-1,1}`. Its pin pattern is
  `xi = (f(chi_a))_a`, which lies in `{-1,1}^K`.
* `R*(k) = K min_D max_e Pr_D[f cuts e]`, where the minimum is over folded `D`
  whose pattern is uniform on `{-1,1}^K`.

**Definitions.**

* **The pin-moment relaxation.** For `1 <= t <= K`, `R_t(k)` is the same
  minimax, but taken over folded `D` whose pattern law is only *t-wise
  uniform*. That means `E_D[prod_{a in S} xi_a] = 0` for every nonempty `S`
  with `|S| <= t`.
* **The coset values.** For a set `C` of patterns, `R_C(k)` is the minimax
  over folded `D` whose pattern is uniform on `C`.
* **Pin-degree.** By LP duality (item 1 of `hadamard-gadget-deletion-ratio-window`),
  a lower-bound certificate is a pair `(w, phi)`:
  * `w` is a probability weighting of the edges;
  * `phi` is a price on patterns with uniform mean 0;
  * its value is `K min_f (E_w[cut_f] - phi(xi_f))`, taken over folded `f`.

  Its *pin-degree* is the Fourier degree of `phi`, that is, the largest
  number of pins that one term of `phi` reads jointly. The value of `R_t(k)`
  equals the largest value over certificates of pin-degree `<= t`. This is
  the same duality, with the constraint set cut down to moments of order
  `<= t`.

## Theorem

1. **Monotone hierarchy.** `R_1(k) <= R_2(k) <= ... <= R_K(k) = R*(k)`. No
   certificate of pin-degree `<= t` proves a ratio above `R_t(k)`.
2. **Blindness below planes, for every k.** `R_3(k) <= 1`. Any certificate
   of pin-degree `<= 3` proves nothing beyond the completeness ratio 1.
   * More precisely, every certificate satisfies
     `value <= 1 - K sum_{S in W} phi^(S)`. Here `W` is the set of nonempty
     `S` with `|S|` even and `sum_{a in S} a = 0`, which are the supports of
     the dual code of `RM(1,k)`.
   * The smallest members of `W` are the affine planes `{p, p+u, p+v, p+u+v}`.
   * So a certificate is worth something only through its price on
     plane-type parities.
3. **Coset bounds.** Fix `0 <= r <= k-1` and let `C` range over the `2^(K - dim RM(r,k))`
   cosets of the Reed-Muller code `RM(r,k)`, written in `±1` form. Then
   `R_{2^(r+1)-1}(k) <= min_C R_C(k)` and `R*(k) <= avg_C R_C(k)`.
   * In particular, a certificate of pin-degree `< 2^(r+1)` cannot beat the
     *easiest* coset of `RM(r,k)`.
   * A crossing, `R*(k) > 2`, needs `avg_C R_C(k) > 2`.
   * Conversely, to kill the crossing at `k` it suffices to give, for each
     coset, a folded adversary that is told the coset (the syndrome of `xi`)
     and has average cost `<= 2` over the cosets.
4. **Symmetric certificates live on `W`.** An optimal certificate can be
   taken invariant under the gadget's symmetry group `G`, which is generated
   by:
   * affine maps of the coordinate index set;
   * coordinatewise multiplication by characters;
   * negation.

   For invariant `w`, the pattern price `phi` depends only on the `G`-orbit
   of the signed `RM(1,k)`-coset of `xi`, and its Fourier support lies in `W`.
5. **Exact values at k = 3.**
   * `R_1(3) = R_2(3) = R_3(3) = 1`.
   * `R_4(3) = R_5(3) = R_6(3) = R_7(3) = 21/16 = 1.3125`.
   * `R_8(3) = R*(3) = 11/8`.
   * The value `R_7(3)` is attained by the odd class: patterns with an odd
     number of `-1` pins, `R_odd(3) = 21/16`. The even class, which contains
     the dictator patterns, satisfies `R_even(3) >= 23/16`.
   * So `R*(3) = 11/8` is certified only by reading the global parity
     `prod_a xi_a` of all 8 pins.

## Proof

**Item 1.**

* **Monotonicity.** A `(t+1)`-wise uniform law is `t`-wise uniform, so the
  constraint set shrinks as `t` grows and the minimum rises.
* **The top level.** A law on `{-1,1}^K` whose moments of every order
  `1..K` vanish has all Fourier coefficients 0 except the constant one, so
  it is uniform. Hence `R_K = R*`.
* **Duality.** `R_t` is a finite LP: minimize `z` subject to
  `Pr_D[cut e] <= z` for all `e`, with `D` a distribution on folded functions
  and `E_D[chi_S(xi)] = 0` for `1 <= |S| <= t`.
  * Its dual variables are a weighting `w >= 0` of the edges with total 1,
    and multipliers `phi^(S)` for `1 <= |S| <= t`.
  * The dual value is `min_f (E_w cut_f - sum_S phi^(S) chi_S(xi_f))`.
  * Strong duality holds because the primal is feasible, for instance via
    the uniform-pattern adversaries, and bounded.
  * Any certificate's value is at most the minimum over `f` weighed by any
    feasible `D`. So a certificate of pin-degree `<= t` is `<= R_t`.

**Item 2.**

* **The dictator law.** Let `f = s x_i`, with `s = ±1` and `i in F_2^k`
  uniform and independent.
  * `f` is folded, and it cuts an edge of direction `j` exactly when
    `i = j`. So every edge is cut with probability exactly `1/K`.
  * Its pattern is `xi_a = s (-1)^(a.i)`, so
    `E[chi_S(xi)] = E[s^|S|] E[(-1)^((sum S).i)]`.
  * This equals 1 when `|S|` is even and `sum S = 0`, and 0 otherwise.
* **The bound.** For any certificate `(w, phi)` with `phi^(∅) = 0`, the
  minimum over `f` is at most the average over the dictator law. That gives
  `value <= K(1/K - E phi(xi)) = 1 - K sum_{S in W} phi^(S)`.
* **Pin-degree at most 3.** `W` contains no set of size `<= 3`: the sizes
  are even, and `a + b = 0` forces `a = b`. So `phi^` vanishes on `W` and the
  value is `<= 1`. Hence `R_3(k) <= 1`, and in fact the dictator law is
  itself 3-wise uniform.
* **The first sets of `W`.** The size-4 sets of `W` are the 4-sets with
  `a + b + c + d = 0`, which are exactly the affine planes.

**Item 3.**

* **Coset laws are highly uniform.** Write a pattern as `xi = (-1)^(v + c)`,
  with `v` fixed and `c` uniform in `RM(r,k)`. Then
  `E[chi_S(xi)] = (-1)^<v,1_S> E[(-1)^<c,1_S>]`.
  * This is 0 unless `1_S` lies in `RM(r,k)^perp = RM(k-r-1,k)`.
  * The minimum weight of `RM(k-r-1,k)` is `2^(r+1)`.
  * So the uniform law on a coset is `(2^(r+1)-1)`-wise uniform, and every
    `D` feasible for `R_C` is feasible for `R_{2^(r+1)-1}`.
* **The average bound.** Let `D_C` be optimal for `R_C`. The equal mixture
  of the `D_C` has a uniform pattern and satisfies
  `Pr[cut e] = avg_C Pr_{D_C}[cut e] <= avg_C R_C/K` for every `e`.

**Item 4.** The generators of `G` act on patterns as follows.

* **Coordinate translation.** The translation `j -> j + t` sends
  `chi_a` to `(-1)^(a.t) chi_a`. Folding then turns the pattern into
  `xi_a (-1)^(a.t)`.
* **Other generators.**
  * Linear maps of the coordinates relabel the pins by the transpose map.
  * Multiplication by `chi_b` sends `chi_a` to `chi_{a+b}`.
  * `f -> -f` negates the pattern.
* **Invariance.** All of these preserve folding, the edge set and the uniform
  pattern law. The objective `w -> K E_xi m_w(xi)` is concave, where
  `m_w(xi)` is the folded minimum with pattern `xi`, and it is `G`-invariant.
  So averaging an optimal `w` over `G` keeps it optimal.
* **The price.** For invariant `w`, the best price is
  `phi = m_w - E m_w`, which is `G`-invariant.
  * Invariance under `xi -> xi (-1)^(a.t)` for all `t` kills `phi^(S)`
    unless `sum S = 0`.
  * Invariance under `xi -> -xi` kills `phi^(S)` unless `|S|` is even.

**Item 5 (k = 3).** Every step is checked by `verify_k3.py`, with the
results in `results-2026-09-19.txt`.

* **Edge orbits.** At `k = 3`, `G` has two edge orbits: the 128 edges
  incident to a `±pin` (orbit A), and the other 896 (orbit B). An invariant
  weighting is therefore `(WA, WB)` per edge.
* **Pattern orbits.** The 256 patterns split into three `G`-orbits:
  * `lin`, the 16 signed `RM(1,3)` words;
  * `quad`, 112 patterns;
  * `cub`, the 128 patterns with an odd number of `-1`'s.
* **The plane average.** Let `Phi(xi)` be the mean over the 14 affine planes
  of the plane product. It equals `1`, `-1/7` and `0` on `lin`, `quad` and
  `cub` respectively.
* **Lower bound, `R_4(3) >= 21/16`.**
  * Take `(WA, WB) = (5, 1)`. The exact relaxed (s-t min cut) values give
    `K m^U = 1`, `3/2` and `21/16` on `lin`, `quad` and `cub`, where
    `m^U <= m`.
  * For any folded `D` whose law is 4-wise uniform, the class masses satisfy
    `E_D[Phi] = rho_lin - rho_quad/7 = 0`.
  * Hence `K E_D[w.cut] >= min(21/16, (1 + 7*(3/2))/8 = 23/16) = 21/16`.
  * The same computation at `(7, 3)`, where every class has `K m^U = 1`,
    gives `R_1(3) >= 1`.
* **Upper bound, `R_7(3) <= 21/16`.**
  * Two explicit folded `f` with pattern in `cub` have orbit cut counts
    `(28, 112)` and `(14, 182)`.
  * Symmetrize each over `G`, which makes the pattern uniform on the odd
    class, and mix them 1/2 and 1/2.
  * Every orbit-A edge is then cut with probability `21/128`, and so is
    every orbit-B edge, since `147/896 = 21/128`.
  * By item 3 with `r = 2` (`RM(2,3)` is the even-weight code), the odd law
    is 7-wise uniform.
* **Why the value stops at 21/16.** `R_4 <= R_7`, and at `k = 3` the set `W`
  has no members of size 5, 6 or 7, so the constraints of `R_5` to `R_7` add
  nothing beyond `Phi`. The two bounds above therefore meet.
* **The even class.** `R*(3) = 11/8` is certified exactly in
  `hadamard-gadget-deletion-ratio-window`. Item 3 then gives
  `R_even >= 2*(11/8) - 21/16 = 23/16`. The relaxed value at `(5, 1)` is also
  `23/16`.
* **The top level.** `R_8(3) = R*(3) = 11/8` by item 1.

## What this changes

* **A class kill with an explicit invariant.** Every lower-bound technique
  for Hadamard gadgets that constrains the adversary only through `<= 3`-wise
  statistics of its pin values proves ratio `<= 1`.
  * This covers pairwise pin-distance or correlation arguments, and
    Sherali-Adams-type pin marginals of order 3.
  * The invariant is that signed dictators have a pin law that is 3-wise
    uniform, because `RM(1,k)^perp` has minimum distance 4.
  * Every member of the class dies at the step where it evaluates its price
    on the dictator law. `K E_dict[phi]` is its entire gain over ratio 1, and
    `E_dict[phi]` is exactly the plane-parity mass `sum_{S in W} phi^(S)`.
  * So a crossing proof must price plane-type (affine-dependent) pin sets.
    This is a 4-query linearity test on the pins, and it must win more than
    `1/K` from it.
* **A new decomposition of the crossing.** By item 3,
  `R*(k) <= avg_C R_C(k)` over the cosets of any `RM(r,k)`. The crossing
  splits into per-coset (syndrome) problems.
  * **To kill it.** It suffices to find, for some `r`, syndrome-aware folded
    adversaries whose average cost is `<= 2`.
  * **To prove it.** Certificates of pin-degree `< 2^(r+1)` are capped by
    the easiest coset.
  * At `k = 3` the split is strict: the odd class costs `21/16`, the even
    class at least `23/16`, and `11/8` is their mean. So the true
    `k = 3` bound is invisible to every certificate that does not read the
    parity of all 8 pins.
* **Open next steps.**
  * **Beyond `k = 3`.** Compute `R_7(4)`, the easiest `RM(2,4)`-coset, and
    `R_{K/2-1}(k)`, the easiest hyperplane-parity syndrome, for `k = 4, 5`.
  * **The deciding question.** If `R_{K/2-1}(k) <= 2` for every `k`, then
    every crossing certificate must read at least `K/2` pins jointly.
