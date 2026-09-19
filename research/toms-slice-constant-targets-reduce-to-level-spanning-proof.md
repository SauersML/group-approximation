---
rg: 2
id: toms-slice-constant-targets-reduce-to-level-spanning-proof
kind: route
title: The lcm of the leaf-maximum lines over the closure of each level component divides the constant Chern class of that component, which prices every component at delta + E <= N; spanning all but delta coordinates then costs 3 delta >= N
target: toms-slice-constant-targets-reduce-to-level-spanning
requires: [toms-overlap-window-drops-need-not-coincide]
---

Notation is as in the target and in `toms-overlap-window-drops-need-not-coincide-proof`. Fix
`z_0` with `rank Q(s, y, z_0) = U - delta(s)`. Put `X = S x Y x {z_0}` and let `u_nu` be the
hyperplane class of `Y_nu`. As in Part 1 there, the pushforward on the slice `{x} x Y` is
Cuntz equivalent to the projection onto

```text
W(x) = C^(g') ⊕ ⊕_nu ( R_nu(x_nu) O_nu(alpha) ⊕ R_nu(1 - x_nu) O_nu(beta) ),
```

where `alpha` and `beta` are distinct and non-zero.

**Step 0 (slice supports).** Fix `x in S` and let `r = rank Q(x, ., z_0)`, which is constant
on `Y`.
- *The support is a bundle.* Let `lambda_r(x, y)` be the `r`-th largest eigenvalue of `Q(x, y)`.
  It is continuous and positive on the compact space `Y`, so its minimum `lambda_x` is
  positive. The spectrum of `Q(x, y)` lies in `{0} ∪ [lambda_x, inf)` for every `y`. So the
  support projection `p_x = chi_(0, inf)(Q(x, .))` is a continuous function of a continuous
  element, and it is a projection in `C(Y) ⊗ K`. Its range is a bundle `V_x` of rank `r`, and
  `Q(x, .) ~ p_x` in the Cuntz semigroup.
- *It contains `W(x)`.* Since `psi(a_n) <~ Q`, `W(x) <~ p_x`. For projections, Cuntz
  subequivalence is Murray-von Neumann subequivalence, so `V_x ≅ W(x) ⊕ E_x`.

**Step 1 (closure points sit under the component).** Let `Omega` be a level component with
`delta = t`, fix `s_0 in Omega`, and let `x in cl Omega`. We claim `V_x ≾ V_s` for every
`s in Omega`.
- *Near `x`.* Put `eps = lambda_x / 4`. By uniform continuity of `Q` on the compact space `X`,
  there is `s in Omega` with `||Q(s, .) - Q(x, .)|| < eps` in `C(Y) ⊗ K`. By the Kirchberg-Rørdam
  lemma, `(Q(x, .) - eps)_+ <~ Q(s, .)`.
- *Comparing supports.* Because `eps < lambda_x`, `(Q(x, .) - eps)_+` has the support
  projection `p_x`, and `p_x` is a continuous function of it. So
  `p_x <~ (Q(x, .) - eps)_+ <~ Q(s, .) ~ p_s`.
- *Along `Omega`.* The classes of `p_s` are locally constant in `s in Omega`. Near `s_1 in Omega`
  the rank on `Omega x Y` is constant, and by the gap argument of Step 0 (applied locally,
  with `lambda` bounded below on a neighbourhood) the support projections vary continuously.
  Close projections are unitarily equivalent. `Omega` is connected, so every `V_s` with
  `s in Omega` is isomorphic to one bundle `V_Omega`.

Hence `V_x ≾ V_Omega` for every `x in cl Omega`. With Step 0, this gives
`V_Omega ≅ W(x) ⊕ F_x` for some bundle `F_x`.

**Step 2 (lcm).** Let `c` be the polynomial of `c(V_Omega) in H^*(Y)`, with exponents at most
`j_nu`, as in Part 1. Then `c(0) = 1`. From `V_Omega ≅ W(x) ⊕ F_x` we get

```text
c(V_Omega) = c(W(x)) c(F_x),    deg c(W(x)) + deg c(F_x) <= (rank W(x) - g') + rank F_x = rank V_Omega - g' = N D - t,
```

with `N D - t <= min j_nu`.
- *Divisibility in the polynomial ring.* No product exponent reaches the truncation, so as in
  Part 1, `c = c(W(x)) · c(F_x)` holds in `Q[u_1, ..., u_N]` and `deg c <= N D - t`. So
  `c(W(x)) = prod_nu (1 + alpha u_nu)^(R_nu(x_nu)) (1 + beta u_nu)^(R_nu(1 - x_nu))` divides
  `c` for every `x in cl Omega`.
- *The lcm.* The linear forms `1 + alpha u_nu` and `1 + beta u_mu` are pairwise non-associate
  irreducibles in a UFD. So `c` is divisible by
  `prod_nu (1 + alpha u_nu)^(P_nu) (1 + beta u_nu)^(Q_nu)`, where `J_nu = pi_nu(cl Omega)`,
  `P_nu = max_(J_nu) R_nu(s)` and `Q_nu = max_(J_nu) R_nu(1 - s)`.

The maxima for different `nu`, and for `P` against `Q`, may be attained at different points
of `cl Omega`. The lcm handles this. Hence

```text
sum_nu ( P_nu + Q_nu )  <=  N D - t.                                          (1)
```

**Step 3 (the table).** `J_nu` is a closed interval in `I_nu`. It equals `cl(pi_nu Omega)`,
since `S` is compact. The zone values `(R(s), R(1 - s))` are:

- chamber `A`: `(k-1, D-k)`;
- wall `w_1`: `(k-1, D-k-1)`;
- chamber `B`: `(k, D-1-k)`;
- wall `w_2`: `(k, D-k-2)`;
- chamber `C`: `(k+1, D-2-k)`.

This gives four cases for `P + Q`.
- *`J` meets one chamber only,* possibly with its end walls: `P + Q = D - 1`.
- *`J` is one wall point:* `P + Q = D - 2`.
- *`J` meets `A` and `B` but not `C`:* `(P, Q) = (k, D - k)`. *`J` meets `B` and `C` but not `A`:*
  `(P, Q) = (k + 1, D - 1 - k)`. Both give `P + Q = D`.
- *`J` meets `A` and `C`,* hence also `B`: `(P, Q) = (k + 1, D - k)`, so `P + Q = D + 1`.

So in all cases `P_nu + Q_nu = D - 1 + e(J_nu)`, and (1) becomes
`N (D - 1) + E(cl Omega) <= N D - t`. That is `delta(Omega) + E(cl Omega) <= N`. This is
part 1. ∎

**Part 2.** Let `Omega` fail to span exactly `f <= t = delta(Omega)` coordinates.
- *Spanned coordinates.* If `Omega` spans `nu`, then `J_nu` meets `A` and `C`, so `e(J_nu) = 2`.
- *The others.* Every other `e(J_nu) >= -1`.

So `E(cl Omega) >= 2(N - f) - f`. Part 1 gives `t + 2N - 3f <= N`, so `N + t <= 3f <= 3t`,
that is `t >= N/2`. The depth is `>= max delta >= t`, and it is an integer, so it is
`>= ceil(N/2)`. ∎

**Part 3.** In Part 2 of `toms-overlap-window-drops-need-not-coincide-proof`, every node target
has the form `F_+ ⊗ p_(nu,+) ⊕ F_- ⊗ p_(nu,-)` with `F_± in C(I_nu) ⊗ K`. Its rank at
`(s, y, z)` is `rank F_+(s_nu) + rank F_-(s_nu)`, which is independent of `(y, z)`. The part `G`
outside the nodes has constant rank `g'`. So the staggered target of depth `ceil(N/2)` is
slice-constant. ∎

**Part 4.** Let `delta` be upper semicontinuous with values in `Z_(>=0)`.
- *`N = 1`.* If `delta = 0` everywhere, the one component is `I` itself, which spans. Otherwise
  a component with `t >= 1` fails at most `1 <= t` coordinates.
- *`N = 2`, easy cases.* A component with `t >= 2` qualifies. So does a component with
  `t = 1` that spans a coordinate.
- *`N = 2`, remaining case.* Assume `delta <= 1` and no component of the closed set
  `H = {delta = 1}` spans a coordinate. The faces `{x_nu = 0}` and `{x_nu = 1}` lie in `A` and `C`.
  So no component of `H` meets both `x_1`-faces, and none meets both `x_2`-faces.

  *Crossing lemma.* If a closed set `F` in the square has no connected subset meeting both
  `x_1`-faces, then the complement contains a path joining the two `x_2`-faces. (This is the
  continuous Hex lemma: D. Gale, *The game of Hex and the Brouwer fixed-point theorem*,
  Amer. Math. Monthly 86 (1979). It also follows from the boundary-bumping separation of
  compacta in M. H. A. Newman, *Elements of the topology of plane sets of points*, Ch. V.)

  So the open set `L = {delta = 0}` contains a path `gamma_2` joining the `x_2`-faces and a path
  `gamma_1` joining the `x_1`-faces. Two such paths meet: this is the square-crossing
  lemma, which follows from Brouwer's fixed-point theorem (R. Maehara, *The Jordan curve
  theorem via the Brouwer fixed point theorem*, Amer. Math. Monthly 91 (1984)). So they lie
  in one component of `L`, which spans both coordinates and fails `0 <= 0`. ∎

For `N = 2` this recovers depth `>= 1` for slice-constant targets. Part 1 of
`toms-overlap-window-drops-need-not-coincide` already gives that for all targets, so the
content of this claim is for `N >= 3`, conditional on (S) there.

**Where the naive `N`-dimensional Hex argument breaks.** Colour each component by a
coordinate it fails to span. Gale's `N`-dimensional Hex theorem gives a connected
monochromatic set joining the `i`-faces. Its components all fail `i`.
- *What holds.* A component that misses `C` in coordinate `i` and one that misses `A` are
  never adjacent. If `Omega ⊂ cl Omega'`, then `pi_i Omega ⊂ cl pi_i Omega'`.
- *What breaks.* The chain can still pass through a component lying in the middle strip
  `[w_1, w_2]` in coordinate `i`. Such a component fails `i` for free. Excluding this needs
  the budget of part 1, not only the count in (S). This is the open step.
