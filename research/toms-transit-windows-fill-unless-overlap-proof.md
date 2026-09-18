---
rg: 2
id: toms-transit-windows-fill-unless-overlap-proof
kind: route
title: Lower semicontinuity costs one rank per leaf at every transit; windows whose leaf maxima do not overlap are filled by the constant bundle of the maxima; overlap contradicts coprime Chern divisibility on the vertex slice
target: toms-transit-windows-fill-unless-their-ranks-overlap
requires: []
---

Notation is as in the target. Write `D = d_n c` and `theta = ceil(D) - D in [0, 1)`.

**Step 0 (rank bands).** In `A`, point traces are exact
(`toms-line-subalgebra-has-no-nonconstant-continuous-rank`): the stage-`n` point mass at
`x in X_n` is the restriction of a trace of `A`. So `d(a_n) <= f` and `d(a_n) >= f - eps_n`
give `d_n (phi(s) - eps_n) <= R(s) <= d_n phi(s)`. At stage `M`, the rank of `a_M` at a
point `y` lies in `[d_M (f(y) - eps_M), d_M f(y)]`, and `d_M f(y)` is the sum of `d_n F_n` over
the `K` copies of `y`. On a box `S` every node contributes `d_n c` and the other coordinates are
fixed, so `d_M f` is constant on `S` and `U = floor(d_M f)` is an integer upper bound for
`rank a_M` there. In `B`, branch traces `beta_n delta_x + kappa_n` replace point masses, and
the bands hold with `d_n` replaced by `r_n / beta_n` and the constant contamination moved
into `g_0` (`toms-simple-algebra-has-no-block-diagonal-rank-realizer`).

**Step 1 (Part 1).** Let `0 < s < 1`. For `t < s`, `R(t) <= d_n phi(t) < d_n phi(s)`, because
`phi` is strictly increasing. Since `R(t)` is an integer, `R(t) <= ceil(d_n phi(s)) - 1`.
Lower semicontinuity gives `R(s) <= liminf_(t -> s-) R(t) <= ceil(d_n phi(s)) - 1`. The same
argument at `1 - s` gives `R(1 - s) <= ceil(d_n phi(1-s)) - 1`. With `x = d_n phi(s)` and
`d_n phi(1-s) = D - x`, the inequality `ceil(x) + ceil(D - x) <= ceil(D) + 1` gives
`R(s) + R(1-s) <= ceil(D) - 1`.

If the window transits, say `Pbar > p*`, pick `s_a` with `R(s_a) = Pbar >= p* + 1`. Then
`p* + 1 + q* <= R(s_a) + R(1 - s_a) <= ceil(D) - 1`, so the room is
`D - p* - q* >= 2 - theta > 1`. The case `Qbar > q*` is symmetric.

Box room: `U - g >= floor(sum_nu (D - p*_nu - q*_nu) + sum_other (d_n F_n - rank a_n))`,
because the other copies have `rank a_n <= d_n F_n` at their fixed points. So
`U - g >= floor(N (2 - theta))`. This is `>= 2N > N` when `D` is an integer, and it is `> N`
whenever `N (1 - theta) >= 1`.

Circularity. A drop of `Q` bounds `eps_M` from below only if `a_M <~ Q`, since then
`rank a_M <= rank Q` pointwise. Then `rank Q >= rank a_M >= d_M f - d_M eps_M >= U - d_M eps_M`
on `S`. Theorem 1 assumes `rank Q <= g + N` on `S`. The two together give
`d_M eps_M >= U - g - N`. With `N = K/2` nodes, `D` an integer, and room exactly two per
node, this is `d_M eps_M >= K/2`, that is `eps_M >= 1/(2 d_n)`, since `d_M = K d_n`. That is the
conclusion Theorem 1 was meant to deliver. A target that sits below `a_M` in the chain
(`Q <~ a_M`) bounds nothing, because its drops do not pass to `a_M`. So no admissible
target has room one per node unless the conclusion already holds.

**Step 2 (Part 2).** Fix a node `nu` with window `I`. The function `s -> a_n(x(s))` lies in
`M_infinity(C(I))_+`, and its rank function is `R|_I <= Pbar`. By Robert's computation
`Cu(C[0,1]) = Lsc([0,1], N-bar)`, Cuntz comparison over an interval is pointwise comparison of
rank functions, so `a_n ∘ x|_I <~ 1_(Pbar)`. Likewise `a_n ∘ x(1 - .)|_I <~ 1_(Qbar)`. Cuntz
subequivalence survives pullback along the coordinate map `S x Y x Z -> I_nu`, and
tensoring with a fixed projection. So the node block satisfies

```text
a_n(x(s_nu)) ⊗ L_(nu,+)  ⊕  a_n(x(1 - s_nu)) ⊗ L_(nu,-)   <~   1_(Pbar) ⊗ L_(nu,+) ⊕ 1_(Qbar) ⊗ L_(nu,-).
```

The other copies sit at fixed points of `X_n`. Their blocks are `a_n(x_0) ⊗ L` with a constant
matrix `a_n(x_0)`, which is Cuntz equivalent to its support projection tensored with `L`.
Orthogonal sums preserve `<~`, so `psi_(n,M)(a_n) <~ P` on the box. Here `P` is the projection
of constant rank `rank_other + sum_nu (Pbar_nu + Qbar_nu)`.

If `kappa_nu <= 0` for every `nu`, then
`rank P <= sum_other d_n F_n + sum_nu D = d_M f`, and so `rank P <= U`, since the left side is an
integer. Put `Q_fill = P ⊕ 1_(U - rank P)`. It has constant rank `U`, it dominates the
pushforward, and `U` lies in the band `[d_M (f - eps_M), d_M f]` of `a_M` whenever that band
contains an integer. An argument that uses only `psi(a_n) <~ Q` and the rank bands therefore
cannot rule out `Q_fill`, and `Q_fill` has no drop.

The ideal case. Let `R(s) = ceil(d_n phi(s)) - 1`, which is the lower semicontinuous
normalization of `floor(d_n phi)`, and let `D` be an integer. A window meets one jump
`s_j`, where `d_n phi(s_j) = k`. Since `D` is an integer, `R(1 - .)` jumps at the same point.
Left of `s_j`, `(R(s), R(1-s)) = (k-1, D-k)`. At `s_j` it is `(k-1, D-k-1)`, and right of `s_j`
it is `(k, D-k-1)`. So `Pbar + Qbar = D`, `kappa = 0`, and the room is `2`. This matches the brief's
"short by 1 off jump points and 2 at them".

**Step 3 (Part 3).** Suppose that `rank Q = g_0 + r` on all of `I x CP^j`. A continuous
positive matrix function of constant rank on a compact space has a continuous support
projection: the least positive eigenvalue is bounded away from `0`. So `Q` is Cuntz equivalent to
the projection onto a bundle `V` of rank `g_0 + r`. Since `I` is contractible,
`V ≅ pr^* V_s` for every slice `V_s = V|_({s} x CP^j)`, and all slices are isomorphic.

On the slice `CP^(j_v)` every ancestor coordinate and every other coordinate is fixed. So
`Gamma_nu` and the lines of the other copies are trivial there, and `L_+`, `L_-` restrict to
`O(alpha)`, `O(beta)`. Take `s_a` with `R(s_a) = Pbar`. At `s_a` the pushforward is Cuntz
equivalent to the projection onto `W_a = C^(g_0) ⊕ Pbar O(alpha) ⊕ R(1-s_a) O(beta)`. For
projections, Cuntz subequivalence is Murray-von Neumann subequivalence, so `W_a` is
isomorphic to a subbundle of `V_(s_a)`, and `V ≅ W_a ⊕ C_a` on the slice. Chern polynomials
vanish above the rank. So in `H^*(CP^j) = Z[u]/(u^(j+1))`,

```text
c(V) = (1 + alpha u)^Pbar (1 + beta u)^(R(1-s_a)) c(C_a),   the right side of degree <= r.
```

In the same way, at `s_b` with `R(1 - s_b) = Qbar`, `c(V) = (1 + beta u)^Qbar (1 + alpha u)^(R(s_b)) c(C_b)`,
also of degree `<= r`. Both right sides are polynomials of degree at most `r <= j`. They agree
modulo `u^(j+1)`, so they are equal in `Q[u]`. So one polynomial `c`, with `c(0) = 1` and
`deg c <= r`, is divisible by `(1 + alpha u)^Pbar` and by `(1 + beta u)^Qbar`. These are coprime,
because `alpha`, `beta` are non-zero and distinct, so their roots `-1/alpha != -1/beta`. So `c` is
divisible by their product, which has degree `Pbar + Qbar > r >= deg c`. Then `c = 0`, which
contradicts `c(0) = 1`. Hence `rank Q` is not identically `g_0 + r`. With the hypothesis
`rank Q <= g_0 + r`, this means `rank Q < g_0 + r` somewhere.

**Step 4 (Part 4).** Let `D` be an integer, and write `E = D - 1`. By Step 1,
`R(s) + R(1-s) <= E` everywhere. At `s_a` this gives `q* <= R(1 - s_a) <= E - Pbar`, and at
`s_b` it gives `p* <= E - Qbar`. So

```text
(Pbar - p*) + (Qbar - q*) >= 2 (Pbar + Qbar) - 2E = 2 kappa + 2 >= 4,
D - p* - q* >= D - 2E + Pbar + Qbar = kappa + 2 >= 3.
```

The ideal staircase over a window with two jumps, at `d_n phi = k` and `d_n phi = k + 1`,
takes the values `(k-1, E+1-k)`, then `(k, E-k)` in the middle chamber, then `(k+1, E-1-k)`.
So `Pbar = k + 1`, `Qbar = E + 1 - k`, `kappa = 1`, `p* = k - 1`, `q* = E - 1 - k`, and the
room is `3`. Relative to the common part, the facet `s = s_0` carries `2 L_-`, the middle
chamber carries `L_+ ⊕ L_-`, and the facet `s = s_1` carries `2 L_+`. Theorem 1's data has
one extra line per facet with room one, so `Pbar - p* = Qbar - q* = 1` and `p* + q* = D - 1`.
Then `kappa = 1`, but there are only `2 < 4` transits, which contradicts the bound above. So a
pushforward window never has the pattern `(1, 1; 1)`.

**Step 5 (Part 5).** Let `s_0 = 1/2 - w` and `s_1 = 1/2 + w`. Then `Pbar >= R(s_1)` and
`Qbar >= R(1 - s_0) = R(s_1)`. By Step 0, `R(s_1) >= d_n (phi(s_1) - eps_n)`, and
`c = 2 phi(1/2)`. So

```text
kappa >= 2 d_n (phi(1/2 + w) - phi(1/2) - eps_n) > 2 d_n / (2 d_n) = 1.
```

The node data `x`, `phi` is the same at every bottom node, because the swap path is chosen in
`X_n`. So one `w` serves all `K/2` bottom nodes. Since `eps_n -> 0` and
`phi(1/2 + w) - phi(1/2) > 0` for a fixed `w`, the hypothesis holds for all large `n` once
`1/(2 d_n) + eps_n` is small. It suffices that `phi(1/2 + w) - phi(1/2)` does not shrink with `n`.
That holds for the swap paths of `toms-sibling-cube-swap-drops-add-to-depth-n`, where
`phi = F_n ∘ x` has range fixed by `h`.

**In `B`.** Steps 1, 2, 4 and 5 use only the bands, with `d_n -> r_n / beta_n`. Step 3 uses
only the vertex slice, where every point block of `B` is a trivial summand of `g_0`. This
finishes the proof.
