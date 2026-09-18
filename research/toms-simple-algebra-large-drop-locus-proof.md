---
rg: 2
id: toms-simple-algebra-large-drop-locus-proof
kind: route
title: A Cuntz-continuity approximant with slack below delta Delta, bands at the diagonal point over the maximum and on the swap family, and the drop-locus transport bound with the point blocks as a trivial summand
target: toms-simple-algebra-approximants-drop-rank-on-a-large-set
requires: []
---

Notation is from the target. `f(tau) = tau(h)`. The drop-locus transport bound and
its swap corollary are `toms-swap-drop-locus-has-codimension-at-most-2m-plus-1`,
proved in `toms-swap-drop-locus-codimension-proof`.

**Step 0 (the arc).** Let `p` be a maximum point of `h`, and `q` a point with `h(q) < h(p)`.
`X_1 = Gr(d, 2d)` is connected. Take a path from `q` to `p`, and stop it the first time
`h` reaches `max h`. Its image is a path-connected Hausdorff set, so it contains an arc
from `q` to that point, and `h < max h` on the arc except at the end. `Delta > 0`
follows: for each `s`, at most one of `s, 1-s` equals `1`, and when one does the other
is `0`, so `g(s) + g(1-s) < 2 g(1)`. The maximum over the compact `[0,1]` is attained.

**Step 1 (approximant).** Fix `theta` with `0 < theta < delta Delta`.
- *Dini.* `d_tau((a - t)_+)` increases to `f(tau)` as `t -> 0`. The functions are lower
  semicontinuous and `f` is continuous, and `T(B)` is compact. So the open sets
  `{tau : d_tau((a - t)_+) > f(tau) - theta}` increase and cover `T(B)`, and some `t` has
  `d((a - t)_+) > f - theta` everywhere.
- *Finite stage.* By continuity of `Cu` under inductive limits (Coward–Elliott–Ivanescu),
  `[a]` is the supremum of an increasing sequence of classes of finite-stage elements
  below `a`. Since `[(a - t)_+] ≪ [a]`, some finite-stage `b in M_infinity(B_N)_+` has
  `(a - t)_+ <~ b <~ a`.

So `f - theta <= d(b) <= f`.

**Step 2 (profile).** For `w in X_M`,
`f(sigma_w) = beta_M tr_w(psi_(1,M)(h)) + integral tr_z psi_(1,M)(h) d kappa_M`. Top leaves carry
`h(z_l)` with total weight `prod_(i<M) alpha_i`, and point blocks carry constants. So
`f(sigma_w) = delta F_M(w) + c_*`, with `c_*` independent of `w` and `F_M` the normalized
top leaf average. At `w(s) = (xi(s), xi(1-s), p)` half the top leaves sit at `c(s)` and
half at `c(1-s)`, so `F_M(w(s)) = (g(s) + g(1-s))/2 <= g(1) - Delta`. At the full diagonal
point `x_M(1) = (xi(1), xi(1), p_*)` over `c(1)`, `F_M = g(1)`.

**Step 3 (slices of the pushforward).** Put `a' = psi_(N,M)(b)`,
`b' = psi_(N,M-1)(b)`, and let `b_Y in M_infinity(C(Y))` be `b'` pushed through all but
the last doubling of `psi_(M-1)^top`. The intermediate twists are pulled back from the
factors of `Y`, so on a slice `{(y_1, y_2)} x CP^j` they are constant. Hence

```text
a'|({(y_1, y_2)} x CP^j) = b_Y(y_1) tensor gamma_1 + b_Y(y_2) tensor gamma_2 + Π,
```

with `Π = psi_(M-1)^pt(b')` constant and untwisted, in orthogonal summands. Put
`R(y) = rank b_Y(y)` and `π = rank Π`. The endpoint slices of `K_M` are
`(xi(0), xi(1))` and `(xi(1), xi(0))`, so the swap corollary applies with `Q = a''`,
`R_x = R(xi(0))`, `R_y = R(xi(1))`, and the containments `a'|slice <~ a''|slice`. Also
`rank a'(x_M(1)) = 2 R(xi(1)) + π`.

**Step 4 (bands).**
- *Lower band.* `d_(sigma_(x_M(1)))(a') = d_(sigma_(x_M(1)))(b) >= f - theta` gives
  `beta_M (2R(xi(1)) + π)/r_M + C(a') >= delta g(1) + c_* - theta`.
- *Upper band.* Let `w_0 in K_M` have `rank a''(w_0) = m`. Then
  `beta_M m / r_M + C(a'') <= f(sigma_(w_0)) <= delta (g(1) - Delta) + c_*`. Since
  `f <= 1` and `C >= 0`, this also gives `m <= r_M / beta_M <= r_M / delta`.
- *Contamination.* `a' <~ a''` gives `rank a' <= rank a''` pointwise, so `C(a'') >= C(a')`.

Subtracting,

```text
beta_M (m - 2R(xi(1)) - π) / r_M  <=  theta - delta Delta  <  0,
```

so `m < 2 R(xi(1)) + π <= 2 max(R_x, R_y) + π`.

**Step 5 (conclusion).** The swap corollary gives `dim D >= 2j - 2m`. With
`j >= delta^2 r_M^2 / 2` and `m <= r_M/delta`, this is `>= delta^2 r_M^2 - 2 r_M/delta`,
which is positive once `r_M > 2/delta^3`, and then `D` is non-empty. If
`psi_(N,M)(b) <~ a'' <~ a`, then `d(a'') <= d(a) = f`, so `a''` qualifies. Square.
