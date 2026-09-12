---
rg: 2
id: homogeneous-quotient-deep-tower-proof
kind: route
title: Kazhdan-project the cell partition and the gluing unitary, then descend level by level and compress onto the fixed subspace
target: homogeneous-quotient-near-genuine-microstates-are-deep
requires: []
---

Throughout, `||.||_2` is the normalized Hilbert--Schmidt norm on `M_d`,
`rho'` the genuine representation, `Gamma(q)` the principal congruence
subgroup of `C = SL_3(Z)`, and all `O(.)` constants absolute.

**Step 1 (equivariant cells).**  Let `Y = Y_(j+1)`; it is a disjoint union
of `r` copies of the regular `C`-set `SL_3(Z/p^(j+1))`, the stabilizer of a
cell being `Gamma(p^(j+1))`.  The vector `xi = (e_y)_y` in
`l^2(Y) (x) (M_d, ||.||_2)` is almost invariant for the unitary
representation `(c . xi)_y = rho'(c) xi_(c^-1 y) rho'(c)^*` of `C`:
`||c . xi - xi|| <= 3 epsilon |Y|^(1/2)` for `c in S_C`, using the covariance
defect and `||rho - rho'||_2 <= epsilon` on `S_C`.  Property (T) of `C` gives
an invariant vector `xi' = (T_y)` with `||xi - xi'|| <= 3 epsilon |Y|^(1/2)/kappa`;
since the representation factors through the finite image of `rho'`, `xi'`
is the average of `xi` over that finite group, so each `T_y` is a convex
combination of projections, `0 <= T_y <= 1`, and
`rho'(c) T_y rho'(c)^* = T_(cy)` for all `c in C`.

**Step 2 (upper bound (DT2)).**  Let `W` be the `rho'(Gamma(p^j m'))`-fixed
subspace, `P_W` its projection, `F = tau(P_W)`.  `Gamma(p^j m')` is normal
in `C`, so `P_W` commutes with `rho'(C)`.  Put `f_y = P_W T_y P_W`.  For
`c in Gamma(p^j m')`, `rho'(c) P_W = P_W`, hence
`f_(cy) = P_W rho'(c) T_y rho'(c)^* P_W = f_y`.  By the Chinese remainder
theorem `Gamma(p^j m')` surjects onto `Gamma(p^j)/Gamma(p^(j+1))`, which
acts freely on each copy of `SL_3(Z/p^(j+1))` with orbits of size
`s = p^8 >= 2`; so `f_y = f_(y')` for `y != y'` in one orbit.  Now
`||T_y - f_y||_2 <= 2 ||1 - P_W||_2 ||T_y|| <= 2 (1-F)^(1/2)`, while
`||T_y - T_(y')||_2 >= ||e_y - e_(y')||_2 - 6 epsilon |Y|^(1/2)/kappa` and, the
`e_y` being orthogonal projections of trace `1/|Y| + O(epsilon)`,
`||e_y - e_(y')||_2 = (2/|Y|)^(1/2)(1 + O(epsilon |Y|))`.  Hence
`4 (1-F)^(1/2) >= (2/|Y|)^(1/2) - O(epsilon |Y|^(1/2)/kappa)`, which is
`(DT2)`.

**Step 3 (one intertwining projection).**  Let `sigma_1 = rho'|_(C_0)` and
`sigma_2 = rho' o Ad_h |_(C_0)`, both genuine representations of `C_0`, and
`H = rho(h)`.  For `c in S_0`, `||sigma_2(c) H sigma_1(c)^* - H||_2 <= 3 epsilon`
(relator defect of `h c h^-1 = Ad_h(c)` plus `||rho - rho'||_2`).  So `H` is
almost invariant for the representation `X |-> sigma_2(c) X sigma_1(c)^*`
of `C_0` on `(M_d, ||.||_2)`, and property (T) of `C_0` gives an invariant
`T`, i.e. `T sigma_1(c) = sigma_2(c) T` for all `c in C_0`, with
`||H - T||_2 <= 3 epsilon/kappa_0`; `T` is the finite-group average of `H`,
so `||T|| <= 1`.

**Step 4 (isotypic weights are transported).**  For an irreducible `pi` of
`C_0` let `w_i(pi) = tau(P^(i)_pi)` be the normalized dimension of the
`pi`-isotypic subspace of `sigma_i`.  `T` maps `P^(1)_pi` into `P^(2)_pi`, so
`w_2(pi) >= ||T P^(1)_pi||_2^2 >= (w_1(pi)^(1/2) - delta_pi)^2` with
`sum_pi delta_pi^2 <= ||H - T||_2^2`; summing and using Cauchy--Schwarz,
`sum_pi (w_1 - w_2)_+ <= 2 ||H - T||_2`, and symmetrically with `T^*`.  Thus
the total variation `TV(w_1, w_2) <= 12 epsilon/kappa_0`.  The same `T`
intertwines the restrictions of `sigma_1, sigma_2` to every subgroup of
`C_0`, so the same bound holds for the weight measures of any restriction.

**Step 5 (descent (DT1)).**  Put `C^((k)) = cap_(0<=m<=k) h^-m C h^m`; then
`h^i C^((k)) h^-i subset C_0` for `0 <= i < k`.  Applying Step 4 to the
subgroup `h^i C^((k)) h^-i` and transporting along `Ad_h`, and chaining
`k` times, the weight measure of `rho'|_(C^((k)))` and the `Ad_(h^k)`-transport
of the weight measure of `rho'|_(h^k C^((k)) h^-k)` are within
`12 k epsilon/kappa_0` in total variation.  The first is supported on
irreducibles trivial on `C^((k)) cap Gamma(p^a m')`, the second on those
trivial on `N^((k)) = C^((k)) cap h^-k Gamma(p^a m') h^k`.  Hence the
`rho'(N^((k)))`-fixed fraction is at least `1 - 12 k epsilon/kappa_0`.  Since
`h^k e_12(x) h^-k = e_12(p^k x)` and `h^k e_23(x) h^-k = e_23(p^k x)`, the
subgroup `N^((k))` contains `e_12(p^(a-k) m')` and `e_23(p^(a-k) m')`.
Conjugating by a fixed finite set `S` of signed permutation matrices gives
all `e_(ij)(+-p^(a-k) m')`; the group they generate is normalized by every
`e_(kl)(+-1)` (its commutators with them are products of level-`p^(a-k)m'`
elementary matrices), hence normal in `SL_3(Z)`, hence equal to its normal
closure, which is `Gamma(p^(a-k) m')` by Bass--Milnor--Serre (`n = 3`, base
ring `Z`).  Each conjugate `g^-1 e_(ij)(q) g` has fixed fraction at least
`1 - 12 k epsilon/kappa_0` (conjugation by the unitary `rho'(g)`), and the
fixed space of the generated group is the intersection, so
`F(p^(a-k) m') >= 1 - 2|S| . 12 k epsilon/kappa_0`; rename the constant `C_1`.

**Step 6 (combine).**  Take `k = a - j` in `(DT1)` and compare with `(DT2)`:
`1 - C_1 (a-j) epsilon/kappa_0 <= F(p^j m') <= 1 - 1/(8|Y_(j+1)|) + C_2 |Y_(j+1)| epsilon/kappa`,
which is `(DT3)`.  The flatness statement is `(DT1)` read as "the total
weight of the top `k` levels is at most `C_1 k epsilon/kappa_0`".
