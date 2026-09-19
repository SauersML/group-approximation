---
rg: 2
id: sp4-ssd-is-a-matrix-ultraproduct-winding-bound-proof
kind: route
title: Take ultraproducts of amplified window witnesses, lift unitaries back, and differentiate the trace of the logarithm along a straight-line path of letters
target: sp4-ssd-is-a-matrix-ultraproduct-winding-bound
requires:
  - sp4-quasirep-windings-budget-and-saturation
  - sp4-winding-ratio-is-an-infimum-over-scales
---

Notation as in the target. "Defect `<= eps` on `W`" means `||pi(g)pi(h) - pi(gh)|| <= eps` for `(g,h) in W`. For
`c < 2` let `K_c = {z in T : |z - 1| <= c}`, an arc avoiding `-1`. Fix `f_c in C(T)` equal to the principal `log` on
`K_c`.

**Step 0: five facts.**
- *(Q1) Norm and trace.* `||[x_n]|| = lim_omega ||x_n||`, and `tau` is a well-defined tracial state, since
  `|tr(x_n)| <= ||x_n||`.
- *(Q2) Unitaries lift to unitaries.* Let `u in U(Q)` with bounded lift `(x_n)`. Then
  `||x_n* x_n - 1|| -> 0` along `omega`. On the `omega`-large set where this norm is `< 1/2`, put
  `u_n = x_n (x_n* x_n)^(-1/2)`, and `u_n = 1` elsewhere. Then `u_n` is unitary and `||u_n - x_n|| -> 0` along
  `omega`, so `[u_n] = u`. Lift `1` as `1`.
- *(Q3) The logarithm passes to the quotient.* Suppose `U_n` are unitaries with `||U_n - 1|| <= c < 2` for
  `omega`-most `n`. The spectra lie in `K_c`, so `log U_n = f_c(U_n)`. Continuous functional calculus of normal
  elements commutes with unital *-homomorphisms, applied to the quotient map `prod M_(n!) -> Q`. So
  `log [U_n] = [log U_n]`, and `tau(log [U_n]) = lim_omega tr(log U_n)`. The same holds for any unital
  *-homomorphism `theta` and any unitary `U` with `||U - 1|| <= c`: `theta(log U) = log theta(U)`.
- *(Q4) Amplification.* `pi (x) 1_m` has the same defects as `pi`, and `W_r(pi (x) 1_m) = W_r(pi) (x) 1_m`. So
  `kappa_r` is multiplied by `m`, and `kappa_r/d` is unchanged.
- *(Q5) Budget in any C*-algebra.* Step 1 of `sp4-quasirep-windings-budget-and-saturation-proof` (with `t = 0`)
  uses only unitarity and the triangle inequality. So for any unital `Pi : Gamma -> U(A)` with defect `<= eps` on
  `W_r`, `||W_r(Pi) - 1|| <= (6g-1) eps`. For `eps <= a_g` this is `<= 1`, so `kappa^tau(Pi)` is defined.

The count behind (Q5): replace the `2g` adjoints `Pi(y)*` by `Pi(y^-1)`, each at cost `<= eps` from the pair
`(y, y^-1)`. Then collapse the `4g` factors to `Pi(r) = Pi(e) = 1` by `4g - 1` multiplications on the pairs
`(p_j, y_(j+1))`. That gives `2g + 4g - 1 = 6g - 1`.

**Step 1: `w_W(eps) >= S_W(eps+)`, attained.** Let `L = S_W(eps+)`. For each `j` with `eps + 1/j <= a_g`, pick a
unital `pi_j : Gamma -> U(d_j)` with defect `<= eps + 1/j` on `W` and
`kappa_r(pi_j)/d_j >= S_W(eps + 1/j) - 1/j >= L - 1/j`. Take `kappa_r(pi_j) >= 0` by complex conjugation (Step 2 of
`sp4-winding-ratio-is-an-infimum-over-scales-proof`).

Let `j(n)` be the largest admissible `j <= n` with `d_j <= n`, and put `sigma_n = pi_(j(n)) (x) 1_(n!/d_(j(n)))`.
This is defined because `d_j <= n` implies `d_j | n!`. For small `n` with no such `j`, put `sigma_n = 1`. For every
`J`, `j(n) >= J` once `n >= max(J, d_1, ..., d_J)`, so `j(n) -> infinity` along `omega`.

Put `Pi(g) = [sigma_n(g)]`. It is unital and unitary. By (Q1), for `(g,h) in W`,
`||Pi(g)Pi(h) - Pi(gh)|| <= lim_omega (eps + 1/j(n)) = eps`. By (Q5), `||W_r(sigma_n) - 1|| <= 1` for
`omega`-most `n`. So by (Q3) and (Q4),
`kappa^tau(Pi) = lim_omega kappa_r(pi_(j(n)))/d_(j(n)) >= L`.

**Step 2: `w_W(eps) <= S_W(eps+)`.** Let `Pi : Gamma -> U(Q)` be unital with defect `<= eps` on `W`. Let `F` be
the finite set of elements occurring in the pairs of `W`, together with their products and `e`. By (Q2), lift each
`Pi(g)`, `g in F`, to unitaries `u_n(g)`, with `u_n(e) = 1`. Put `pi_n(g) = u_n(g)` on `F` and `pi_n(g) = 1` off `F`.

By (Q1), each pair `(g,h) in W` has `lim_omega ||pi_n(g)pi_n(h) - pi_n(gh)|| <= eps`. Since `W` is finite, for every
`eps' in (eps, a_g]` the set `A_(eps')` of `n` with defect `<= eps'` on `W` lies in `omega`. On `A_(eps')`,
`|kappa_r(pi_n)|/n! <= S_W(eps')`.

`W_r` uses only the letters and their adjoints, so `W_r(Pi) = [W_r(pi_n)]`. By (Q5) on `A_(a_g)` and by (Q3),
`kappa^tau(Pi) = lim_omega kappa_r(pi_n)/n!`. So `|kappa^tau(Pi)| <= S_W(eps')` for every `eps' in (eps, a_g]`.
With Step 1 this gives `w_W(eps) = S_W(eps+)`, a maximum.

**Step 3: the window-free identity.**
- *Upper bound.* A uniform `eps`-quasi-representation `Pi` has defect `<= eps` on every `W`. So by Step 2,
  `|kappa^tau(Pi)| <= S_W(eps+)` for all `W`.
- *Lower bound.* Let `L = inf_W S_W(eps+)`. `Gamma` is countable, so choose finite windows
  `W_r subset W_1 subset W_2 subset ...` exhausting `Gamma x Gamma`. Pick `pi_j` with defect `<= eps + 1/j` on `W_j`
  and `kappa_r(pi_j)/d_j >= S_(W_j)(eps + 1/j) - 1/j >= L - 1/j`. The last inequality holds because
  `S_(W_j)(eps + 1/j) >= S_(W_j)(eps+) >= L`.
- Build `Pi` as in Step 1. A pair `(g,h)` lies in `W_j` for all `j >= j_0`. So its defect is
  `<= lim_omega (eps + 1/j(n)) = eps`. Hence `Pi` is a uniform `eps`-quasi-representation, and `kappa^tau(Pi) >= L`.

This proves item 1.

**Step 4: item 2.**
- *First direction.* Suppose `w(eps_0) < eps_0 nu/(2 pi)` with `eps_0 < a_g`. Step 3 gives a `W` and an
  `eps_1 in (eps_0, a_g]` with `S_W(eps_1) < eps_0 nu/(2 pi) < eps_1 nu/(2 pi)`.
- *Second direction.* Suppose `S_W(eps_1) < eps_1 nu/(2 pi)`. Pick `eps_0 < eps_1` with
  `S_W(eps_1) < eps_0 nu/(2 pi)`. Then `w(eps_0) <= S_W(eps_0+) <= S_W(eps_1)`, which is below the bound.
- Since `w(eps_0)` is a maximum by Step 3, the condition `w(eps_0) < eps_0 nu/(2 pi)` says exactly that every uniform
  `eps_0`-quasi-representation satisfies (SSD_Q).
- The `tau_W` form is the same argument with `w_W` and Step 2. The contrapositive follows from attainment.

**Step 5: homotopy invariance (item 3).** Write `W(s) = A_1(s) ... A_N(s)` with `N = 4g`, where each `A_j` is one
of the `x_l` or `x_l*`, and each `x_l` occurs exactly once plain and once starred.
- *A uniform arc.* `s -> ||W(s) - 1||` is continuous on `[0,1]`, so it is `<= c` for some `c < 2`, and every
  spectrum lies in `K_c`.
- *A fixed contour.* Choose an open `U` containing `K_c` and disjoint from `(-infinity, 0]`, and a cycle `gamma` in
  `U \ K_c` winding once around each point of `K_c`. Then
  `log W(s) = (1/(2 pi i)) oint_gamma log z (z - W(s))^(-1) dz`. The resolvents are bounded uniformly on
  `gamma x [0,1]` by `1/dist(gamma, K_c)`.
- *Differentiate.*

  ```text
  d/ds log W = (1/(2 pi i)) oint_gamma log z (z - W)^(-1) W' (z - W)^(-1) dz.
  ```

  Apply `tau_A` and use cyclicity:
  `d/ds tau_A(log W) = tau_A(X W')`, where `X = (1/(2 pi i)) oint_gamma log z (z - W)^(-2) dz`.
- *Integrate by parts.* `log` is single-valued on `U`, so `X = (1/(2 pi i)) oint_gamma z^(-1) (z - W)^(-1) dz`,
  which is `W^(-1)`. Hence `d/ds tau_A(log W) = tau_A(W^(-1) W')`.
- *Telescoping.* `W' = sum_j A_1 ... A_j' ... A_N`. By cyclicity,
  `tau_A(W^(-1) A_1 ... A_j' ... A_N) = tau_A(A_j^(-1) A_j')`. For the pair `x, x*`: differentiating `x* x = 1`
  gives `(x*)' = -x* x' x*`. So `tau_A(x (x*)') = -tau_A(x x* x' x*) = -tau_A(x' x*) = -tau_A(x* x')`, which cancels
  `tau_A(x^(-1) x')`. The sum is `0`.

**Step 6: rounding criterion (item 4).** For each letter `y`:
- *The path.* `||theta(Pi(y))* v_y - 1|| = ||v_y - theta(Pi(y))|| <= delta < 2`. So
  `L_y = log(theta(Pi(y))* v_y)` is a skew-adjoint principal logarithm. Put
  `u_y(s) = theta(Pi(y)) exp(s L_y)`. This is a smooth path of unitaries from `theta(Pi(y))` to `v_y`.
- *It stays close.* If the spectrum of `exp(L_y)` has angles in `[-phi_0, phi_0]`, `phi_0 < pi`, with
  `2 sin(phi_0/2) <= delta`, then `||u_y(s) - theta(Pi(y))|| = ||exp(s L_y) - 1|| <= 2 sin(s phi_0/2) <= delta`.

Let `W(s)` be the relator word in the `u_y(s)`.
- It has `4g` unitary factors, each within `delta` of its value at `s = 0`, starred factors included. So
  `||W(s) - W(0)|| <= 4 g delta`.
- `W(0) = theta(W_r(Pi))`, and by (Q5), `||W(0) - 1|| <= (6g-1) eps`. So `||W(s) - 1|| < 2` for all `s`.
- `W(1) = prod [v_(a_i), v_(b_i)] = 1`.

By Step 5 in `(M, tau_M)`, `tau_M(log W(0)) = tau_M(log 1) = 0`. By (Q3),
`tau(log W_r(Pi)) = tau_M(theta(log W_r(Pi))) = tau_M(log W(0)) = 0`.

For a homomorphism `Rho`, `prod [Rho(a_i), Rho(b_i)] = Rho(prod [a_i, b_i]) = Rho(e) = 1`, because `r = 1` in `Gamma`.
With `eps <= a_g` and `delta < 1/(4g)`, `(6g-1) eps + 4 g delta < 1 + 1 = 2`.

**Step 7: items 5 and 6.**
- *Item 5.* By item 4, every uniform `eps_0`-quasi-representation has `kappa^tau = 0`, so `w(eps_0) = 0`. By Step 3,
  `inf_W S_W(eps_0+) = 0`. So for each `c > 0` there are `W` and `eps_1 in (eps_0, a_g]` with
  `S_W(eps_1) < c eps_0 < c eps_1`.
  - Taking `c < nu/(2 pi)` gives the window-free (SSD). Since `nu/(2 pi) <= tau_W` (item 5 of
    `sp4-winding-ratio-is-an-infimum-over-scales`), this includes (SSD).
  - It also gives `inf_W inf_eps S_W(eps)/eps = 0`, which is `Theta_inf = 0` by item 3 there.
  - The deficit hole then follows through the route `sp4-winding-deficit-from-one-scale`.
- *Item 6.* If `P_op = R/Z`, item 5 of `sp4-winding-ratio-is-an-infimum-over-scales` gives
  `S_W(eps') >= nu eps'/(2 pi)` for all `W` and all `eps' in (0, a_g]`. So `inf_W S_W(eps+) >= nu eps/(2 pi)`. Step 3
  gives a uniform `eps`-quasi-representation `Pi` with `kappa^tau(Pi) >= nu eps/(2 pi) > 0`, and item 4 fails for
  this `Pi`.
