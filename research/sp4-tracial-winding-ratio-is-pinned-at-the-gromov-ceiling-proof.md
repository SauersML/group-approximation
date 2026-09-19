---
rg: 2
id: sp4-tracial-winding-ratio-is-pinned-at-the-gromov-ceiling-proof
kind: route
title: Replace the determinant in Lemma L by a derivative of tau-log, rerun the sharp budget in any tracial algebra, and match it against the twisted regular witnesses
target: sp4-tracial-winding-ratio-is-pinned-at-the-gromov-ceiling
requires:
  - sp4-winding-ratio-sharp-constant-is-gromov-dual
  - sp4-winding-deficit-fails-in-twisted-tracial-algebras
---

Notation of the target. `(A, tau)` is a unital C*-algebra with a tracial state. The first required node supplies
the relator cycle `c_r`, the telescoping of `W_r(pi)` into conjugated defects, the LP constants and their limits
(its items 4 and 5). The second supplies the witnesses `pi_t` in `A_t` (its items 1-3).

## Step 1: tracial Lemma L (item 1)

Let `U_1, ..., U_n` be unitaries in `A` with `sum_m ||U_m - 1|| < 2`.
- Each `U_m` has spectrum off `-1`. So `H_m = -i log U_m` is self-adjoint, with `||H_m|| < pi` and
  `||U_m - 1|| = 2 sin(||H_m||/2)`.
- Put `V_m(s) = exp(i s H_m)` and `U(s) = V_1(s) ... V_n(s)` for `s in [0,1]`. As in Step 1.2 of the sharp-constant
  proof, `||V_m(s) - 1|| <= ||U_m - 1||`, so `||U(s) - 1|| <= c := sum_m ||U_m - 1|| < 2`. The spectra of all
  `U(s)` lie in the compact arc `K = {|z| = 1, |z - 1| <= c}`, which avoids the slit `(-infinity, 0]`.
- *Derivative of `tau(log)`.* Let `f = log` on a neighbourhood `Omega` of `K` in the slit plane, and `Gamma_0` a
  contour in `Omega` around `K`. Then `f(U) = (1/2 pi i) oint f(lambda) (lambda - U)^-1 d lambda`. Differentiating
  the resolvent gives `(lambda - U)^-1 U' (lambda - U)^-1`. The trace property turns this into
  `tau((lambda - U)^-2 U')`, and integrating gives `d/ds tau(log U(s)) = tau(U(s)^-1 U'(s))`.
- *Evaluate.* `U' = sum_m V_1 ... V_(m-1) (i H_m V_m) V_(m+1) ... V_n`. Since `V_m` commutes with `H_m`,
  `U^-1 U' = sum_m X_m^* (i H_m) X_m` with `X_m = V_(m+1) ... V_n` unitary. So `tau(U^-1 U') = i sum_m tau(H_m)`.
- Hence `tau(log U(s)) = i s sum_m tau(H_m)`, as it vanishes at `s = 0`. At `s = 1` this is
  `sum_m tau(log U_m)`. QED

Also `tau(log(V U V^*)) = tau(V (log U) V^*) = tau(log U)` and `log U^* = -log U` when `-1` is not in the spectrum.
Since `log U` is skew-adjoint and `tau` is a state, `tau(log U)` lies in `i R`.

## Step 2: tracial sharp budget (item 2)

Let `pi : Gamma -> U(A)` be unital with defect `eps < min(1, 2/(6g-1))` on `W`. Put
`D(g,h) = pi(g) pi(h) pi(gh)^*` and `beta^tau(g,h) = (1/(2 pi i)) tau(log D(g,h))`, which is real and normalized.
- *Winding formula.* The telescoping of Item 1 of the sharp-constant proof is pure algebra in `U(A)`. It writes
  `W_r(pi)` as a product of `6g-1` unitaries, each a unitary conjugate of `D(q_m)^(sigma_m)` with `(q_m, sigma_m)`
  the terms of `c_r`, and each within `eps` of `1`. By Step 1, `||W_r(pi) - 1|| < 2` and
  `kappa_r^tau(pi) = <beta^tau, c_r>`.
- *Local cocycle.* The identity `D(g,h) D(gh,l) = Ad(pi(g))(D(h,l)) D(g,hl)` holds in `A`. For `(g,h,l)` in `T(W)`,
  each side is a product of two unitaries within `eps < 1` of `1`. Step 1 gives `delta beta^tau = 0` on `T(W)`.
- *Bound.* `log D(g,h)` has spectrum in `i [-2 arcsin(eps/2), 2 arcsin(eps/2)]`, and `|tau(x)| <= ||x||`. So
  `|beta^tau| <= a(eps)`.
- So `beta^tau / a(eps)` is feasible for `N_W`, and `|kappa_r^tau(pi)| <= a(eps) N_W` (the feasible set is
  symmetric). Taking the supremum gives `S_W^A(eps) <= a(eps) N_W`.

Integrality (`d beta - delta theta` integral) is not used and has no tracial analogue. That is why the bound is the
same as for the relaxation `R_W` of item 8 of the sharp-constant node.

## Step 3: pinning (item 3)

Upper bound: Step 2, since `a_g = 1/(6g-1) < min(1, 2/(6g-1))`.

Lower bound: for `eps in (0, a_g]`, item 3 of the twisted-tracial node gives `pi_(t(eps))` in `A_(t(eps))` with
defect `<= eps` on `W` and `|kappa_r^tau| = |k| t(eps)`, where `t(eps) = arcsin(eps/2)/(pi beta*_W)`. So
`|k| t(eps) = |k| a(eps)/beta*_W`.

## Step 4: the tracial ratio (item 4)

- `a(eps)/eps -> 1/(2 pi)` as `eps -> 0+`. Step 3 gives `tau_W <= Theta^tr(W) <= N_W/(2 pi)`.
- `S_W^tr` is nonincreasing in `W`, since a larger window adds constraints. So `Theta^tr_inf` exists.
- By items 4(d) and 4(e) of the sharp-constant node, `beta*_W` increases to `|k|/nu` and `N_W` decreases to `nu`.
  So `tau_W -> nu/(2 pi)` and `N_W/(2 pi) -> nu/(2 pi)`, and `Theta^tr_inf = nu/(2 pi)`.

## Step 5: reformulation (item 5)

- `(M_d, tr/d)` is a tracial algebra, and there `kappa_r^tau = kappa_r/d`. So `S_W(eps) <= S_W^tr(eps)`, and
  `Theta_inf <= Theta^tr_inf = nu/(2 pi)`. The first bullet follows from Step 4.
- If `P_op = R/Z`, item 5 of the sharp-constant node gives `Theta(W) >= tau_W` for every `W`, and item 6 gives
  `Theta_inf = nu/(2 pi) = Theta^tr_inf`.

QED.
