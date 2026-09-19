---
rg: 2
id: sp4-single-scale-deficit-from-ultraproduct-rounding
kind: route
title: Rounding uniform quasi-representations into the matrix ultraproduct at one scale gives the single-scale winding deficit with every constant
target: sp4-quasirep-single-scale-winding-deficit
requires:
  - sp4-ssd-is-a-matrix-ultraproduct-winding-bound
  - sp4-ultraproduct-quasireps-round-to-homs-at-one-scale
---

The notation is that of `sp4-ssd-is-a-matrix-ultraproduct-winding-bound`. Let `eps_0 in (0, a_g)` and
`delta < 1/(4g)` be as in (UQ) of `sp4-ultraproduct-quasireps-round-to-homs-at-one-scale`.

**Step 1: `w(eps_0) = 0`.** Let `Pi : Gamma -> U(Q)` be a uniform `eps_0`-quasi-representation. (UQ) gives
`theta : Q -> M`, `tau_M o theta = tau`, and a homomorphism `Rho` with `||theta(Pi(y)) - Rho(y)|| <= delta` on the
`2g` letters. Put `v_y = Rho(y)`. Then `prod [v_(a_i), v_(b_i)] = Rho(r) = 1`. Also

```text
(6g-1) eps_0 + 4 g delta  <  (6g-1) a_g + 1  =  2.
```

So item 4 of the reduction node applies and `kappa^tau(Pi) = 0`. Since `Pi` was arbitrary, `w(eps_0) = 0`.

**Step 2: back to matrices.** By item 1 of the reduction node, `inf_W S_W(eps_0+) = w(eps_0) = 0`. Fix any `c` with
`0 < c < nu/(2 pi)`. Item 5 of `sp4-winding-ratio-is-an-infimum-over-scales` gives `nu/(2 pi) <= tau_W` for every `W`,
so `c < tau_W`. Choose:
- a window `W`, containing `W_r`, with `S_W(eps_0+) < c eps_0`;
- then `eps_1 in (eps_0, a_g]` with `S_W(eps_1) < c eps_0`.

Then `S_W(eps_1) < c eps_1`. By the definition of `S_W`, every unital `pi : Gamma -> U(d)` with defect `<= eps_1` on
`W` has `|kappa_r(pi)| <= S_W(eps_1) d <= c eps_1 d`.

This is (SSD) for the relator `r`, the window `W` and the scale `eps_1`, with the constant `c < tau_W`. It is also the
window-free form, since `S_W(eps_1) < c eps_1 < eps_1 nu/(2 pi)`. As `c > 0` was arbitrary, (SSD) holds with every
positive constant.
