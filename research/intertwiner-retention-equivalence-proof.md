---
rg: 2
id: intertwiner-retention-equivalence-proof
kind: route
title: Conjugation model for the converse; sector characters are positive definite and Kazhdan-rigid
target: intertwiner-retention-is-equivalent-to-hyperlinearity
requires:
  - intertwiner-retention-makes-leavitt-quotient-hyperlinear
  - universal-leavitt-el4-nonsofic
---

**(1)**  The direction "sector implies hyperlinear" is
`intertwiner-retention-makes-leavitt-quotient-hyperlinear`.  Conversely let
`sigma_n : Q -> U(d_n)` be canonical microstates (`||sigma_n(ab) -
sigma_n(a) sigma_n(b)||_2 -> 0`, `tr sigma_n(a) -> delta_(a,1)`).  Define
`u_n` on a free basis `x_j` of `F` by `u_n(x_j) = sigma_n(q(x_j))`; this is an
exact representation of `F`, and by asymptotic multiplicativity
`||u_n(f) - sigma_n(q(f))||_2 -> 0` for every fixed `f`.  Put `v_n = u_n`
and `W_n = HS(C^(d_n))`.  Then `Pi_n(f) = u_n(f) (x) conj(u_n(f))`, whose
normalized trace on `C^(d_n) (x) conj(C^(d_n))` is `|tr u_n(f)|^2`, so
`||Pi_n(f) - 1||_(2,d_n^2)^2 = 2 - 2 |tr u_n(f)|^2`.  For `f in K`,
`tr u_n(f) -> tr sigma_n(1) = 1`; for `f notin K`, `tr u_n(f) -> 0`.  (IR1)
holds with `P_n = 1`, (IR2) and (IR3) follow.

**(2)** is a comparison of hypotheses, no proof needed.

**(3)**  `phi_n(f) = r_n^(-1) Tr(P_n Pi_n(f) P_n) = r_n^(-1) sum_i <Pi_n(f) e_i, e_i>`
over an orthonormal basis of `W_n` is an average of diagonal matrix
coefficients of the exact unitary representation `Pi_n` of `F`, hence a
normalized positive-definite function on `F`.  By (IR2),
`|phi_n(fk) - phi_n(f)| <= ||(Pi_n(k) - 1) P_n||_(2,r_n) -> 0` for fixed
`k in K`, and similarly on the left, so every ultralimit `phi` of `(phi_n)`
is a normalized positive-definite function on `Q`.  Since
`||(Pi_n(f) - 1) P_n||_(2,r_n)^2 = 2 - 2 Re phi_n(f)`, the hypothesis
`max_S ||(Pi_n(s) - 1)P_n|| -> 0` says `phi(s) = 1` on the generating set
`S`.  In the GNS representation of `phi` the cyclic vector is then fixed by
`S`, hence by `Q`, so `phi = 1` identically (this uses only that `S`
generates; property (T) of `Q`, from `universal-leavitt-el4-nonsofic`, gives
the quantitative version: `Re phi(s) >= 1 - epsilon` on `S` forces
`|1 - phi(g)| <= C(kappa) sqrt(epsilon)` for all `g`, so the conclusion is
stable under small generator defects).  Hence
`||(Pi_n(f) - 1) P_n||_(2,r_n) -> 0` for every `f`, contradicting (IR3)
unless the generator defect is bounded below along the sequence.
