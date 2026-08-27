---
rg: 2
id: hs-stability-from-ulam-stability-and-lifting
kind: route
title: Ulam stability plus tracial-to-uniform lifting gives flexible Hilbert-Schmidt stability
target: sln-z-flexibly-hs-stable
requires:
  - tracial-to-uniform-lifting-for-sl-n-z
---

Let `sigma_m : SL_N(Z) -> U(d_m)` have normalized-HS defect
`eps_m -> 0`, `N >= 3`.  The ultraproduct `pi = prod_U sigma_m` is
an exact representation into the tracial ultraproduct `M = A / I`.

**Step 1 (lift).**  By the required claim there is a vanishing
corner `Q` and a lift `tilde pi` into `U(Q A Q)`; unwinding the
ultraproduct, there are corner projections `Q_m` with
`tau(1 - Q_m) -> 0` and maps `sigma'_m : SL_N(Z) -> U(Q_m H_m)` with
OPERATOR-norm defect `eta_m -> 0` and `|| sigma'_m(s) - Q_m
sigma_m(s) Q_m ||_2 -> 0` on generators.

Only the lifting claim is consumed.  The linearized shadow
`abelian-lifting-obstruction-vanishes-for-sl-n-z` (vanishing of
`H^2_b(Gamma, I)`) is NOT an input: the defect of a set-theoretic lift is a
nonabelian `U(A) cap (1 + I)`-valued cocycle, additive only modulo `I . I = I`,
so the additive class is never the object to be killed, and the route is
valid from the lifting claim alone.  The abelian node stays as the recorded
first-order heuristic (and its own open `(ALO-GAP)` audit), off this route.

**Step 2 (Ulam stability).**  Burger--Ozawa--Thom (`SL_n(Z)`,
`n >= 3`): there are exact representations `rho_m` on `Q_m H_m` with
`|| rho_m(s) - sigma'_m(s) ||_op <= C eta_m`; Glebsky--Lubotzky--
Monod--Rangarajan [arXiv:2301.00476] give the same for most
high-rank lattices.

**Step 3 (conclude).**  Operator distance dominates normalized-HS
distance, so `|| rho_m(s) - sigma_m(s) ||_2 -> 0` on the corner
`Q_m` of co-trace `-> 0`: flexible HS-stability, the target.  The
converse reduction is immediate, so this route is an equivalence:
for Ulam-stable groups the entire content of HS-stability is the
lifting claim.  Downstream, HS-stability of `SL_N(Z)` removes the
outlier sector of the correctability hole at rank `N`, and with the
rank-generic Weyl sector theorem and the Lambda-exact face analysis
at a prime with `(p,p)_p = -1` gives the relative commutant collapse
and the non-hyperlinearity of the coset wreath group over that
pair.
