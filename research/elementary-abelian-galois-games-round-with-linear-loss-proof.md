---
rg: 2
id: elementary-abelian-galois-games-round-with-linear-loss-proof
kind: route
title: Bochner weights restrict uniformly to K-hat, high characters span, their common kernel is a cheap complement
target: elementary-abelian-galois-games-round-with-linear-loss
requires: [galois-unique-game-value-is-transversal-expansion]
artifacts:
  - research/artifacts/ugc-galois-games-2026-09-12.md
---

The complete proof is Theorem 4 and Propositions 5--6 of the artifact.

1. By the symmetric SDP formula of the required claim, there is a real
   positive-definite `phi` with `phi(0) = 1`, `phi = 0` on `K \ {0}` and
   `sum mu phi >= 1 - epsilon`. By Bochner, `phi = sum w_chi chi` with
   `w >= 0` and `sum w = 1`.
2. `phi|_K = delta_0`, so the push-forward of `w` to `Khat` is uniform by
   Fourier inversion on `K`.
3. `sum w_chi (1 - lambda_chi) <= epsilon`. With `eta = 2p epsilon/(p-1)`
   (`3 epsilon` for `p = 2`), the restrictions of the characters with
   `lambda >= 1 - eta` have density `> 1/p` in `Khat`. So they are not in a
   proper subgroup, and they contain a basis `psi_1..psi_r`.
4. Lift the basis to `chi_1..chi_r` and let `Y = (log_zeta chi_i)`. `Y|_K` is
   an isomorphism, so `T = ker Y` is a complement of `K`.
5. `Phi_mu(T) = Pr[Y(s) != 0] <= sum_i (1 - lambda_(chi_i))/(1 - cos(2 pi/p))`.
6. Tightness on Khot--Vishnoi uses
   `N Stab_rho[1_T] <= N alpha^(2/(1+rho))` with `alpha = 1/N` and
   `rho = 1 - 2 epsilon`, by Bonami--Beckner hypercontractivity. The cyclic
   example is a direct computation: odd holonomy forces a violated edge, and
   `phi = (1 + cos(pi x/n))/2` is admissible.
