---
rg: 2
id: galois-games-round-through-free-subgroups-proof
kind: route
title: Orbit-representative transversal of G/H, isotypic splitting of the certificate, halving chain of kernels, Hilbert--Schmidt Markov bound
target: galois-games-round-through-free-subgroups
requires: [galois-unique-game-value-is-transversal-expansion]
artifacts:
  - research/artifacts/ugc-galois-games-part2-2026-09-12.md
---

Complete proofs are Theorems 7--8 and Corollary 9 of the artifact.

* **Duality.** `Stab_H(xK) = H cap x K x^-1`, and
  `Stab_K(yH) = y (y^-1 K y cap H) y^-1`.
* **Rounding.** `T = { g : g^-1 H in D }`, with `D` a set of `K`-orbit
  representatives in `G/H`. `Y(g a) = a^-1 Y(g)` runs once over an orbit, so `T`
  is a transversal. For `s in H`, `Y(s t) = Y(t)`, so `Phi_mu(T) <= mu(G \ H)`.
  The value formula of the required claim finishes.
* **Kernels.** The symmetric SDP formula of the required claim gives an
  admissible `phi`. Isotypic splitting gives `sum w_rho (1 - lambda_rho) <= eps`.
  So `w(B) <= 1/3` for `B = {lambda < 1 - 3 eps}`, and on
  `K cap (intersection of good kernels)`, `Re phi >= 1/3`. Hence that
  intersection is trivial. A chain that at least halves `K` at each step needs
  `<= log_2 k` representations. Their common kernel is normal and meets `K`
  trivially, hence every conjugate of `K` trivially.
* **Cost.** `E_mu |rho(s) - I|_HS^2 = 2 d (1 - lambda) <= 6 eps d`, and
  `|rho(g) - I|_HS^2 >= 2(1 - cos(2 pi/m))` off `ker rho`.
