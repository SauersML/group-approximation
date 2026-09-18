---
rg: 2
id: fpbs-cycle-tails-force-rank-gradient-equals-l2-betti-proof
kind: route
title: Sandwich the boundary-action cost between Gaboriau and Abert-Weiss, then apply Abert-Nikolov and Ershov-Luck
target: fpbs-cycle-tails-force-rank-gradient-equals-l2-betti
requires:
  - fpbs-bernoulli-maximal-cost
  - fpbs-amen2-betti-cost-input
  - fpbs-graphing-cost-betti-cycle-dimension-identity
  - fpbs-short-cycle-edge-measure-vanishes-near-optimum
artifacts:
  - research/artifacts/fpbs/docs/cost-betti-rank-gradient-calibration-2026-09-17.md
---

**(0)** The identity node gives z(Phi_n) = g + eps_n. The short-cycle node
bounds the edges on cycles of length at most L by measure L eps_n, so
z_L <= L eps_n. Hence g <= L eps_n + tau_L. Let n and then L tend to infinity.

**(i)** Let a be the boundary action of a Farber chain. It is essentially free
and p.m.p. Gaboriau (`fpbs-amen2-betti-cost-input`) gives
C(a) >= 1 + beta_1. Abert–Weiss (`fpbs-bernoulli-maximal-cost`) gives
C(a) <= C(b) = 1 + beta_1. Abert–Nikolov, arXiv:math/0701361v3, Theorem 1:
"Let (Γ_n) be a Farber chain in Γ. Then RG(Γ, (Γ_n)) = cost(E) − 1 where E
denotes the orbit relation given by the action of Γ on the boundary of the
coset tree T(Γ, (Γ_n))."

**(ii)** Use b_1(H;K) <= d(H). For the p-chains, Ershov–Lück,
arXiv:1206.0474v3, Theorem 1.6(2): "Assume that ∩_i G_i = {1}. Then
b_1^(2)(G) ≤ lim_(i→∞) b_1(G_i;F_p)/[G:G_i]."

**(iii)** Lück approximation (EL Theorem 1.1) for the Q-gradient. Then apply
the universal-coefficient chain b_1 <= b_1 + d_p(T) = b_1(F_p) <= b_1 + d(T)
= d(H_1) <= d(Gamma_n).

Quotes and all details are in Sections 1–3 of the artifact. This route imports
AN Theorem 1, EL Theorems 1.1 and 1.6, and the two established cost inputs.
It is not an independent formalization.
