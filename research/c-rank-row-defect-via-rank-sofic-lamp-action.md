---
rg: 2
id: c-rank-row-defect-via-rank-sofic-lamp-action
kind: route
title: A C-rank-realized action moving a Gamma-invariant set gives a C-linear sofic lamp quotient with a rigid defect
target: c-linear-sofic-group-carries-nontrivial-rigid-defect
requires:
  - kt-pair-c-rank-sofic-action-moves-fixed-algebra
  - kt-wreath-rank-radical-is-rank-fixed-algebra-rigidity
---

Let `(Y, nu)`, `B` and `n in N` witness `kt-pair-c-rank-sofic-action-moves-fixed-algebra`.

1. Section 3 of `kt-wreath-rank-radical-fixed-algebra-proof` builds `pi : Y -> 2^(G/Gamma)` and a
   model `theta : W -> U(R_omega)` with `rk(theta(m_n) - 1) = nu(nB triangle B) > 0`.
2. With `mu = pi_* nu`, the kernel of `theta` on lamps is `N_mu`. The group `H = W/N_mu` embeds in
   `theta(W) x G`, so it is `C`-linear sofic.
3. `G <= H`, because `N_mu` consists of lamps. `Gamma` and `G` are Kazhdan and `Gamma` is infranormal
   in `G` (Kun--Thom Theorem E). The image `z` of `e_o` centralizes `Gamma`.
4. `m_n notin N_mu` and `N_mu` is `G`-invariant. By the cocycle `m_(ab) = m_a + a . m_b`, some seed
   commutator `[g z g^(-1), gamma] = g . m_(g^(-1) gamma g)` is nontrivial in `H`.

So `H` witnesses the target. By `sofic-groups-kill-rigid-compression-defects`, `H` is not sofic.
