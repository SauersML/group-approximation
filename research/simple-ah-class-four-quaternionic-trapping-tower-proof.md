---
rg: 2
id: simple-ah-class-four-quaternionic-trapping-tower-proof
kind: route
title: Run Toms's trapping tower over T^3 x S^3 with quaternionic Grassmannian steps and read eta cubed in BSpin_8-bordism at every stage
target: simple-ah-algebra-with-class-four-component-group
requires:
  - trapped-lambda-mod-eight-class-over-seed-factor
  - eta-cubed-commutator-has-nonzero-lambda-mod-eight-class
  - quaternionic-grassmannian-trapping-defect-is-rank
  - toms-trapped-spin-bordism-class
artifacts:
  - research/artifacts/class-four-lambda-mod-eight-trapping-part2-2026-09-13.md
---

Part 2, Section 5.

The stages are A_i = Gamma(End(C^2 (+) Q_i)) over T^3 x S^3 x X_i, with
X_1 = point. The step is X_{i+1} = X_i x Gr_8(H^{8+2d_i}),
Q_{i+1} = Q_i (+) d_i·zeta_i, where d_i = m_i·rank E_i. The connecting maps are
phi_i(a) = alpha_i^* a (+) (+)_l a(z_{i,l}) (x) 1_{zeta_i}, with evaluation
sets dense in every earlier base.

Invariants (Lemma 5.1): dim X_i = 4·rank Q_i, and
<c_top(Q_i)^2, [X_i]> = ±1. TX_i − W_{i,R} carries a BSpin_8-structure. This
is built as a sum, using the defect 8·q_1 ≡ 0 mod 8 of the Grassmannian
prerequisite.

Witness: w_i = (c_4 o pr) (+) 1_{Q_i}. The evaluation blocks contract in the
connected groups U(V), so phi_{1,j}(w_1) is homotopic to w_j. The trapped
prerequisite gives nu(w_j) = ±[T^3 x S^3, c_4]_red, which is nonzero by the
eta-cubed prerequisite, while nu(1) = 0. If the limit c were in U_0(A), Toms
Lemma 7.1 would put some w_j in U_0(A_j). That is impossible.

Simplicity: Toms Lemma 6.3, through the density argument of his
Proposition 6.4. Stable finiteness: a faithful trace. Order two:
[cbar_4] = 6 nu' has order two in pi_6(S^3). K_1 and M_2: c is a
commutator, and elements diag(x, 1) commute modulo U_0(M_2(A)).
