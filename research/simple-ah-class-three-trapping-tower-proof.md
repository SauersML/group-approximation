---
rg: 2
id: simple-ah-class-three-trapping-tower-proof
kind: route
title: Run Toms's Grassmannian trapping tower over T^2 x S^3 and read the eta-squared commutator in spin bordism at every stage
target: simple-ah-algebra-with-class-three-component-group
requires:
  - trapped-spin-bordism-class-over-any-spin-seed-factor
  - eta-squared-commutator-has-nonzero-spin-bordism-class
  - toms-trapped-spin-bordism-class
artifacts:
  - research/artifacts/class-three-spin-bordism-trapping-2026-09-12.md
  - research/artifacts/class-three-spin-bordism-trapping-part2-2026-09-12.md
---

Tower (Part 2, Section 4). Start with X_1 = Gr_2(C^4) and Q_1 = zeta_1, and
put Y_i = T^2 x S^3 x X_i, E_i = C^2 (+) Q_i. Pass from X_i to
X_{i+1} = X_i x Gr_2(C^{2d_i+2}), adding multiplicity bundles V (x) zeta.
The connecting maps are phi_i(a) = alpha_i^* a (+) (+)_l a(z_{i,l}) (x) 1,
with evaluation sets dense in every earlier base. Toms Proposition 5.2 keeps
dim X_i = 4 rank Q_i, X_i simply connected and spin, and
<c_{r_i}(Q_i)^2, [X_i]> = 1.

Witness. The triple commutator of alpha(s_1) (+) 1, alpha(s_2) (+) 1 and
omega(z) (+) 1 is w_1 = (c o pr) (+) 1_{Q_1}. The evaluation blocks contract
in the connected groups U(V), so phi_{1,j}(w_1) is homotopic to
w_j = (c o pr) (+) 1_{Q_j}.

Detection. By the seed-factor prerequisite with M = T^2 x S^3,
nu(w_j) = 1·[T^2 x S^3, c]_red and nu(1) = 0. The eta-squared prerequisite
makes the class nonzero, so w_j is not in U_0(A_j) at any stage. If the limit
w were in U_0(A), Toms Lemma 7.1 would put some phi_{1,j}(w_1), and hence
w_j, in U_0(A_j). That is impossible.

Simplicity: Toms Lemma 6.3. The fullness argument of his Proposition 6.4 uses
only density of the evaluation sets.

Stable finiteness: a tracial state exists by compactness, and simplicity
makes it faithful. Order two: [cbar] has order two in pi_5(S^3). K_1 class:
w is a commutator. M_2: diag(x, 1) and diag(1, x) agree modulo U_0, so
commutators of such elements vanish there.
