---
rg: 2
id: stw99-l-three-vertex-model-four-hom-loops-proof
kind: route
title: Split the K1 lattice with the j=3 edge actions, then read the table off equation (5)
target: stw99-l-three-vertex-model-four-hom-loops
requires:
  - stw99-l-row-unitaries-detect-edge-phase-actions
  - stw99-l-finite-graph-models-are-uct-kirchberg
---

*Integrality of `[U_1], [U_2]`.*  Take `j = n = 3` in equation (5):
`Delta_{g_{i3}}([U_k]) = delta_{ik} [p_3] = -delta_{ik} e_C`.  Compose
with minus the `e_C`-coordinate of `K_0(C) = Z e_C (+) Z b` to get
homomorphisms `phi_i : K_1(C) -> Z` with `phi_i([U_k]) = delta_{ik}`.
So `Z^2 -> K_1(C)`, `(m_1,m_2) |-> m_1[U_1] + m_2[U_2]`, has the left
inverse `(phi_1, phi_2)`; its image is a direct summand of the rank-two
free group `K_1(C)`, and a complement of a rank-two summand in a rank-two
free group is zero.  Hence the image is everything.

*The table.*  Equation (5) gives `Delta_{g_{13}}([U_1]) = [p_3] = -e_C`,
`Delta_{g_{11}}([U_1]) = [p_1] = b`, `Delta_{g_{23}}([U_2]) = -e_C`,
`Delta_{g_{21}}([U_2]) = b`, and zero for the other index; inverting the
phase in `h_1` and `h_3` negates `Delta`, turning `-e_C` into `e_C`.  The
vertex identities `[p_2] = 2e_C - b`, `[p_3] = -e_C` come from the
prerequisite.

*The `K_0` component.*  Each `g_{ij,z}` fixes every vertex projection, so
each fixed `p_i` has zero reduced class; the vertex classes generate
`K_0(C)`, so the `Hom(K_0/Z e_C, K_1)` component of all four loops is
zero.

*Basis.*  In the basis `{[U_1],[U_2]}` of `K_1(C)` and `{e_C, b}` of
`K_0(C)`, the four values are the four elementary matrix units of
`Hom(K_1(C), K_0(C))`.
