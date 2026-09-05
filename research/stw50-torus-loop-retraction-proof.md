---
rg: 2
id: stw50-torus-loop-retraction-proof
kind: route
title: Bott evaluation followed by a unit coefficient is a left inverse to the torus action
target: stw50-unit-retraction-splits-torus-loops
requires:
  - stw50-bott-and-rotation-unit-inputs
artifacts:
  - research/artifacts/stw50-rotation-loop-retraction-2026-09-04.md
---

Evaluation followed by multiplication by u_j* is a continuous based
map Aut(A)->U(A). It therefore induces a homomorphism on pi_1,
regardless of whether evaluation is a homomorphism of topological
groups. Compose with stabilized Bott and epsilon.

On the torus loop of winding vector n, its j-th unitary loop is
exp(2*pi*i*n_j*t)1_A, so the j-th coordinate is epsilon(n_j[1])=n_j.
This proves rho gamma_*=id. Since pi_1 of a topological group is
abelian, its subgroup gamma_*(Z^r) is a direct summand.
