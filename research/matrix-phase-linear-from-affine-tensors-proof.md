---
rg: 2
id: matrix-phase-linear-from-affine-tensors-proof
kind: route
title: Affine symmetrization and tensor powers linearize the qualitative matrix modulus
target: matrix-phase-linear-alpha-plane-inequality
requires:
  - matrix-phase-noncommutative-alpha-plane-route
artifacts:
  - research/artifacts/alpha-plane-affine-tensor-linearization-2026-09-04.md
  - experiments/alpha_plane_affine_tensor_check.py
  - experiments/alpha-plane-affine-tensor-check.json
---

Let E_t be the slope-t energy, so I=E_1, A=E_alpha and F=average_t E_t.
Hilbert-space variance, applied to x -> R_(x+b) R_x^*, gives
E_t<=2F at every slope and F<=2.

Choose epsilon_*>0 from the prerequisite so that I+A<=epsilon_* implies
F<=1/4. For a table R with f_0=F(R)>0 and delta_0=I(R)+A(R), dilute by
m=2|K| equal identity blocks and double by the complex conjugate. Its
energies are divided by m and its word traces are real. Write f=f_0/m and
beta=1-1/|K|. Direct-sum the table over Aff(K), then take its k-th tensor
power with k=ceil(beta/f).

The amplified slope energy is exactly

    2 beta [1-(1-E_t(R)/(2 m beta))^k].

The upper bound on each slope and the equality of their average with F
imply, by a concave-chord estimate, amplified full energy at least
beta(1-exp(-1))>1/4. Bernoulli's inequality gives amplified sampled energy
at most k delta_0/m <= delta_0/f_0, because kf<=beta+f<=1.

Thus delta_0/f_0<=epsilon_* contradicts the qualitative threshold.
Consequently F(R)<= (I(R)+A(R))/epsilon_* universally. All details,
including zero directions and repeated-point slopes, are in the artifact.

The independent qualitative route through scalar alpha-plane soundness
remains the prerequisite proof; the reverse linear-to-qualitative route
is not used. No numerical epsilon_* and no nonhyperlinear group are
asserted. The replay checks finite identities and cannot establish the
qualitative premise by computation.
