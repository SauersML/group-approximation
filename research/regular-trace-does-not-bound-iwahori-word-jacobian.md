---
rg: 2
id: regular-trace-does-not-bound-iwahori-word-jacobian
kind: claim
title: Regular trace does not bound the Iwahori restriction Jacobian away from zero
artifacts:
  - research/pauli-branch-and-congruence-tensor-give-low-angle.md
distinct_from:
  iwahori-uniform-infinitesimal-rigidity: that proves a uniform gap for the coupled Mayer--Vietoris mismatch at compatible congruence endpoints; this gives vanishing singular values for either single-vertex restriction chart at regular-character nonendpoint models.
  iwahori-two-loci-have-zero-uniform-angle: that gives a nonlinear same-dimensional strict boundary family near the exact intersection; this is an exact tangent calculation and survives tensoring to the regular character face.
  residual-finite-tensor-camouflages-iwahori-transfer-failures: that preserves an abstract tensor-stable obstruction; this supplies an explicit Pauli restriction-Jacobian obstruction and its exact singular estimate.
---

Let
\[
 V=\operatorname{PSL}_2(\mathbb Z)=
 \langle x,a\mid x^2=a^3=1\rangle
\]
and write the index-three Iwahori subgroup as
\[
 H=\langle u,e\mid e^2=1\rangle,\qquad
 u=xa,\quad e=axa^{-1}.
\]
There is a sequence of exact representations
\[
 \Pi_n:V\longrightarrow U(d_n)
\]
whose normalized characters converge pointwise to the regular character,
whose order-two and order-three generators have the regular spectral
multiplicities, and for which the least positive singular value of the
differential
\[
 d\operatorname{Res}_{\Pi_n}:
 T_{\Pi_n}\operatorname{Hom}(V,U(d_n))
 \longrightarrow
 T_{\Pi_n|H}\operatorname{Hom}(H,U(d_n))                 \tag{RTJ1}
\]
tends to zero.

More precisely, for every
\(\theta\neq\pi/4\) there is a two-dimensional representation
\(\rho_\theta\) for which \(d\operatorname{Res}_{\rho_\theta}\) is injective
and
\[
 s_{\min}(d\operatorname{Res}_{\rho_\theta})
 \leq \sqrt{3/2}\,|\cos(2\theta)|.                       \tag{RTJ2}
\]
At \(\theta=\pi/4\) the differential has a one-dimensional kernel. If
\(\theta_n\to\pi/4\), \(\theta_n\neq\pi/4\), and \(\lambda_{Q_n}\) are
regular representations of separating odd congruence quotients of \(V\),
then
\[
 \Pi_n=\rho_{\theta_n}\otimes\lambda_{Q_n}               \tag{RTJ3}
\]
has regular limiting character and retains the singular value in (RTJ2)
exactly on the reducing tangent sector
\(M_2\otimes\mathbb C1\). The witnessing Pauli tangent is invertible on the
whole tensor-product Hilbert space and has uniformly bounded operator norm;
it is not a vanishing-rank operator-space outlier.

The Iwahori Nielsen map
\[
 \alpha(u)=u^{-1}e,\qquad \alpha(e)=u^{-1}eu
\]
is uniformly bi-Lipschitz on Hilbert--Schmidt representation coordinates.
Consequently the same vanishing holds after applying the opposite
Iwahori twist.

Thus Haar/free or regular-character moments alone cannot prove a uniform
lower bound for the two separate restriction Jacobians. The theorem does
**not** give a Dogon--Vigdorovich countersequence: the Pauli base point is
not a compatible arithmetic endpoint, and the full coupled mismatch at
compatible congruence endpoints has the established uniform arithmetic gap.
A counterexample would still require nonlinear integration together with
global incidence of the two twisted loci. The root remains open.

DERIVATION
pauli-branch-and-congruence-tensor-give-low-angle
