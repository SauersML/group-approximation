---
rg: 2
id: edge-commutant-gauge-gives-pauli-normal-form
kind: route
title: Integrate the Pauli kernel and diagonalize its transverse normal form
target: pauli-kernel-integrates-and-has-quadratic-crossing
requires:
  - regular-trace-does-not-bound-iwahori-word-jacobian
  - finite-dimensional-dual-of-sl2-z-inverse-two-is-odd-congruence
---

# Exact gauge integration and the transverse crossing

Use the Pauli matrices \(\sigma_x,\sigma_y,\sigma_z\). At
\(\theta_0=\pi/4\),
\[
 A_0=-{1\over2}1+i{\sqrt3\over2}\sigma_x,\qquad X=\sigma_z.
\]
Direct multiplication gives
\[
 U_0=XA_0=-{\sqrt3\over2}\sigma_y-{1\over2}\sigma_z,
 \qquad
 E_0=A_0XA_0^{-1}=U_0.                                  \tag{1}
\]
Call this common Hermitian involution \(C\).

Put \(H_0=-iC/\sqrt6\). Since \(H_0\) commutes with \(C\), simultaneous
conjugation by \(W_s=\exp(sH_0)\) fixes both words in (1), proving (PKN2).
Moreover
\[
 H_0-\operatorname{Ad}X(H_0)
 =H_0-\operatorname{Ad}A_0(H_0)
 ={i\sigma_y\over\sqrt2}=B_1.                           \tag{2}
\]
The right-logarithmic derivative of simultaneous conjugation is therefore
the kernel vector found in the restriction-Jacobian calculation. Equation
(1) proves more than vanishing through cubic order: the whole analytic path
is inside one exact restriction fiber.

Substitution of \(\theta_0\) in the four-by-four Pauli Gram matrix from the
preceding route gives characteristic polynomial
\[
 t(t-2)\bigl((t-4)^2-6\bigr).
\]
This proves (PKN3), including the positive normal gap after the exact kernel
is removed.

For the transverse calculation, write
\[
 q=\sin(2\theta),\qquad c=\cos(2\theta).
\]
The Pauli vector of \(C\) is
\[
 {\bf c}=(0,-\sqrt3/2,-1/2).
\]
The involution \(E_\theta=A_\theta X A_\theta^{-1}\) has Pauli vector
\[
 {\bf e}_\theta=
 \left({3\over2}cq,-{\sqrt3\over2}q,
       -{1\over2}+{3\over2}c^2\right).                  \tag{3}
\]
Consequently
\[
 |{\bf c}\mathbin{\times}{\bf e}_\theta|^2
 ={3\over16}(1-q-3c^2)^2+{9\over4}c^2q^2.               \tag{4}
\]
For \(\theta\) near \(\theta_0\), equation (4) is bounded above and below by
fixed positive multiples of \(c^2\).

Conjugation by
\[
 W_s=\exp(-isC/\sqrt6)
\]
rotates Pauli vectors around \({\bf c}\) through angle \(2s/\sqrt6\).
Normalized Hilbert--Schmidt norm agrees with Euclidean norm on Pauli
vectors, hence
\[
 \|W_sE_\theta W_s^*-E_\theta\|_{2,2}
 =2|{\bf c}\mathbin{\times}{\bf e}_\theta|
   |\sin(s/\sqrt6)|.                                    \tag{5}
\]
The corresponding formula for \(U_\theta=XA_\theta\) has a perpendicular
Pauli component of size
\[
 {\sqrt3\over4}|1-q|=O(c^2).
\]
Equations (4)--(5), together with
\[
 |c|\asymp|\theta-\theta_0|,\qquad
 |\sin(s/\sqrt6)|\asymp|s|,
\]
prove (PKN4).

In a sufficiently small parameter square, (PKN4) also shows that the zero
set is exactly
\[
 \{s=0\}\ \cup\ \{\theta=\theta_0\}.
\]
Its parameter distance is comparable to
\(\min(|s|,|\theta-\theta_0|)\), which is at most the square root of their
product. This proves (PKN5). Taking
\(|s|=|\theta-\theta_0|\) proves sharpness of exponent \(1/2\).

Finally, \(\rho_{\theta_0}\) is the faithful two-dimensional standard
representation of the mod-two quotient
\(\operatorname{PSL}_2(\mathbb F_2)\cong S_3\). If it extended to
\(\operatorname{PSL}_2(\mathbb Z[1/2])\), finite-dimensional endpoint
classification would force an odd principal congruence subgroup into its
kernel. Chinese remaindering maps every odd principal congruence subgroup
surjectively modulo two, contradicting faithfulness of the \(S_3\) image.
Thus the exact fiber above is not an arithmetic compatible endpoint.
