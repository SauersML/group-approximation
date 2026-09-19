---
rg: 2
id: kazhdan-stabilizer-collapses-shared-pauli-sign
kind: claim
title: A Kazhdan stabilizer and finite orbit rank collapse the shared Pauli sign for exact actors
artifacts:
  - research/compactness-closes-exact-actor-pauli-window.md
distinct_from:
  shared-center-extraspecial-wreath-has-fd-invisible-spin-sector: that proves exact finite-dimensional invisibility by divisibility and quantifies the fixed-window multiplicity reservoir; this gives a dimension-free robust collapse when the actor coordinates are genuine and the ordered-pair orbit rank is finite.
  approximate-collapse-for-kt-compressor: that asks for image/commutant collapse for arbitrary approximate Kun--Thom actor coordinates; this closes the shared-sign step only after the actor has been made exact.
  property-t-does-not-kill-boolean-fiber-holonomy: that shows property T alone cannot monomialize an arbitrary multiplicity cocycle; this uses exact actor covariance, finite double-coset propagation, and compactness of one finite matrix algebra, not monomialization.
---

Let \(G\) act transitively on an infinite set \(X=G/\Gamma\). Assume:

- \(\Gamma\) has a finite Kazhdan set \(Q\) with constant \(\kappa>0\);
- the ordered-pair rank is finite, equivalently
  \[
  \Gamma\backslash G/\Gamma
  =\{\Gamma,\Gamma r_1\Gamma,\ldots,\Gamma r_s\Gamma\}.    \tag{KPS1}
  \]

Let \(\rho:G\to U(D)\) be an exact finite-dimensional unitary
representation, and let \(A,B,J\in U(D)\). Suppose, in normalized
Hilbert--Schmidt norm,
\[
 \|ABA^*B^*-J\|_2\le\delta,                              \tag{KPS2}
\]
\[
 \max_{q\in Q}
 \max\{\|A\rho(q)-\rho(q)A\|_2,\
       \|B\rho(q)-\rho(q)B\|_2\}
 \le\delta,                                              \tag{KPS3}
\]
and, for every \(\ell=1,\ldots,s\) and \(C,D_0\in\{A,B\}\),
\[
 \|C\rho(r_\ell)D_0\rho(r_\ell)^*
   -\rho(r_\ell)D_0\rho(r_\ell)^*C\|_2
 \le\delta.                                              \tag{KPS4}
\]
Then
\[
 \boxed{\ \|J-I\|_2\le 2\delta+\frac{16}{\kappa}\delta\ }. \tag{KPS5}
\]

The estimate is independent of the matrix dimension, the number of sites,
and the dimensions of all actor multiplicity spaces.

Consequently, in a shared-center Pauli wreath with a Kazhdan point
stabilizer and finitely many ordered-pair orbits, every asymptotic model
whose actor coordinates are genuine representations satisfies
\[
 \|J_n-I\|_2\longrightarrow0.                            \tag{KPS6}
\]
Thus the fixed-window multiplicity reservoir does not obstruct
shared-sign collapse in the coordinatewise-genuine actor regime.

The remaining qualification is essential. A general hyperlinear
approximation supplies actor matrices which are only asymptotically
multiplicative. Pointwise actor relations do not make the conjugates of
(KPS3)--(KPS4) uniform over a dimension-dependent choice of sites.
Upgrading arbitrary actor coordinates to the exact-actor situation above
is precisely an actor exactification or approximate-image-collapse theorem;
property \((T)\) by itself does not provide it. No nonhyperlinear group is
proved here.

DERIVATION
compactness-closes-exact-actor-pauli-window
