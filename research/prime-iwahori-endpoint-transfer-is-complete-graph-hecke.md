---
rg: 2
id: prime-iwahori-endpoint-transfer-is-complete-graph-hecke
kind: claim
title: The prime Iwahori endpoint transfer is the complete-graph Hecke operator
distinct_from:
  regular-hecke-transfer-has-finite-fourier-sector-lmis: that gives abstract whole-group multiplicity matrices for every supplied extender; this computes those matrices and their canonical top isometry on the regular endpoint orbit.
  regular-hecke-second-moment-is-intersection-energy: that computes the sum of squared singular values from the double-coset intersection; this gives every singular value at a prime endpoint.
  regular-congruence-endpoint-orbit-has-uniform-selberg-retraction: that retracts after a congruence endpoint has been selected; this gives the exact finite Hecke normal form at the selected regular endpoint.
---

Let \(G=\langle B,x\rangle\) be finite with \(x=x^{-1}\), and let

\[
D=(\lambda_G(B))',\qquad
T_0(A)=E_D(\lambda_G(x)A\lambda_G(x)).
\]

There is a concrete unitary coordinate model

\[
L^2(D)\cong
 \ell^2(B\backslash G)\otimes\ell^2(G)                \tag{PCG1}
\]

in which

\[
T_0=M_{B,x}\otimes1_{\ell^2(G)},                      \tag{PCG2}
\]

where the normalized double-coset Hecke operator is

\[
(M_{B,x}f)(Bh)
 =\frac1{|B|}\sum_{b\in B}f(Bxb^{-1}h).               \tag{PCG3}
\]

The coordinate map sends \(A\in D\) to the function

\[
a_A(Bh,u)=A_{hu^{-1},h},                              \tag{PCG4}
\]

with the evident scalar normalization. Simultaneous left \(B\)-invariance
of the matrix coefficients makes (PCG4) well defined. In these coordinates,
the canonical top space \(\lambda_G(G)'\) consists exactly of functions
which are constant in the \(B\backslash G\) coordinate.

After Fourier transform in the \(G\)-coordinate, the sector matrix from
'regular-hecke-transfer-has-finite-fourier-sector-lmis' is therefore

\[
K_{\pi,\lambda(x)}
 =M_{B,x}\otimes1_{d_\pi}
\quad\text{on }\mathbb C^q\otimes\mathbb C^{d_\pi}.    \tag{PCG5}
\]

Its canonical top subspace is the range of the isometry

\[
J_\pi:\mathbb C^{d_\pi}\longrightarrow
 \mathbb C^q\otimes\mathbb C^{d_\pi},\qquad
J_\pi v=q^{-1/2}{\bf1}_q\otimes v.                    \tag{PCG6}
\]

If \(G=\operatorname{PSL}_2(\mathbb F_p)\), \(p\) is odd, \(B\) is the
standard Borel, and \(x\) is the Weyl involution, then
\(q=p+1\) and

\[
M_{B,x}=\frac{{\bf J}_q-1_q}{p}.                      \tag{PCG7}
\]

Indeed, \(B\cap xBx\) is the split torus, of index \(p\) in \(B\);
the double coset sends each point of \(B\backslash G\) uniformly to every
other point. Consequently

\[
\operatorname{spec}(M_{B,x})
 =\{1,\,-1/p\},                                       \tag{PCG8}
\]

with the eigenvalue \(1\) simple and the eigenvalue \(-1/p\) of
multiplicity \(p\). Thus every Fourier sector has a dimension-free top
gap

\[
\gamma_p=1+\frac1p\geq1.                              \tag{PCG9}
\]

The formula is equivariant over the whole regular endpoint orbit. If
\(U\in U(D)\) and

\[
Y=U^*\lambda_G(x)U,
\]

then

\[
T_YR_U=R_UT_0,\qquad
T_Y=R_UT_0R_U^*.                                      \tag{PCG10}
\]

Hence the top isometry in the \(\pi\)-sector is
\(\sigma_\pi(U)J_\pi\).

Equations (PCG7)--(PCG10) identify the exact graph to which a
Davis--Kahan argument would compare a supplied near-top module. The
endpoint gap itself is completely uniform; any failure of such an argument
must occur before spectral perturbation, in deriving operator control of
\(T_X-T_Y\) from normalized-Hilbert--Schmidt relation defects or in turning
an \(L^2\)-close graph into a module-compatible Kraus frame.

DERIVATION
prime-iwahori-complete-graph-hecke-proof
