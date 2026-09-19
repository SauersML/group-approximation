---
rg: 2
id: regular-hecke-transfer-has-finite-fourier-sector-lmis
kind: claim
title: The regular Hecke transfer has finite Fourier-sector LMIs
distinct_from:
  regular-hecke-second-moment-is-intersection-energy: that gives a global double-coset budget for the singular values; this diagonalizes the transfer and its coverage dual over irreducible whole-group sectors.
  near-top-hecke-coverage-has-exact-hole-dual: that states one compressed right-multiplier SDP on all of L2(D); this splits that SDP into explicit finite sector inequalities.
  regular-core-window-is-a-hecke-kraus-hull: that diagonalizes the relative ucp selector through the core commutant; this uses the exact right-regular whole-group symmetry inside that commutant.
---

Let \(G=\langle B,x\rangle\) be finite, \(q=[G:B]\), and use the regular
finite-core notation

\[
D=(\lambda_G(B))',\qquad
T_X(A)=E_D(\lambda_G(x)AX).
\]

Write \(\varrho\) for the right regular representation of \(G\) on
\(\ell^2(G)\). Left multiplication on \(D\),

\[
{\mathsf L}_g(A)=\varrho(g)A,                          \tag{HFS1}
\]

is a unitary representation of \(G\), and

\[
L^2(D)\cong q\,\lambda_G
 \cong\bigoplus_{\pi\in\widehat G}
 V_\pi\otimes\mathbb C^{q d_\pi}.                     \tag{HFS2}
\]

Here the harmless choice between \(\pi\) and its contragredient is absorbed
by relabeling \(\widehat G\).

The transfer \(T_X\) commutes with (HFS1). Consequently there are uniquely
defined selfadjoint contractions

\[
K_{\pi,X}\in M_{q d_\pi}
\]

up to unitary change of multiplicity coordinates such that

\[
T_X\cong
 \bigoplus_{\pi\in\widehat G}
 1_{V_\pi}\otimes K_{\pi,X}.                          \tag{HFS3}
\]

For \(0\leq\epsilon<1\), put

\[
q_{\pi,\epsilon}
 =1_{[1-\epsilon,1]}(K_{\pi,X}).
\]

Then

\[
Q_\epsilon
 =1_{[1-\epsilon,1]}(T_X)
 \cong\bigoplus_\pi1_{V_\pi}\otimes q_{\pi,\epsilon},
\qquad
\operatorname{rank}(Q_\epsilon)
 =\sum_\pi d_\pi\operatorname{rank}(q_{\pi,\epsilon}). \tag{HFS4}
\]

Right multiplication by every \(Z\in D\) also commutes with (HFS1).
Therefore it has a simultaneous sector form

\[
R_Z\cong
 \bigoplus_{\pi\in\widehat G}
 1_{V_\pi}\otimes\sigma_\pi(Z),                       \tag{HFS5}
\]

where \(\sigma_\pi:D^{\rm op}\to M_{q d_\pi}\) is a unital
star-representation.

The optimal near-top coverage is thus exactly

\[
c_\epsilon
 =\min\left\{\tau(Z):
 \begin{array}{l}
 Z\in D,\ Z\geq0,\\
 q_{\pi,\epsilon}\sigma_\pi(Z)q_{\pi,\epsilon}
   \succeq q_{\pi,\epsilon}\quad(\pi\in\widehat G)
 \end{array}\right\}.                                 \tag{HFS6}
\]

The global singular-value budget also splits as

\[
\frac{\operatorname{Tr}(T_X^2)}{\dim_{\mathbb C}D}
 =
 \frac{\sum_\pi d_\pi\operatorname{Tr}(K_{\pi,X}^2)}
      {q|G|}.                                          \tag{HFS7}
\]

At the canonical endpoint \(X=\lambda_G(x)\), the exact top space is

\[
D\cap\{\lambda_G(x)\}'=\lambda_G(G)'=\mathbb C[G]^{\rm op}.
\]

As a left \(\varrho(G)\)-module this is one regular copy. Hence

\[
\operatorname{rank}(q_{\pi,0})=d_\pi
\quad\text{inside a multiplicity space of dimension }q d_\pi.        \tag{HFS8}
\]

Despite this \(1/q\) occupancy in every sector, the top space contains the
unit and has coverage one. Thus the arithmetic gate is not to create many
near-top vectors. It is to place approximately one coherent regular copy
across the sector multiplicities so that their products cover the unit.
Formula (HFS6) is the exact finite family of LMIs which must exclude a
subunit-trace positive majorant. No current uniform arithmetic estimate
does so, and the nonhyperlinear-group root remains open.

DERIVATION
regular-hecke-fourier-sector-lmi-proof
