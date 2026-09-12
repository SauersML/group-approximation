---
rg: 2
id: monomial-kazhdan-hnn-is-rf-but-non-rfd-and-not-vfhs-stable
kind: claim
title: A monomial Kazhdan HNN host is residually finite but neither C-star RFD nor very-flexibly HS-stable
artifacts:
  - research/monomial-kazhdan-hnn-host-screen-proof.md
distinct_from:
  monomial-ascending-hnn-coset-action-sofic: that constructs finite action charts; this converts those charts and the strict-compressor wall into exact actor stability obstructions.
  one-kt-compressor-has-pauli-microstates-with-low-band-leakage: that disproves mixed-return normalization on Pauli-compatible microstates; this records the resulting failure of very-flexible HS stability and proves residual finiteness of the actor.
  strict-kazhdan-compressor-forces-non-rfd: that is the general maximal-C-star obstruction; this applies it to the concrete one-compressor Kun--Thom host and combines it with the marked Pauli model.
---

**ESTABLISHED CONCRETE HOST SCREEN; LLP IS NOT DECIDED.**

Let \(k=\mathbb F_q\), let \(\ell,d\ge3\), and put
\[
 \Gamma=\operatorname{EL}_{\ell}
       (k[x_1,\ldots,x_d]).
\]
Let \(T\in\operatorname{SL}_d(\mathbb Z)\) have nonnegative entries and
assume
\[
       T\mathbb N^d<\mathbb N^d.
\]
The induced monomial map gives a proper injective endomorphism
\(\alpha_T:\Gamma\to\Gamma\).  Form the ascending HNN extension
\[
 V_T=\langle\Gamma,t\mid
       t\gamma t^{-1}=\alpha_T(\gamma)\quad(\gamma\in\Gamma)\rangle.
                                                               \tag{MHS1}
\]
Then:
\[
\boxed{
\begin{array}{c|c}
\text{property of }V_T&\text{status}\\ \hline
\text{residually finite as a group}&\textbf{yes}\\
\text{sofic and hyperlinear}&\textbf{yes}\\
C^*_{\max}(V_T)\text{ RFD}&\textbf{no}\\
\text{very-flexible normalized-HS stability}&\textbf{no}.
\end{array}}                                                  \tag{MHS2}
\]
In particular \(V_T\) is not flexibly HS-stable and not ordinary
HS-stable either.

Residual finiteness is detected by finite exponent tori.  The kernel of
the exponent map \(V_T\to\mathbb Z\) embeds in
\[
 \operatorname{EL}_{\ell}(k[\mathbb Z^d]).
\]
For \(M\ge1\), reduction of exponents modulo \(M\) gives the finite ring
\[
 A_M=k[(\mathbb Z/M\mathbb Z)^d].
\]
Since \(\det T=1\), \(T\) acts by an automorphism of \(A_M\), and hence
there are finite quotients
\[
 V_T\longrightarrow
 \operatorname{EL}_{\ell}(A_M)\rtimes\langle T\bmod M\rangle. \tag{MHS3}
\]
A sufficiently large \(M\) keeps the finitely many Laurent monomials in
any prescribed nonzero matrix entry distinct.  These quotients separate
the exponent-zero kernel; cyclic quotients of the exponent map separate
all remaining elements.

The RFD failure is stronger and of a different nature.  The group
\(\Gamma\) is Kazhdan and
\[
          t\Gamma t^{-1}=\alpha_T(\Gamma)<\Gamma.
\]
Therefore the strict-compressor Kazhdan-projection theorem gives a nonzero
projection
\[
 e=t p_\Gamma t^{-1}-p_\Gamma\in C^*_{\max}(V_T)          \tag{MHS4}
\]
which every finite-dimensional representation kills.  Thus residual
finiteness of the group does not upgrade to residual finite-dimensionality
of its full group C-star algebra.  Property FD fails as well.

Finally let \(X=V_T/\Gamma\), let \(P_X\) be the common-center Pauli group,
and set
\[
                    \Pi_T=P_X\rtimes V_T.                 \tag{MHS5}
\]
The monomial action theorem and the marked Pauli chart theorem give
\[
                    \Pi_T\text{ is sofic}.                \tag{MHS6}
\]
Its canonical matrix models keep the common central involution \(J\) at
normalized-HS distance \(\sqrt2\) from the identity.  If \(V_T\) were
very-flexibly HS-stable, its restriction in those models would admit exact
finite-dimensional actor corner dilations on the fixed packet
\(Q\cup\{r_0\}\), where
\[
 \gamma_0\in\Gamma\setminus\alpha_T(\Gamma),\qquad
 r_0=t^{-1}\gamma_0t.
\]
The dimension-free mixed-return estimate would then force
\[
                    \|J-I\|_2\longrightarrow0,            \tag{MHS7}
\]
contradicting (MHS6).  This proves the last line of (MHS2).

Thus the proposed design strategy cannot obtain the needed actor by taking
an ascending HNN extension of a Kazhdan polynomial elementary group.  The
strict compressor itself destroys RFD, and the concrete sofic Pauli
extension simultaneously refutes even arbitrary-padding finite-corner
HS stability.  Whether \(C^*_{\max}(V_T)\) has LLP remains open and is not
needed for either negative conclusion.
