---
rg: 2
id: binary-iwahori-h1-vanishes-at-odd-levels
kind: claim
title: Binary Iwahori first cohomology vanishes at every odd congruence level
distinct_from:
  first-mersenne-iwahori-levels-have-zero-binary-h1: that verifies m=15 and m=63 by exact elimination; this proves the identity at every odd level.
  iwahori-uniform-infinitesimal-rigidity: that is a characteristic-zero tangent statement; this eliminates the characteristic-two Smith obstruction by congruence subgroup rigidity.
  proper-torus-diagonal-code-is-incomplete-cover-curl: that identifies the exact cellular complex and leaves its cohomology open; this computes that cohomology, with all duplicate face rows retained.
---

**ESTABLISHED.** Let

\[
 \Gamma=\operatorname{PSL}_2(\mathbb Z[1/2])
\]

in the square-free coordinates \((x,r,t)\). For every odd integer \(m>1\),
let

\[
 q_m:\Gamma\longrightarrow
 G_m=\operatorname{SL}_2(\mathbb Z/m\mathbb Z)/\{+\!I,-I\}
\]

be reduction and put \(K_m=\ker q_m\). Define

\[
 P_\infty=\langle r,t\rangle,\quad
 N_\infty=\langle r,x\rangle,\quad
 A_\infty=\langle xt\rangle,\quad
 B_\infty=\langle xt^2r\rangle
\]

and denote their images in \(G_m\) by \(P_m,N_m,A_m,B_m\). For the
cellular complex \(K_{H,m}\) with

\[
 \begin{aligned}
 C^0&=\mathbb F_2[P_m\backslash G_m],\\
 C^1&=\mathbb F_2[N_m\backslash G_m],\\
 C^2&=\mathbb F_2[A_m\backslash G_m]\oplus
       \mathbb F_2[B_m\backslash G_m],
 \end{aligned}                                             \tag{BIH1}
\]

one has

\[
 H^1(K_{H,m};\mathbb F_2)=0.                              \tag{BIH2}
\]

Equivalently, every binary edge cochain satisfying both cubic parity rows
is a vertex cut:

\[
 Z^1(K_{H,m};\mathbb F_2)=B^1(K_{H,m};\mathbb F_2).       \tag{BIH3}
\]

The one-skeleton is connected, so if \(V_m=|P_m\backslash G_m|\), then

\[
 \dim_{\mathbb F_2}Z^1(K_{H,m};\mathbb F_2)=V_m-1.        \tag{BIH4}
\]

The proof has two independent parts. First, the exact relative Iwahori
presentation has a simply connected coset development \(X\), and
\(K_m\backslash X\) is exactly the complex in (BIH1). Pullback from the
quotient gives an injection

\[
 H^1(K_m\backslash X;\mathbb F_2)
 \hookrightarrow \operatorname{Hom}(K_m,\mathbb F_2).    \tag{BIH5}
\]

This remains valid although \(K_m\) has vertex stabilizers.

Second, Serre's congruence subgroup property implies

\[
 \operatorname{Hom}(K_m,\mathbb F_2)=0.                  \tag{BIH6}
\]

Indeed, the kernel of a hypothetical binary character contains a principal
congruence subgroup of an odd level \(j\) divisible by \(m\). After the
single global sign is normalized on the primes dividing \(m\), the finite
quotient \(K_m/K_j\) is a product of odd-primary congruence kernels and
groups \(\operatorname{SL}_2(\mathbb Z/q^a\mathbb Z)\) for new odd primes
\(q\). None has a quotient of order two.

At the corrected Mersenne levels \(m=4^n-1\),

\[
 |H_m|=2n,\qquad |N_m|=4n,\qquad |P_m|=2mn.
\]

The nonglobal central sign \(r^n\) gives distinct paired \(A_m\)- and
\(B_m\)-face cells with the same boundary. Both cells occur in (BIH1);
(BIH2) does not delete or merge the duplicate checks.

Thus the dimension hypothesis in
linear-cocycle-dimension-forces-phase-countersequence holds with the
sharp value \(\dim Z^1=V_m-1\). This closes the algebraic
phase-frustration gate and refutes the proposed diagonal Hamming decoder.
It does not show that the same cochains are far from nondiagonal exact
operator endpoints, and the non-hyperlinearity root remains open.

DERIVATION
relative-development-and-csp-kill-binary-h1
