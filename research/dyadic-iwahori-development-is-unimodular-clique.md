---
rg: 2
id: dyadic-iwahori-development-is-unimodular-clique
kind: claim
title: The Iwahori development is the dyadic unimodular-row clique complex
distinct_from:
  binary-iwahori-h1-vanishes-at-odd-levels: that obtains binary cohomology vanishing from a relative presentation and monodromy; this identifies the development directly with Hutchinson's clique complex and audits every finite triangle.
  proper-torus-diagonal-code-is-incomplete-cover-curl: that builds the finite cellular curl from cosets; this proves that its two face orbits exhaust the full refined clique two-skeleton, with the exact Mersenne multiplicity.
---

Put
\[
 A=\mathbb Z[1/2],\qquad A^\times=\{\mathord\pm2^j:j\in\mathbb Z\}.
\]
Let \(Y(A)\) be Hutchinson's clique complex: its vertices are unimodular
rows in \(A^2\) modulo multiplication by \(A^\times\), and two vertices
are adjacent when their determinant is a unit. If \(X\) is the coset
development with
\[
 X^{(0)}=P_\infty\backslash\Gamma,\quad
 X^{(1)}=N_\infty\backslash\Gamma,\quad
 X^{(2)}=(A_\infty\backslash\Gamma)\sqcup
         (B_\infty\backslash\Gamma),
\]
where
\[
 \Gamma=\operatorname{PSL}_2(A),\quad
 P_\infty=\langle r,t\rangle,\quad
 N_\infty=\langle r,x\rangle,
\]
\[
 A_\infty=\langle xt\rangle,\qquad
 B_\infty=\langle xt^2r\rangle,
\]
then there is a \(\Gamma\)-equivariant cellular isomorphism
\[
 X\cong Y(A)^{(2)}.                                    \tag{DUC1}
\]
In particular \(X\) contains every triangle of the refined graph, not
only a selected subfamily. Hutchinson's theorem and the universality of
\(\mathbb Z[1/2]\) for \(\mathrm{GE}_2\) give
\[
 \pi_1(X)=\pi_1(Y(A))=1.                              \tag{DUC2}
\]

There is an equally explicit finite statement. Let
\[
 m=4^n-1\quad(n\ge2),\qquad R=\mathbb Z/m\mathbb Z,
 \qquad L=\mathord\pm\langle2\rangle\le R^\times .
\]
The vertices of the finite Iwahori graph are unimodular rows in \(R^2\)
modulo \(L\), and two vertices are adjacent precisely when their
determinant lies in \(L\). Every 3-clique occurs in the union of the
\(A_m\)- and \(B_m\)-face rows. More precisely, through a fixed edge
the two face families have third-row ratios
\[
 \mathord\pm\langle4\rangle
 \quad\text{and}\quad
 \mathord\pm2\langle4\rangle,                        \tag{DUC3}
\]
whose disjoint union is \(L\). Each geometric triangle occurs exactly
twice as a cellular face: the two cells differ by the nonglobal scalar
involution \(c=r^n\). Consequently the duplicate cellular checks have
the same binary kernel as the full refined clique two-skeleton:
\[
 H^1(K_{H,m};\mathbb F_2)
 \cong H^1(\operatorname{Cl}(\Gamma_L(R));\mathbb F_2). \tag{DUC4}
\]

DERIVATION
dyadic-unimodular-clique-identification-proof
