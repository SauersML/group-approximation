---
rg: 2
id: split-edge-asymmetric-amalgams-are-operator-mf
kind: claim
title: Two split edge maps make an asymmetric amalgam operator MF
artifacts:
  - research/diagonal-envelope-from-two-edge-retractions.md
distinct_from:
  common-mf-envelope-fences-asymmetric-amalgams: that assumes a synchronized common MF envelope; this constructs one canonically from two edge retractions.
  shulman-amalgam-mf-criterion: that gives an exact C*-corona criterion; this is an elementary group-theoretic sufficient condition for split extensions.
  kazhdan-edge-terminal-sign-remains-hyperlinear: that analyzes one property-(T) edge by a transverse finite splitting; this applies to every split property-(T) edge without rewriting the amalgam.
---

**ESTABLISHED OPERATOR-NORM FIREWALL; HYPERLINEARITY NOT DECIDED.**

Let \(\theta_i:H\hookrightarrow G_i\) be injections of countable groups.
Assume that both split: there are homomorphisms
\[
r_i:G_i\longrightarrow H,\qquad r_i\theta_i=\operatorname{id}_H.
                                                               \tag{SER1}
\]
If \(G_0\) and \(G_1\) are operator MF, then
\[
G_0*_{\theta_0,\theta_1}G_1
\quad\text{is operator MF}.                              \tag{SER2}
\]

Indeed \(G_0\times G_1\) is operator MF, and the injections
\[
\begin{aligned}
j_0(g)&=(g,\theta_1r_0(g)),\\
j_1(k)&=(\theta_0r_1(k),k)
\end{aligned}                                            \tag{SER3}
\]
agree on \(H\). The common-envelope theorem embeds the asymmetric amalgam
in the symmetric double of \(G_0\times G_1\).

The edge \(H\) may be nonamenable or have property \((T)\). Thus an
asymmetric graph of two semidirect products
\[
(N_0\rtimes H)*_H(N_1\rtimes H)
\]
cannot be an operator-MF counterexample when its vertices are operator MF.

For the terminal-sign architecture \(B=K\rtimes H\), the selector vertex
already retracts onto \(H\). Therefore the other, actor vertex must be
genuinely non-retracting. If the edge contains a central involution \(c\)
which every finite-dimensional representation of the actor kills, then a
retraction fixing \(c\) is impossible whenever \(H\) has a finite quotient
detecting \(c\): composing the retraction with that quotient would detect
\(c\) in a finite-dimensional actor representation. Exact
finite-dimensional invisibility is therefore useful here as a
**non-splitting certificate**, not as an HS modulus.

Nothing in (SER1)--(SER3) selects the canonical trace. The conclusion is only
operator MF; it neither proves nor refutes hyperlinearity, and the
nonhyperlinear root remains open.

DERIVATION
diagonal-envelope-from-two-edge-retractions
