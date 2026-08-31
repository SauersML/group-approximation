---
rg: 2
id: five-clifford-diagonal-spin-absorbs-the-full-orbit-lock
kind: claim
title: A diagonal spin model absorbs the full five-Clifford orbit lock
artifacts:
  - research/five-clifford-cyclic-phase-network-finite-model-proof.md
distinct_from:
  five-clifford-odd-orbit-cancels-phase-not-payload: that computes one orbit norm and exhibits an unconstrained cyclic multiplicity; this gives a single cyclic finite model satisfying every within-orbit and cross-orbit commutator lock simultaneously.
  rectangular-pauli-gauges-absorb-every-controlled-phase-network: that uses independent rectangular Pauli gauges for arbitrary phase data; this preserves the one-actor order-five covariance and the exact five-Clifford volume relation.
  extraspecial-fusion-filter-is-local-and-normalizer-globalization-is-matricial: that proves the normalizer globalization boundary; this shows that the finer actor-character compression in the cyclic proposal has positive leakage even when all proposed ordinary relators vanish.
---

**EXACT FINITE CYCLIC ABSORBER.**

Let

\[
 K=\langle J,X_1,\ldots,X_5\mid
 J^2=X_i^2=1,\ J\ {\rm central},\
 [X_i,X_j]_g=J\ (i\ne j),\
 X_1X_2X_3X_4X_5=J\rangle .                            \tag{FDS1}
\]

Let \(g\) have order five and cyclically permute the \(X_i\). Adjoin
involutions \(U,V\) whose conjugation actions on \(K\) agree with those of
\(X_1,X_2\), respectively. Put

\[
 U_i=g^iUg^{-i},\qquad V_i=g^iVg^{-i}
 \quad(0\leq i<5).                                      \tag{FDS2}
\]

Even after imposing **all** the rows

\[
 [U_i,U_j]_g=[V_i,V_j]_g=[U_i,V_j]_g=1
 \quad(0\leq i,j<5),                                    \tag{FDS3}
\]

the marked sector \(J=-1\) has an exact representation of dimension
sixteen.

Let \(\rho\) be the four-dimensional spin representation of \(K\), and let
\(h\) implement the order-five cycle. On
\({\mathbf C}^4\otimes{\mathbf C}^4\), set

\[
 \begin{aligned}
 \pi(k)&=\rho(k)\otimes I,\\
 \pi(g)&=h\otimes h,\\
 \pi(U)&=\rho(X_1)\otimes\rho(X_1),\\
 \pi(V)&=\rho(X_2)\otimes\rho(X_2).
 \end{aligned}                                          \tag{FDS4}
\]

Every relation in (FDS1)--(FDS3) holds and
\(\pi(J)=-I\). The two Clifford minus signs cancel in every off-diagonal
orbit commutator.

The odd-orbit words also fail to expose the hidden factor. With

\[
 E_U=J\prod_{i=0}^4U_i,\qquad
 E_V=J\prod_{i=0}^4V_i,                                 \tag{FDS5}
\]

one has

\[
 \pi(E_U)=\pi(E_V)=-I.                                  \tag{FDS6}
\]

Thus their commutator is trivial, while neither word recovers the first
hidden gauge \(\rho(X_1)\) or \(\rho(X_2)\).

Finally, every nonzero spectral cut \(q_\lambda\) of the second-factor
cycle \(h\) has strictly positive leakage for the corresponding gauge:

\[
 (1-q_\lambda)\rho(X_1)q_\lambda\ne0.                   \tag{FDS7}
\]

If a cut were reducing, the five conjugate Clifford reflections would all
agree on its range, contradicting their pairwise anticommutation. Hence the
finer character corner does not repair this model. All ordinary orbit rows
have zero defect while (FDS7) is positive, so no dimension-independent
inequality can bound that leakage using only those rows.

This closes the five-Clifford phase-orbit repair, including the version with
all shared pairwise commutator locks. A surviving Hecke decoder needs an
additional noncommutator return relation which directly charges the
off-character leakage. The existence of such a relation, and the
nonhyperlinear group, remain open.

DERIVATION
five-clifford-cyclic-phase-network-finite-model-proof
