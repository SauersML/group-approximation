---
rg: 2
id: qutrit-central-line-rank-obstruction-proof
kind: proof
title: Separate central and leaf qutrit lines by the retracted fixed-space rank
target: qutrit-central-line-twist-is-impossible-in-jacobson-host
requires:
  - qutrit-two-to-one-phase-graph-requires-central-line-twist
  - thompson-27-cylinder-qutrit-cell-is-fd-invisible
  - one-balanced-actor-qutrit-bridge-is-jacobson-core
---

# Separate central and leaf qutrit lines by the retracted fixed-space rank

## 1. The coefficient retraction preserves a proposed conjugacy

The Jacobson algebra has the unital retraction
\[
 \epsilon:J=\mathbb F_2\langle S,T\mid TS=1\rangle
 \longrightarrow\mathbb F_2,\qquad \epsilon(S)=\epsilon(T)=1.
\]
Applying it entrywise gives a group homomorphism
\[
 \epsilon_*:GL_{28}(J)\longrightarrow GL_{28}(\mathbb F_2).
                                                               \tag{QRI3}
\]
In particular, if \(gPg^{-1}=Q\) for two constant scalar matrices \(P,Q\),
then
\[
 \epsilon_*(g)P\epsilon_*(g)^{-1}=Q.                    \tag{QRI4}
\]
Thus the \(\mathbb F_2\)-linear rank of \(P-I\) is a conjugacy invariant
even when the proposed conjugator originally has nonconstant Jacobson
coefficients.

## 2. Fixed spaces of the two line types

Use the affine qutrit leaf labeling
\[
 \Omega=\mathbb F_3^2\times\mathbb F_3
\]
and the extra scalar coordinate fixed by the entire qutrit packet.  On a
leaf \((u_1,u_2,s)\),
\[
 J^rZ_1^q(u_1,u_2,s)
 =(u_1,u_2,s+r-qu_1).                                   \tag{QRI5}
\]

First take \(q=0\) and \(r\ne0\).  For each of the nine pairs
\((u_1,u_2)\), equation (QRI5) is a three-cycle on the \(s\)-coordinate.
There are therefore nine disjoint three-cycles and one fixed extra
coordinate.  On the permutation module over \(\mathbb F_2\), a three-cycle
has a one-dimensional fixed space and its permutation matrix minus the
identity has rank two.  Hence
\[
 \operatorname{rank}_{\mathbb F_2}(J^r-I)=9\cdot2=18.   \tag{QRI6}
\]

Now take \(q\ne0\).  There is exactly one value
\[
 u_1=rq^{-1}
\]
for which the last coordinate in (QRI5) is unchanged.  This gives nine
fixed leaves: three choices of \(u_2\) and three choices of \(s\).
For each of the other two values of \(u_1\), the three choices of \(u_2\)
give one three-cycle each.  Thus there are six disjoint three-cycles,
nine fixed leaves, and the fixed extra coordinate.  Consequently
\[
 \operatorname{rank}_{\mathbb F_2}(J^rZ_1^q-I)=6\cdot2=12.
                                                               \tag{QRI7}
\]
The other nonidentity generator of the same order-three line has the same
cycle decomposition and the same rank.

Equations (QRI6) and (QRI7), together with (QRI4), prove that no
\(g\in GL_{28}(J)\) conjugates the central line \(\langle J\rangle\) to a
noncentral line \(\langle J^rZ_1^q\rangle\), \(q\ne0\).

## 3. Elimination of every single-word Hall router

Let \(g\in GL_{28}(J)\), and set
\[
 H=C\cap gCg^{-1},\qquad H'=g^{-1}Hg.
\]
Conjugation by \(g\) is an isomorphism from \(H'\) onto \(H\).  If one were
\(\langle J\rangle\) and the other a noncentral line, a nonidentity
generator of one would be conjugate to a nonidentity generator of the
other.  Section 2 rules this out.

The character-block theorem for
\[
 e_a=z_{C,\chi_a},\qquad
 \chi_a(J)=\omega,\quad\chi_a(Z_1)=\omega^a
\]
classifies the support of \(e_bge_a\).  A two-to-one star on the selected
source phases can occur only when exactly one of \(H,H'\) is the central
line and the other is noncentral.  Since this pair is impossible, no
\(g\in GL_{28}(J)\) has that phase graph.

The conclusion applies a fortiori to every evaluated word in
\(EL_{28}(J)\), regardless of its length, its \(S/T\) depth, or the number
of constant Weyl conjugations used to write it.  An abstract extension by
a cyclic automorphism interchanging the two line types cannot map into this
host while preserving the displayed qutrit packet: its claimed conjugacy
would violate (QRI6)--(QRI7).  This proves the claim.
