---
rg: 2
id: qutrit-central-line-twist-is-impossible-in-jacobson-host
kind: claim
title: The qutrit central-line twist is impossible in the Jacobson host
artifacts:
  - research/qutrit-central-line-rank-obstruction-proof.md
distinct_from:
  qutrit-two-to-one-phase-graph-requires-central-line-twist: that proves an asymmetric central/noncentral intersection is the only group-word mechanism for a two-to-one phase graph; this rules out that mechanism for every word in the full Jacobson host.
  qutrit-first-stk-word-central-line-proof: that audits a bounded S/T/opposite-root closure by active-support calculations; this uses a conjugacy invariant and has no word-length bound.
  one-balanced-actor-qutrit-bridge-is-jacobson-core: that identifies the ambient group and its scalar retraction; this uses the retraction to separate the two order-three line types.
---

Let
\[
 C=\langle J,Z_1\rangle\cong C_3^2
\]
be the qutrit phase subgroup in the scalar copy of
\(GL_{28}(\mathbb F_2)\leq GL_{28}(J)\).  There are two kinds of
order-three lines in \(C\):
\[
 L_{\rm cen}=\langle J\rangle,\qquad
 L_{r,q}=\langle J^rZ_1^q\rangle\quad(q\ne0).
\]
No element of \(GL_{28}(J)\), and hence no word in \(EL_{28}(J)\), conjugates
\(L_{\rm cen}\) to any \(L_{r,q}\).

Indeed, under the coefficient retraction
\[
 \epsilon:J\longrightarrow\mathbb F_2,\qquad S,T\longmapsto1,
\]
a nonidentity element of \(L_{\rm cen}\) satisfies
\[
 \operatorname{rank}_{\mathbb F_2}(J-I)=18,
\]
whereas a nonidentity element of every noncentral line satisfies
\[
 \operatorname{rank}_{\mathbb F_2}(J^rZ_1^q-I)=12.       \tag{QRI1}
\]
These ranks are invariant under conjugacy by the invertible matrix
\(\epsilon(g)\).

Consequently, for every \(g\in GL_{28}(J)\), if
\[
 H=C\cap gCg^{-1},\qquad H'=g^{-1}Hg,
\]
then \(H\) and \(H'\) cannot be respectively a central and a noncentral
line.  The established qutrit character-intersection criterion says that
this asymmetric pair is the only way a single group element can send the
two selected phases of \(R=e_0+e_1\) through only the one complement phase
\(e_2=q-R\).  Therefore:

\[
 \boxed{\text{No single Jacobson-host group word has the required
 two-to-one qutrit phase graph.}}                       \tag{QRI2}
\]

This also rules out adjoining an abstract cyclic router which sends
\(J\) to a leaf-stabilizer generator while claiming that it is realized by
the given 28-dimensional host representation.  Such an abstract automorphism
does not extend to this scalar qutrit module.

The remaining Hall route must be genuinely analytic: a compression, sum,
or polar involving more than one group-word double coset must delete a
branch.  Searching for a longer host word that conjugates the two line
types cannot succeed.
