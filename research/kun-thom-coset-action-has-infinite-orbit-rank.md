---
rg: 2
id: kun-thom-coset-action-has-infinite-orbit-rank
kind: claim
title: The Kun--Thom coset action has infinitely many ordered-pair orbits
distinct_from:
  marked-double-coset-infinite-degree: that proves one marked orbital has infinite valency by an intersection-index computation; this proves that there are already infinitely many distinct orbitals, using the linear-part quotient.
  coordinate-action-not-sofic: that is the deep failure of finite orbit charts; this is an elementary exact double-coset count and does not use nonsoficity.
  kazhdan-stabilizer-collapses-shared-pauli-sign: that requires finitely many double cosets; this proves its finite-rank hypothesis fails for the original Kun--Thom action.
---

Let
\[
 R_+=\mathbb F_q[x_1,\ldots,x_d],\qquad
 R=\mathbb F_q[x_1^{\pm1},\ldots,x_d^{\pm1}],
\]
\[
 \Gamma=\operatorname{EL}_r(R_+),\qquad
 G=\operatorname{EL}_r(R)\rtimes\operatorname{SL}_d(\mathbb Z),
\]
with the Kun--Thom action on \(X=G/\Gamma\).  Then
\[
 \bigl|\Gamma\backslash G/\Gamma\bigr|=\infty.             \tag{KTR1}
\]

Indeed the semidirect-product projection
\[
 \pi:G\longrightarrow\operatorname{SL}_d(\mathbb Z)
\]
kills \(\Gamma\).  Hence
\[
 \Gamma g\Gamma\longmapsto\pi(g)                          \tag{KTR2}
\]
is a well-defined map from the double-coset space to
\(\operatorname{SL}_d(\mathbb Z)\).  It is surjective, because
\(a\in\operatorname{SL}_d(\mathbb Z)\) is the image of \((1,a)\in G\).
Since \(\operatorname{SL}_d(\mathbb Z)\) is infinite, (KTR1) follows.

Equivalently, the diagonal \(G\)-action on \(X\times X\) has infinitely many
orbits.  This is stronger in one direction and weaker in another than the
known marked-orbital calculation: it counts infinitely many orbitals, while
that calculation proves that one particular orbital has infinite degree.

Two programme consequences are immediate.

1. The finite-rank exact-actor Pauli collapse theorem and its
padding-stable correction estimate do not apply to this original
Kun--Thom \(G\)-set: there is no finite list of double-coset prototype rows.
2. The shared-center Pauli semidirect product over this \(X\) is not finitely
presented, by the necessary finite-double-coset condition in
the shared-center Pauli finite-presentation criterion.

Thus the finite-rank Kazhdan-stabilizer Pauli route is a genuinely different
host search.  Gao--Kunnawalkam Elayavalli--Patchell's sofic-action machinery
does not bridge the difference: its generalized-wreath theorem is forward
from a sofic action, while this Kun--Thom action is nonsofic and has infinite
orbit rank.
