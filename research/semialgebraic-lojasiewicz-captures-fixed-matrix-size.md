---
rg: 2
id: semialgebraic-lojasiewicz-captures-fixed-matrix-size
kind: route
title: Apply the global Łojasiewicz inequality to the fixed-size representation variety
target: bounded-dimension-iwahori-pairs-have-holder-capture
requires:
  - finite-dimensional-dual-of-sl2-z-inverse-two-is-odd-congruence
  - iwahori-local-global-defect-question
---

# Apply the global Łojasiewicz inequality at fixed matrix size

Fix \(d\). Let \(V_+\) and \(V_-\) be the two modular vertex groups and
choose the fixed finite vertex and Iwahori generating sets used in the
Dogon--Vigdorovich metric. Put
\[
 \mathcal R_d=
 \operatorname{Hom}(V_+,U(d))\times
 \operatorname{Hom}(V_-,U(d)).                            \tag{1}
\]
After writing matrices in real and imaginary coordinates, \(U(d)\) is a
compact real algebraic set. Each modular vertex is finitely presented, so
(1) is a compact real algebraic subset of a finite-dimensional Euclidean
space.

For \(\pi\in\mathcal R_d\), define the squared edge mismatch
\[
 E_d(\pi)=
 \sum_{b\in S_B}
 \|\pi_+(b)-\pi_-(\sigma b)\|_{2,d}^{\,2},                \tag{2}
\]
where \(\|\cdot\|_{2,d}\) is normalized Hilbert--Schmidt norm. Matrix words
and their adjoints are polynomial in real coordinates, so \(E_d\) is a
nonnegative polynomial function on \(\mathcal R_d\). Its zero set is
\[
 \mathcal Z_d=E_d^{-1}(0).                                \tag{3}
\]

Exact equality on the chosen generators of the Iwahori edge is equality on
the whole edge group. By the universal property of the amalgam,
\(\mathcal Z_d\) is exactly the set of restrictions to the two vertices of
representations
\[
 \operatorname{SL}_2(\mathbb Z[1/2])\longrightarrow U(d). \tag{4}
\]
Thus it is the same-dimensional compatible locus, not a larger algebraic
relaxation.

Let \(\delta_d(\pi)\) be Euclidean distance from \(\pi\) to \(\mathcal Z_d\),
measured on the fixed vertex-generator matrices. The distance to a compact
semialgebraic set is semialgebraic. The global semialgebraic Łojasiewicz
inequality on the compact set \(\mathcal R_d\), applied to \(E_d\) and its
zero set, supplies \(C_d<\infty\) and \(\beta_d>0\) such that
\[
 \delta_d(\pi)\leq C_d E_d(\pi)^{\beta_d}
 \qquad(\pi\in\mathcal R_d).                              \tag{5}
\]
All norms on the fixed finite coordinate space are equivalent, while
\[
 E_d(\pi)^{1/2}
 \leq |S_B|^{1/2}\operatorname{def}(\pi).
\]
After changing \(C_d\) and putting \(\alpha_d=2\beta_d\), (5) gives a
compatible \(\widetilde\pi\in\mathcal Z_d\) with
\[
 d_2(\pi,\widetilde\pi)
 \leq C_d\operatorname{def}(\pi)^{\alpha_d}.              \tag{6}
\]
The generalized Dogon--Vigdorovich distance is no larger than the
same-dimensional comparison in (6).

By **finite-dimensional-dual-of-sl2-z-inverse-two-is-odd-congruence**, the
representation (4) has finite image and factors through an odd congruence
quotient. Hence (6) is congruence capture, not merely compatibility with an
unclassified finite-dimensional endpoint.

For \(1\leq d\leq d_0\), decrease the finitely many exponents to one common
positive exponent and enlarge the finitely many constants. Since the defect
is bounded on the compact varieties, this gives one pair
\((C_{d_0},\alpha_{d_0})\) and proves (BDH1).

The proof cannot pass to \(d=\infty\): the Euclidean dimension of
\(\mathcal R_d\), the global Łojasiewicz exponent, and the norm-comparison
constants are all allowed to deteriorate with \(d\). That deterioration is
exactly where the regular ultraproduct face and global noncongruence capture
remain.
