---
rg: 2
id: van-kampen-telescope-retains-moving-unit-ball-loss
kind: route
title: Telescope defective relator fillings through unitary tables and the group basis
target: word-section-fillings-obstruct-matrix-ulam-input
requires:
  - relative-table-separator-is-cayley-cocycle-obstruction
  - matrix-ulam-stability-needs-full-unit-ball-control
---

# Relator area controls one evaluated null word

Let \(U_w\) denote evaluation of a word \(w\in F(S)\). Suppose a null word
has a van Kampen expression
\[
 w=\prod_{j=1}^{A}q_jr_j^{\epsilon_j}q_j^{-1},
 \qquad r_j\in\mathcal R,\quad\epsilon_j\in\{-1,1\}.     \tag{1}
\]
Normalized Hilbert--Schmidt distance on unitaries is bi-invariant.
Telescoping the product in (1), conjugation invariance, and (WSF1) give
\[
 \|U_w-1\|_2\leq
 \sum_{j=1}^{A}\|U_{r_j}^{\epsilon_j}-1\|_2
 \leq A\delta.                                           \tag{2}
\]
If some core relators evaluate exactly, their summands in (2) are zero.
Minimizing the number of the remaining relators proves the same estimate
with the defective area in (WSF3).

# An equivariant section gives the RMS Cayley filling bound

Choose one representative of each left \(B\)-coset and extend its word
section by left multiplication with fixed core words. This gives (WSF2).
Put
\[
 W_g=U_{\iota(g)}.                                       \tag{3}
\]
Then \(W_{bg}=\beta(b)W_g\), so \(W\) is a relative unitary zero-cochain.
The null word
\[
 \iota(sg)^{-1}s\iota(g)                                 \tag{4}
\]
and (2) give
\[
 \begin{aligned}
 \|U_sW_g-W_{sg}\|_2
 &=\|U_{\iota(sg)}^*U_sU_{\iota(g)}-1\|_2\\
 &\leq A(s,g)\delta.                                     \tag{5}
 \end{aligned}
\]
Squaring (5), averaging over \(S\times G\), and taking square roots proves
(WSF4).

The flat frame associated with \(W\) is a member of the complete
multi-Kraus class. Hence its coefficient-body distance is at most
\(\mathcal E_U(W)\). This proves the sufficient implication (WSF5). It is
one-way: an arbitrary low-energy rectangular Kraus frame need not arise
from any unitary word section.

# Extending from group elements to the operator-norm unit ball

For a finite quotient \(G\), define on its group basis
\[
 \Phi(\lambda_g)=U_{\iota(g)}.                           \tag{6}
\]
The loop
\(\iota(gh)^{-1}\iota(g)\iota(h)\) and (2) prove (WSF6).
Suppose additionally that the linear extension of (6) takes the
operator-norm unit ball to contractions. This contractivity is not a
consequence of the relator bounds and is part of the missing compiler.

For
\[
 x=\sum_ga_g\lambda_g,\qquad y=\sum_hb_h\lambda_h,
\]
linearity and (WSF6) yield
\[
 \|\Phi(x)\Phi(y)-\Phi(xy)\|_2
 \leq A_{\max}\delta
       \left(\sum_g|a_g|\right)\left(\sum_h|b_h|\right). \tag{7}
\]
Under the canonical trace,
\[
 \sum_g|a_g|^2=\|x\|_2^2\leq\|x\|^2\leq1,
\]
and similarly for \(y\). Cauchy--Schwarz bounds each first norm by
\(|G|^{1/2}\), proving (WSF7).

The factor \(|G|A_{\max}\) is not claimed optimal. It records exactly what
the formal word telescope provides. Removing it would require new
operator-space cancellation, positivity, or a nonlinear synchronization
estimate. The matrix Ulam theorem consumes such a uniform estimate after
it is available; it does not improve (7) from presentation data.
