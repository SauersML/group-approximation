---
rg: 2
id: word-section-fillings-obstruct-matrix-ulam-input
kind: claim
title: Word-section compilers retain moving filling loss before matrix Ulam stability
artifacts:
  - research/van-kampen-telescope-retains-moving-unit-ball-loss.md
distinct_from:
  matrix-ulam-stability-needs-full-unit-ball-control: that computes the exact compression leakage and gives a sharp M2 example separating marked tests from the unit ball; this quantifies the van Kampen loss of an arbitrary finite-quotient word-section compiler.
  induced-rounding-needs-rms-section-fillings: that analyzes the canonical induced section for the Iwahori packet; this gives the abstract relative filling criterion for every equivariant word section.
  multi-kraus-frame-energy-is-the-full-relative-pd-gate: that exactly metrizes the full positive-definite body by all Kraus frames; this treats the stricter unitary word-section subclass and does not assert a converse.
---

Let
\[
 \Gamma=\langle S\mid\mathcal R\rangle
\]
be finitely presented, let \(G\) be a finite quotient, let \(B<G\), and
suppose the marked unitaries \(U_s\) have relator defect
\[
 \max_{r\in\mathcal R}\|U_r-1\|_2\leq\delta.             \tag{WSF1}
\]
Relations belonging to an exactly represented core may be assigned cost
zero below. Choose a \(B\)-equivariant word section
\(\iota:G\to F(S)\), meaning that after choosing a left \(B\)-transversal,
\[
 U_{\iota(bg)}=\beta(b)U_{\iota(g)}.                    \tag{WSF2}
\]
For every marked Cayley edge define the defective filling area
\[
 A(s,g)=\operatorname{Area}_{\mathcal R}^{\rm def}
 \bigl(\iota(sg)^{-1}s\iota(g)\bigr),                   \tag{WSF3}
\]
where only relators whose evaluated defect is bounded by \(\delta\) are
counted.

Then the relative unitary zero-cochain
\[
 W_g=U_{\iota(g)}
\]
satisfies the exact finite-level estimate
\[
 \mathcal E_U(W)
 \leq\delta\left(\frac1{|S||G|}
       \sum_{s\in S,g\in G}A(s,g)^2\right)^{1/2}.        \tag{WSF4}
\]
Consequently, a sequence of equivariant sections with
\[
 \delta_n A_{{\rm rms},n}\longrightarrow0               \tag{WSF5}
\]
forces the unitary Cayley cosystole to vanish and hence, by the relative
positive-definite corner criterion, forces the full multi-Kraus distance
to vanish as well.

There is a stronger loss before one may invoke the dimension-free
matrix-algebra Ulam theorem. On the group basis, a word-section linear
compiler obeys
\[
 \|\Phi(\lambda_g)\Phi(\lambda_h)-\Phi(\lambda_{gh})\|_2
 \leq A(g,h)\delta.                                      \tag{WSF6}
\]
Even if one separately proves that its linear extension maps the
operator-norm unit ball to contractions, the elementary coefficient
estimate gives
\[
 \sup_{\|x\|,\|y\|\leq1}
 \|\Phi(x)\Phi(y)-\Phi(xy)\|_2
 \leq |G|A_{\max}\delta.                                 \tag{WSF7}
\]
Thus Alekseev--Thom can be applied under the additional rate in (WSF7), or
after a new dimension-free cancellation/completely-positive construction.
It does not remove the moving filling constant.

For the concrete Iwahori quotients, neither a uniform bound on
\(A_{\rm rms}\) nor a cancellation theorem replacing it is known. Since
the defect may tend to zero arbitrarily slowly relative to the moving
level, (WSF4) alone does not prove capture. It is a rigorous sufficient
finite-quotient criterion and an exact firewall around the naive
presentation-to-unit-ball upgrade. The root remains open.

DERIVATION
van-kampen-telescope-retains-moving-unit-ball-loss
