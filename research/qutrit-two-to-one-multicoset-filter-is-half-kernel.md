---
rg: 2
id: qutrit-two-to-one-multicoset-filter-is-half-kernel
kind: claim
title: Every typed two-to-one qutrit word filter has a half-source kernel
artifacts:
  - research/qutrit-multicoset-capacity-proof.md
distinct_from:
  qutrit-central-line-twist-is-impossible-in-jacobson-host: that rules out a Hall-deficient graph for one group word; this allows arbitrary finite linear combinations and identifies their unavoidable singular-value loss.
  qutrit-two-to-one-phase-graph-requires-central-line-twist: that classifies character intersections of a single double coset; this constructs the desired graph by Fourier filtering and proves that its polar cannot cover the two-phase source.
  qutrit-jacobson-residual-has-fixed-polar-gap: that gives a Hilbert-Schmidt gap once a full polar identifies unequal carriers; this proves that an exactly phase-typed filter can never have that full polar.
---

Let
\[
 C=\langle J,Z_1\rangle,\qquad
 q=e_0+e_1+e_2,\qquad R=e_0+e_1,\qquad q-R=e_2.
\]
Choose the generic active qutrit labeling, so the raw root
\(t=x_{23}(T)\) has complete \(C\)-phase graph.  Then
\[
 A=e_2tR                                                     \tag{QMC1}
\]
is an explicit finite linear combination of host words with the exact
Hall-deficient support table
\[
 e_bAe_a\ne0
 \quad\Longleftrightarrow\quad
 b=2\ \hbox{and}\ a\in\{0,1\}.                            \tag{QMC2}
\]
The two nonzero blocks satisfy
\[
 \|e_2te_0\|_2^2=\|e_2te_1\|_2^2={1\over81}.             \tag{QMC3}
\]
Thus a multi-word Fourier filter can manufacture the desired \(2\)-to-\(1\)
phase graph exactly.  This is not yet a router.

In every finite-dimensional representation of the order-\(3^5\) qutrit
packet, the central-\(\omega\) block is a sum of copies of its unique
nine-dimensional spin representation.  On each copy,
\[
 \dim e_0=\dim e_1=\dim e_2=3,\qquad \dim R=6.
\]
Consequently every operator \(B\), no matter how many host words occur in
it, which is exactly phase typed by
\[
 B=e_2BR                                                   \tag{QMC4}
\]
has
\[
 \operatorname{rank}B\leq\dim e_2={1\over2}\dim R.
\]
At least half of the \(R\)-source singular values are zero.  Equivalently,
if \(v=\operatorname{polar}(B)\), then in the canonical trace
\[
 v^*v\leq R,\qquad vv^*\leq e_2,\qquad
 \tau(v^*v)\leq{1\over9},\qquad
 \tau(R-v^*v)\geq{1\over9}.                              \tag{QMC5}
\]
In particular \(v^*v\ne R\), and
\[
 \|R-v^*v\|_2\geq{1\over3}.                              \tag{QMC6}
\]

The conclusion is independent of whether \(B\) is a short Fourier filter,
a sum across many \(C\)-double cosets, or a polar input built from Jacobson
words.  Inserting the residual between the phase cuts does not help if the
typing is retained: every expression of the form
\[
 B=e_2\,X\,R\,e_{\rm res}\,R
\]
still satisfies (QMC4) and the half-kernel theorem.  An expression ending
instead in \(R e_{\rm res}\), with no final \(R\), may have source support
outside \(R\), but then it is not a map from the two \(C\)-character atoms;
the claimed Hall typing has been lost.

Therefore exact coefficients can create the graph, but exact phase typing
forces branch deletion rather than a full-source polar.  A successful
analytic obstruction must prove a separate raw occurrence identity which
both restores the \(R\)-typing and, contrary to (QMC5), forces full source.
The finite Fourier filter or any unconstrained multi-coset sum alone cannot
do so.
