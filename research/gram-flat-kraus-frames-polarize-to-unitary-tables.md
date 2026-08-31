---
rg: 2
id: gram-flat-kraus-frames-polarize-to-unitary-tables
kind: claim
title: Gram-flat Kraus frames polarize equivariantly to relative unitary tables
artifacts:
  - research/equivariant-polar-rounding-pays-gram-flatness.md
distinct_from:
  multi-kraus-frame-energy-is-the-full-relative-pd-gate: that allows arbitrary rectangular Stinespring frames and exactly metrizes the full coefficient body; this gives a sufficient flattening theorem for square pointwise Gram-flat frames.
  almost-full-hecke-frame-gives-flexible-corner: that fills missing trace coverage directly inside a Kraus corner; this rounds each fibre to a unitary and quantifies the additional Gram-flatness price.
  right-core-cayley-average-gives-toeplitz-window: that starts from an already unitary right-core gauge; this proves when a square nonunitary frame can be converted into such a gauge.
---

Let \(A=(A_g)_{g\in G}\) be a square relative Stinespring frame,
\(A_g\in M_d(\mathbb C)\), satisfying (MKF2). Put
\[
 B_g=|G|^{1/2}A_g,\qquad
 \eta_{\rm gr}(A)=\frac1{|G|}\sum_{g\in G}
 \operatorname{tr}_d|B_g^*B_g-1|.                      \tag{GFP1}
\]
There is a relative unitary zero-cochain
\[
 W:G\to U(d),\qquad W_{bg}=\beta(b)W_g,                 \tag{GFP2}
\]
such that
\[
 \mathcal E_U(W)
 \leq\mathcal E_U^{\rm K}(A)+2\sqrt{\eta_{\rm gr}(A)}.  \tag{GFP3}
\]
Thus any sequence of square frames with both Kraus energy and average
pointwise Gram defect tending to zero has vanishing unitary Cayley
cosystole. This is a dimension-free equivariant polar synchronization
criterion.

The Gram hypothesis is a real extra input. Let
\(\pi:G\to U(d)\) be any irreducible representation with \(d>1\), let
\(v\) be a unit vector, take trivial core, and define the rectangular
rank-one Fourier frame
\[
 A_g\xi=\sqrt{\frac d{|G|}}\,
        \langle\pi(g)v,\xi\rangle
 \quad(A_g:\mathbb C^d\to\mathbb C).                    \tag{GFP4}
\]
Then
\[
 \sum_gA_g^*A_g=1,\qquad
 F_A(k)=\sum_gA_{kg}^*A_g=\pi(k),                        \tag{GFP5}
\]
and, for \(U_s=\pi(s)\),
\[
 A_{sg}U_s=A_g,\qquad\mathcal E_U^{\rm K}(A)=0.          \tag{GFP6}
\]
After embedding its one-dimensional target into \(\mathbb C^d\), every
\(B_g^*B_g\) has rank one and
\[
 \operatorname{tr}_d|B_g^*B_g-1|=2\left(1-\frac1d\right). \tag{GFP7}
\]
Hence a zero-energy Stinespring minimizer can be maximally nonflat.

This does not produce a unitary-table counterexample: the exact
representation \(\pi\) also has the flat zero-energy table
\(W_g=\pi(g)\). It proves that polarizing an arbitrary low-energy Kraus
minimizer, or alternating between energy minimization and fibrewise polar
rounding without controlling which minimizer is selected, cannot be a
general proof. The missing theorem would have to select a Gram-flat frame,
not infer flatness from multi-Kraus energy alone. No such selection theorem
is proved for the two Iwahori cubics, so the root remains open.

DERIVATION
equivariant-polar-rounding-pays-gram-flatness
