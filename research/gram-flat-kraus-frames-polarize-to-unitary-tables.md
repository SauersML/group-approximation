---
rg: 2
id: gram-flat-kraus-frames-polarize-to-unitary-tables
kind: claim
title: Gram-flat square Kraus frames polarize to relative unitary tables
artifacts:
  - research/equivariant-polar-rounding-pays-gram-flatness.md
distinct_from:
  multi-kraus-frame-energy-is-the-full-relative-pd-gate: that allows arbitrary rectangular Stinespring frames and exactly metrizes the full coefficient body; this gives a sufficient original-dimension flattening theorem for square pointwise Gram-flat frames.
  right-translation-flattens-every-relative-kraus-frame: that makes every frame pointwise isometric after a possibly large target amplification; this rounds square fibres to unitaries and therefore addresses the additional common-corange or target-dimension gate.
  almost-full-hecke-frame-gives-flexible-corner: that fills missing trace coverage directly inside a Kraus corner; this rounds each square fibre to a unitary and quantifies the Gram-flatness price.
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
Thus square frames whose Kraus energy and average pointwise Gram defect
both vanish have vanishing unitary Cayley cosystole.

For polar rounding on the original square carrier, the Gram hypothesis is
a real extra input. Let \(\pi:G\to U(d)\) be irreducible with \(d>1\), let
\(v\) be a unit vector, take trivial core, and define the rank-one Fourier
frame
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
After embedding the one-dimensional target into \(\mathbb C^d\),
\[
 \operatorname{tr}_d|B_g^*B_g-1|
 =2\left(1-\frac1d\right).                              \tag{GFP7}
\]
Thus a zero-energy minimizer need not be square-flat.

This is not a unitary-table counterexample: the exact representation
\(\pi\) also has the flat zero-energy table \(W_g=\pi(g)\).
Right-translation-flattens-every-relative-kraus-frame further shows that
arbitrary column-Gram nonflatness can always be removed in a taller target
without changing the table or energy. What remains for a unitary-table
proof is to align those tall isometries' coranges with one common
\(d\)-plane, or to select a square Gram-flat frame. Energy minimization
followed by square fibrewise polar rounding does not supply that operation.
No such corange-reduction theorem is proved from the two Iwahori cubics,
so the root remains open.

DERIVATION
equivariant-polar-rounding-pays-gram-flatness
