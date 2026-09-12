---
rg: 2
id: bounded-payload-congruence-tensors-have-uniform-capture
kind: claim
title: Bounded payloads tensored with congruence endpoints have uniform global capture
artifacts:
  - research/blockwise-lojasiewicz-survives-congruence-tensoring.md
distinct_from:
  bounded-dimension-iwahori-pairs-have-holder-capture: that fixes the whole ambient matrix dimension; this permits unbounded ambient dimension, multiplicity, and congruence tensor factors while bounding only the payload blocks.
  pauli-tensor-charts-are-globally-congruence-captured: that closes one explicit two-dimensional Pauli chart near its mod-two base; this closes every bounded-dimensional payload chart, with no finite-image or proximity assumption on the payload.
  residual-finite-tensor-camouflages-iwahori-transfer-failures: that shows regular congruence tensors preserve an abstract obstruction; this proves they cannot turn a bounded-dimensional near-compatible payload into a global-capture obstruction.
---

Fix \(D<\infty\). For each \(j\), let
\[
 \kappa_{j,\pm}:V_\pm\longrightarrow U(k_j),
 \qquad k_j\leq D,
\]
be an arbitrary exact modular-vertex pair, and let
\[
 \eta_j:A=\operatorname{PSL}_2(\mathbb Z[1/2])
       \longrightarrow U(m_j)
\]
be an exact finite-dimensional congruence endpoint. Form the paired block
\[
 \pi_{j,\pm}=\kappa_{j,\pm}\otimes\eta_j|_{V_\pm},       \tag{BPT1}
\]
using the exact common Iwahori identification of \(\eta_j\). Allow arbitrary
multiplicities, orthogonal direct sums of these paired blocks, and one common
unitary conjugation of the whole pair.

There are constants \(C_D<\infty\) and \(\alpha_D>0\), independent of all
\(m_j\), congruence levels, multiplicities, numbers of blocks, and ambient
dimensions, such that every pair \(\pi\) in this tensor hull satisfies
\[
 D(\pi)\leq C_D\operatorname{def}(\pi)^{\alpha_D}.        \tag{BPT2}
\]
The correcting endpoint can be chosen in the same total dimension.

There is a quantitative partial-hull version. Suppose an exact vertex pair
has a common reducing carrier of relative rank \(1-r\) on which it belongs
to the tensor hull above; make no assumption on the complementary carrier.
Then
\[
 D(\pi)\leq
 C_D\operatorname{def}(\pi)^{\alpha_D}+2\sqrt r.          \tag{BPT3}
\]
Consequently, if
\[
 \operatorname{def}(\pi_n)\to0,\qquad
 \liminf_n D(\pi_n)\geq\varepsilon>0,
\]
then for every fixed \(D\), at least asymptotic physical rank
\(\varepsilon^2/4\) lies outside every common bounded-payload congruence
tensor decomposition.

This applies in particular when the \(\eta_j\) are deep regular congruence
representations, so that tensor camouflage makes all fixed-word characters
regular. Hence a positive-RMS-distance regular enemy cannot be a hidden
mixture of bounded-dimensional payloads behind regular congruence factors.
Its payload complexity must itself escape every fixed dimension on positive
physical rank.

The theorem assumes an authenticated common tensor-block decomposition. It
does not extract such blocks from an arbitrary regular microstate, and it
does not control an indecomposable unbounded payload. Those are the surviving
global-capture possibilities; the root remains open.

DERIVATION
blockwise-lojasiewicz-survives-congruence-tensoring
