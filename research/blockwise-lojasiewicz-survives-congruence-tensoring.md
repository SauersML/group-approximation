---
rg: 2
id: blockwise-lojasiewicz-survives-congruence-tensoring
kind: route
title: Repair bounded payloads blockwise and sum them by Hilbert--Schmidt concavity
target: bounded-payload-congruence-tensors-have-uniform-capture
requires:
  - bounded-dimension-iwahori-pairs-have-holder-capture
  - finite-dimensional-dual-of-sl2-z-inverse-two-is-odd-congruence
---

# Blockwise fixed-size repair survives arbitrary congruence tensors

Choose the exponent in
**bounded-dimension-iwahori-pairs-have-holder-capture** no larger than one,
decreasing it and enlarging the constant on the compact defect interval if
necessary. Thus every payload pair of dimension at most \(D\) has a
same-dimensional compatible correction \(\widetilde\kappa_j\) with
\[
 d_2(\kappa_j,\widetilde\kappa_j)
 \leq C_D e_j^{\alpha_D},\qquad 0<\alpha_D\leq1,          \tag{1}
\]
where \(e_j=\operatorname{def}(\kappa_j)\).

On the Iwahori edge the two restrictions of \(\eta_j\) agree exactly.
Therefore, for every edge generator \(b\),
\[
 \begin{aligned}
 &\|\kappa_{j,+}(b)\otimes\eta_j(b)
  -\kappa_{j,-}(\sigma b)\otimes\eta_j(b)\|_2\\
 &\qquad =
 \|\kappa_{j,+}(b)-\kappa_{j,-}(\sigma b)\|_2.           \tag{2}
 \end{aligned}
\]
Tensoring the correction in (1) with \(\eta_j\) likewise preserves its
normalized Hilbert--Schmidt cost. Moreover
\[
 \widetilde\kappa_j\otimes\eta_j
\]
is an exact representation of \(A\), so its two vertex restrictions form a
compatible endpoint.

Let
\[
 w_j={k_jm_j\over d}
\]
be the physical dimension weight of a block in the whole direct sum. If
\(S_B\) is the fixed edge generating set, Pythagoras and (2) give
\[
 \sum_jw_je_j^2
 \leq\sum_{b\in S_B}\sum_jw_j
  \|\kappa_{j,+}(b)-\kappa_{j,-}(\sigma b)\|_2^2
 \leq |S_B|\operatorname{def}(\pi)^2.                   \tag{3}
\]
The direct sum of the corrected tensor blocks is one exact compatible
endpoint. Its squared distance from \(\pi\) is at most
\[
 C_D^2\sum_jw_je_j^{2\alpha_D}.
\]
Since \(x\mapsto x^{\alpha_D}\) is concave and \(\sum_jw_j=1\), Jensen's
inequality and (3) give
\[
 \sum_jw_je_j^{2\alpha_D}
 \leq\left(\sum_jw_je_j^2\right)^{\alpha_D}
 \leq |S_B|^{\alpha_D}
       \operatorname{def}(\pi)^{2\alpha_D}.              \tag{4}
\]
Absorb the fixed factor in the constant to obtain (BPT2). A common global
unitary gauge cancels from every norm and is retained on the corrected
direct sum.

For (BPT3), apply the same calculation only on the common reducing carrier.
The weights of its blocks need not sum to one; adjoining a zero weight makes
the same concavity estimate valid, and its contribution is still bounded by
the full defect through (3). On the complementary rank-\(r\) carrier replace
both vertices by the trivial compatible representation. Any two unitary
generator matrices are at normalized Hilbert--Schmidt distance at most two,
so this replacement costs at most \(2\sqrt r\) in the whole dimension.
The triangle inequality proves (BPT3).

If the limiting distance is at least \(\varepsilon\) while the defect tends
to zero, (BPT3) forces
\[
 2\sqrt{\liminf r_n}\geq\varepsilon,
\]
which is the asserted \(\varepsilon^2/4\) escape rank.
