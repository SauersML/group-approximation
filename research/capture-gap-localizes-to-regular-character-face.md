---
rg: 2
id: capture-gap-localizes-to-regular-character-face
kind: claim
title: Every congruence-capture gap localizes quantitatively to the regular character face
artifacts:
  - research/central-cut-quantifies-the-regular-capture-obstruction.md
distinct_from:
  bs14-character-split-leaves-only-the-regular-microstate-face: that identifies the finite and regular central summands; this proves that a positive metric gap survives on an exact-vertex regular corner and quantifies the minimum rank of that corner.
  regular-iwahori-exactification-is-regular-branch-liftability: that identifies correction of every regular microstate with the full remaining theorem; this shows every failure of global congruence capture produces such a regular failure.
  dv-distance-is-defect-plus-congruence-capture: that reduces the published distance to congruence-capture distance; this reduces a positive congruence-capture gap to one central character face.
---

**ESTABLISHED REDUCTION; THE REGULAR FACE REMAINS OPEN.**

Use the center-free packet
\[
 A=\operatorname{PSL}_2(\mathbb Z[1/2])
   =V_+*_{B}V_-
\]
and the congruence-capture distance \(A_{\mathrm{cong}}\). Suppose exact
vertex pairs \(\pi_n=(\pi_{n,+},\pi_{n,-})\), of dimensions \(d_n\), satisfy
\[
 \operatorname{def}(\pi_n)\longrightarrow0,\qquad
 \liminf_n A_{\mathrm{cong}}(\pi_n)\geq\varepsilon>0.       \tag{RCL1}
\]
Then, after a subsequence, there are integers \(e_n\), numbers
\(e_n/d_n\to r\), and exact vertex pairs
\(\kappa_n:V_+*V_-\to U(e_n)\) such that

1. the edge defect of \(\kappa_n\) tends to zero;
2. its induced ultraproduct representation of \(A\) has normalized character
   exactly the regular character \(\delta_e\);
3. its congruence-capture gap survives:
   \[
    \liminf_n A_{\mathrm{cong}}(\kappa_n)
       \geq \varepsilon/\sqrt r\geq\varepsilon;            \tag{RCL2}
   \]
4. the regular-corner weight is quantitatively nonzero:
   \[
    r\geq \varepsilon^2/4.                                 \tag{RCL3}
   \]

The complementary corners are flexibly \(o(1)\)-close to genuine
finite-dimensional representations of \(A\), hence to odd-congruence
endpoints. Therefore every countersequence to global congruence capture can
be replaced by a **pure regular-character countersequence**. Moving finite
quotient levels, their mixtures, and all hyperfinite character mass cannot
carry the gap.

For the \(\operatorname{SL}_2\) formulation, first split the common central
involution into its two exact sign sectors. Peterson--Thom character
classification gives a finite-quotient part and a center-supported regular
part in each sector. The same cutting argument applies sectorwise. After
passing to the projective packet, these are the same single regular
obstruction; no noncentral character face remains.

The estimate does not capture the regular corner by congruence
representations. It proves only that this corner is the unique possible
high-dimensional escape. The nonhyperlinear-group root remains open.

DERIVATION
central-cut-quantifies-the-regular-capture-obstruction
