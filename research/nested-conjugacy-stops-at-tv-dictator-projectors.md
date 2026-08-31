---
rg: 2
id: nested-conjugacy-stops-at-tv-dictator-projectors
kind: claim
title: Nested-conjugacy embeddings stop at the zero-noise dictator projector
artifacts:
  - research/tv-nested-conjugacy-bridge-boundary-proof.md
distinct_from:
  tv-zero-noise-cell-is-an-abelian-torsor: that classifies the surviving local group; this audits whether the 2025 nested-conjugacy BCS embedding can add the missing dictator selection and still land in LCS.
  lcs-parity-gadgets-preserve-odd-dictator-affine-hull: that is a syntax-internal affine closure; this identifies the exact non-group projector relation and the precise scope of Fanizza et al. Theorem 5.5 and Lemma 3.12.
  perfect-completeness-constant-soundness-lcs-compiler: that asks for the terminal BCS-to-LCS bridge; this proves the new quantitative BCS embedding does not supply it.
---

The \(\epsilon=0\) Taller--Vidick residue is already entirely made of group
relations: in each outer cell it is the abelian-torsor presentation

$$
A_hB_kB_{hk}=1.
$$

Thus Fanizza--Kroell--Mehta--Paddock--Rochette--Slofstra--Zhao
[arXiv:2510.04943v4, Lemma
3.12](https://arxiv.org/html/2510.04943v4#S3) can route these relations
through a solution group, but this adds no constraint absent from the
original LCS.

Let \(P\) be the projected honest assignment support of one cell and assume
\(n=|P|\geq3\).  With basis reflections
\(Q_p=A_{\delta_p}\), the \(J=-1\) scalar profiles are the odd subsets
\(\beta\subseteq P\).  Honest dictators are the singleton subsets.  Their
affine hull is the entire odd-parity hyperplane.

The exact dictator condition is the non-group joint-spectral constraint

$$
E_\beta
 =\prod_{p\in\beta}\frac{1-Q_p}{2}
  \prod_{p\notin\beta}\frac{1+Q_p}{2}
 =0
\qquad\text{for every odd }|\beta|\geq3.                \tag{1}
$$

Equivalently, the commuting signs \(Q_p\) must satisfy the nonaffine
exactly-one predicate.  No finite system of group-word relations, nested
conjugacy group relations, or scalar-extendable group auxiliaries can impose
(1) while retaining every singleton: scalarizing any group presentation
gives affine parity equations, whose projected solution set contains the
affine hull of the singleton profiles.

Fanizza et al.
[Theorem 5.5](https://arxiv.org/html/2510.04943v4#S5.SS1) does encode (1)
quantitatively into a **BCS algebra**, preserves and extends tracial states,
and bounds relation-decomposition blow-up by
\(2^{16}M^2\ell^2\).  It does not make the outer exactly-one BCS constraint
linear.  Its proof retains one ordinary BCS relation and uses Lemma 3.12
only for the flattened conjugacy relations.  Hence its output is a general
BCS, not an LCS, at precisely the dictator projector.

Therefore the 2025 theorem is a genuine quantitative BCS-to-BCS bridge, but
not the missing perfect BCS-to-LCS compiler.  Applying the positive-noise
Taller--Vidick test after it again loses perfect completeness; applying the
zero-noise test again restores the same odd affine hull.

This is a fence for the direct composition only.  It does not rule out a new
non-scalar corner construction which converts the projector constraint into
a marked group relation with a reverse finite-dimensional decoder.
