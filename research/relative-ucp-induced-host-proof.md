---
rg: 2
id: relative-ucp-induced-host-proof
kind: route
title: Bound minimal Stinespring multiplicities by Frobenius reciprocity
target: every-relative-ucp-window-lives-in-one-induced-representation
requires:
  - finite-positive-definite-window-is-a-relative-corner-selector
---

Let \((\sigma,V_0)\) be the minimal Stinespring dilation of the relative
ucp map.  Unitary core values put \(C^*(B)\) in the multiplicative domain,
so \(\sigma(b)V_0=V_0\beta(b)\).

In the \(\pi\)-isotypic block
\(\sigma_\pi=\pi\otimes1_{\mathbb C^{m_\pi}}\), the multiplicity
components of \(V_0\) are elements of
\(\operatorname{Hom}_B(H_\beta,H_\pi|_B)\).  They are linearly independent:
a scalar dependence would exhibit a whole \(\pi\)-copy orthogonal to the
cyclic Stinespring span.  Hence

\[
m_\pi\leq\dim\operatorname{Hom}_B(H_\beta,H_\pi|_B).
\]

Frobenius reciprocity identifies the right side with the multiplicity of
\(\pi\) in \(\operatorname{Ind}_B^G\beta\).  Thus \(\sigma\) embeds in that
single finite induced representation, and composing the embedding with
\(V_0\) proves (UIR3)--(UIR4).  Compression gives the converse.  Applying
this equivalence to the marked involution gives the Stiefel formula (UIR8).
