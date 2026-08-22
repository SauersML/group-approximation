---
rg: 2
id: atlas-rank-stability-primary-source-fence-proof
kind: route
title: Match the Atlas carrier operations against the published normalized-rank closure list
target: atlas-rank-stability-literature-fence
requires:
  - atlas-augmented-thirteen-vf-fillings
  - atlas-thirteen-vf-fillings-are-tietze-irredundant
---

Read Bauer--Blachar--Greenfeld arXiv:2401.04676v2 at Definition 1.1,
Theorems 5.1, 6.2, 7.2, 7.7, and Proposition 7.1.  Definition 1.1 allows
dimension change and is over an arbitrary field.  Theorem 5.1 therefore
applies to every modular finite group algebra in the Atlas graph, and
Proposition 7.1 applies to the ordinary free product of the two chart
algebras.  The paper has no occurrence or theorem for amalgamated free
products, graph products with identified subalgebras, or HNN extensions.
Its listed permanence operations are exactly free products, direct products,
and matrix rings.

The Cairn decomposition writes the carrier as a graph of finite groups with
nontrivial edge inclusions, then obtains `Gamma_+` by thirteen independent
normal fillings.  These are respectively an amalgam/HNN synchronization and
a quotient operation, neither in the published closure list.  Example 2.3
shows directly that finite-relator quotient permanence fails for associative
algebras in general.

Finally compare the metrics in the other primary sources.  Gerasimova--
Shchepin use complex unitary Schatten norms.  Fournier-Facio uses profinite
ultrametrics and explicitly excludes rank metric from that framework.
Mallahi-Karai--Mohammadi Yekta Proposition 6.1 treats one finite complex
group table.  Hence none supplies the two missing operations in binary
normalized rank, proving the citation fence.
