---
rg: 2
id: nikolov-segal-generation-by-conjugates-citation
kind: route
title: Nikolov--Segal, Generators and commutators in finite groups, Theorems 1.1 and 1.2, read from arXiv:1102.3037v6
target: nikolov-segal-generation-by-conjugates
requires: []
---

Read from the arXiv PDF (arXiv:1102.3037v6, dated 13 Dec 2011 on the arXiv stamp, title page dated
November 7, 2018), pages 1--3, on 2026-09-13 by lane `ex2-weak-sofic-bounded-factors`. The PDF was fetched on
MSI and the pages were read as images. The published numbering was not re-checked.

Page 1: "for `g in G` we write `[G, g] = {[x, g] | x in G}` where `[x, g] = x^-1 g^-1 x g` is the usual commutator."

Page 2, Subsection 1.1: "In this subsection all groups are assumed to be *finite*. The minimal size of a
generating set for `G` is denoted `d(G)`. To a finite group `G` we associate the characteristic subgroup"
```text
G_0 = ∩ { T ◁ G | G/T is almost-simple }  =  ∩_(M in 𝒮) C_G(M)        (1)
```
"where `𝒮` is *the set of all non-abelian simple chief factors of* `G` (a group `H` is *almost-simple* if
`S ◁ H <= Aut(S)` for some non-abelian simple group `S`). ... (Note that `G_0 = G` if `𝒮` is empty, by the usual
convention.)"

Page 3:

> **Theorem 1.1** *Let `G` be a group and `K <= G_0` a normal subgroup of `G`. Suppose that
> `G = K<y_1, ..., y_r> = G'<y_1, ..., y_r>`. Then there exist elements `x_ij in K` such that*
> `G = < y_i^(x_ij) | i = 1, ..., r, j = 1, ..., f_0 >`
> *where `f_0 = f_0(r, d(G)) = O(r d(G)^2)`.*

> "Recall that `G_0 = G` if every non-abelian chief factor of `G` has composition length at least 2, in
> particular if `G` is soluble; the result in the soluble case was established in [S1]."

> For a subset `X` of a group `G`, we write `X^(*f) = {x_1 x_2 ... x_f | x_1, x_2, ..., x_f in X}`.

> **Theorem 1.2** *Let `G` be a group and `{y_1, ..., y_r}` a symmetric generating set for `G`. If `H` is a
> normal subgroup of `G` then*
> `[H, G] = ( prod_(i=1..r) [H, y_i] )^(*f_1)`
> *where `f_1 = f_1(r, d(G)) = O(r^2 d(G)) = O(r^3)`.*

Page 4 also records a variant of Theorem 1.2 in which the `y_i` only generate `G` modulo `C_G(H)`, "the proof
is a little more involved and will appear elsewhere". It is not used.

The proofs use the classification of finite simple groups in general. [S1] is D. Segal, *Closed subgroups of
profinite groups*, cited there for the soluble case of Theorem 1.1.
