---
rg: 2
id: slofstra-solution-group-embedding-preserves-marked-involutions
kind: claim
title: Slofstra effectively embeds every finitely presented marked group into a solution group while preserving its central sign and chosen involutions
distinct_from:
  perfect-completeness-constant-soundness-lcs-compiler: that asks for a new perfect-completeness matrix-soundness compiler from contextual data; this theorem starts with an ordinary finitely presented group and preserves exact marked elements, but supplies no matrix-soundness estimate by itself.
  lcs-tracial-ru-gap-equiv-nonhyperlinear: that is the endpoint equivalence between a tracial/non-RU LIN system and a finitely presented nonhyperlinear group; this is the exact constructive group-embedding input used in the group-to-LIN direction.
  slofstra-involution-not-sofic-radical: that proves the particular central sign used in Slofstra's Tsirelson separation survives a permutation ultraproduct; this records the general exact embedding theorem and makes no approximation claim.
---

**ESTABLISHED BY CITATION.**  Let `G` be a finitely presented group, let
`J' in Z(G)` satisfy `(J')^2=1`, and let `w_1,...,w_n in G` be involutions.
There is a finite binary linear system, equivalently a finite hypergraph
`H` with a vertex labelling `b`, a solution group `Gamma(H,b)` with its
distinguished central involution `J`, selected edge generators
`x_(e_1),...,x_(e_n)`, and an injective homomorphism

```text
phi:G -> Gamma(H,b)
```

such that

```text
phi(J')=J,              phi(w_i)=x_(e_i)  (1<=i<=n).       (SSE1)
```

The construction is effective from a finite presentation and words for the
marked elements.

Proof: `slofstra-wagon-wheel-embedding-citation`.

The theorem is exact and algebraic.  It preserves nontriviality of the marked
central sign and turns chosen involutions into literal LCS variables.  It does
not assert that approximate representations of the output can be decoded into
anything beyond their fixed-word restrictions to the embedded input group.
