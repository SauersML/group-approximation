---
rg: 2
id: kt-pair-non-hyperlinear-rigidity
kind: route
title: Refute hyperlinearity of the Kun–Thom wreath group by a rigidity theorem
target: non-hyperlinear-group
requires: [invariant-cartan-completion]
artifacts:
  - notes/TRUE_DIAGONAL_NORMALIZER_RIGIDITY.md
---

# Refute hyperlinearity of the Kun–Thom wreath group

The rigidity-side twin of `growing-fiber-models`, carried so that the graph
records both outcomes of the same fork rather than only the one the programme
wants.

`W = (⊕_(G/Γ) ℤ/2ℤ) ⋊ G` for Kun–Thom's Theorem E pair is a *specific,
finitely generated, explicitly presented* group. If `invariant-cartan-completion`
holds, then every trace-preserving embedding of
`M_KT = L^∞({±1}^(G/Γ)) ⋊ G` into a matrix tracial ultraproduct can be
conjugated to have an invariant diagonal ultraproduct containing the Bernoulli
algebra; `diagonal-normalizer-rigidity` clause 4 converts that into a
Păunescu-sofic embedding of the generalized Bernoulli action; and
`coordinate-action-not-sofic` (Kun–Thom Corollary D) says none exists. Hence
no embedding exists at all, `M_KT` is not Connes embeddable, and `W` is not
hyperlinear.

Two consequences worth stating so the stakes are visible, and so that nobody
reaches for this route casually:

- it would exhibit the first non-hyperlinear group, hence the first group von
  Neumann algebra refuting the Connes embedding problem — an object the
  post-MIP\* literature explicitly records as not yet produced;
- it would simultaneously refute `hyperlinear-wreath-model` and close the
  flexible branch of `hyperlinear-nonsofic-group` at this candidate.

The route is listed with `requires: [invariant-cartan-completion]` and not as
a direct proof: the conversion step is proved (cited note, Theorem 6 and
Corollary 7), the completion step is open, and nothing in the cited literature
supplies it. `kt-centralizer-normalization-hs` is a second, independent
sufficient input for the same conclusion, through Theorem A's endgame rather
than through Corollary D; it is carried as its own claim.
