---
rg: 2
id: expander-tree-boundary-k0-max-reduced-injective
kind: claim
title: For a host with isometrically embedded large-girth expanders, the max-to-reduced map is injective on K_0 for the tree boundary of the expander-marking subshift
distinct_from:
  monster-bc-detector-lives-on-a-proper-orbit-ideal: that imports Finn-Sell's theorem that the partial-translation boundary groupoid over the corona is a-T-menable; this asks for K_0 injectivity of max to reduced for the transformation groupoid of the tree-boundary configurations in G.
---

**OPEN.** Let `G`, `(A_n)` and `∂Y` be as in hypotheses (M) of `hls-ghost-lift-needs-forest-shift-failure`: the nonzero
tree-boundary configurations of the expander-marking subshift inside `(Z/p)^G`. The claim is that
`K_0(C_0(∂Y \ {0}) ⋊_max G) -> K_0(C_0(∂Y \ {0}) ⋊_r G)` is injective.

**Why it matters.**
- It is hypothesis (H-K) of `hls-ghost-lift-needs-forest-shift-failure`, the analogue of HLS Lemma 1(2).
- With it, ghost ranks on the marked expanders certify that a full-shift class lies outside the cylinder image.
- Without it, the reduction to the forest shift is not available.

## Attempts

- **a-T-menability (Tu).**
  - Nonzero boundary points are configurations whose supports are isometrically embedded `D`-regular trees.
  - Tree distance between nearest support points gives a conditionally negative definite kernel on each orbit.
  - A continuous proper conditionally negative definite function on `(∂Y \ {0}) ⋊ G` would give K-amenability, hence the
    claim.
- **Where it stops.**
  - Nearest-point projections onto the support are not canonical.
  - A continuous choice across all boundary points, proper on arrows over compact sets, is not written.
  - Finn-Sell's a-T-menability of the corona groupoid concerns partial translations on the Stone--Čech corona, not this
    transformation groupoid. The transfer is not written.
