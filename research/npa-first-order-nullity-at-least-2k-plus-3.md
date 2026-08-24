---
rg: 2
id: npa-first-order-nullity-at-least-2k-plus-3
kind: claim
title: The compressed moment kernel has dimension at least two k plus three
artifacts:
  - research/artifacts/npa-critical-face-dimension-law-audit-2026-08-23.md
distinct_from:
  npa-first-order-nullity-at-most-2k-plus-3: that half must exhibit enough independent rows of the level-k system and is an induction on shells; this half must exhibit enough independent kernel vectors and is a construction, with no inductive content and no dependence on the unseen-class lemma.
---

For every `k >= 2`, `dim ker Phi_k >= 2k+3`; equivalently there are `2k+3`
linearly independent `y` with `N_k^T Gamma_k(y) N_k = 0`.

**This half has no source and no proof.**  The ingesting dossier and its
follow-up both discharge it onto arXiv:2607.13762 -- "the paper already has the
constructive all-`k` lower bound", "exactly the side Section 9 says was known" --
and three independent retrievals of that paper and of its companion found no such
statement, no dimension formula for `V_k`, and no matching Section 9.1 text.  The
retrievals are model-rendered, so the audit leaves the attribution question open;
what is not open is that no construction has been exhibited anywhere in this
chain.

The consequence is that the dimension law is currently **two open halves, not
one**.  A reader who accepts the withdrawn-by-one-lemma status of the upper bound
still has no proof of the equality, because the direction that is supposed to be
free is the one nobody in the chain has written down.

## Attempts

The most promising construction available from the imported structural laws, and
not yet carried out: the kernel law holds not only at `delta*` but on an explicit
open family of `delta`, so `Gamma_k(y_0(delta)) N_k = 0` and hence
`y_0(delta)` lies in `ker Phi_k` for every `delta` in an open subset of `R^k`.
If `delta |-> y_0(delta)` is affine, its image spans an affine subspace of
dimension `k` inside `ker Phi_k`, giving `dim ker Phi_k >= k+1` immediately.  The
affineness of the face parametrization was not checked here and is the first
thing to settle.

That would leave `k+2` further directions.  The natural source for them is the
shell picture itself: each level is supposed to contribute `4` fresh unseen
coordinates, on which no row of the system has any support, and a coordinate on
which every row vanishes is a kernel direction outright.  So a proof of
`npa-unseen-classes-are-free-at-level-k` would very likely pay for both halves at
once -- the freeness lemma is exactly a statement that certain coordinate
directions lie in the kernel.  That coupling is worth noting before anyone
attacks the two halves separately: they may be one problem.
