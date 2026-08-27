---
rg: 2
id: block-monomial-fiber-models
kind: route
title: Block-monomial fiber models (lamps diagonal, group unitaries monomial in U(m))
target: hyperlinear-wreath-model
requires: []
artifacts:
  - notes/TRUE_BLOCK_MONOMIAL_COORDINATE_COLLAPSE.md
---

# Block-monomial fiber models

Put the model space at `ℂ^{Y_n} ⊗ ℂ^{m_n}` with `m_n → ∞`, keep the lamps on
the coordinates (`Θ(a_x) ∈ D_{Y_n} ⊗ 1`), and make every `Θ(u_g)`
block-monomial: a permutation of `Y_n` carrying arbitrary `U(m_n)` blocks. The
attraction is that `Θ(u_g)` is then not a permutation matrix, so Kun–Thom
Corollary D does not literally apply, and that the fiber can supply
Hilbert–Schmidt separation for the group elements the coordinate permutation
`σ_n` fails to separate — relieving `σ_n` of ever having to be a sofic
approximation of `G`. This is the most natural constructive reading of "the
trace is blind to sizes", and it is the first thing to try after
`coordinate-action-not-sofic`.

Dead: the permutation part survives the fiber. `‖A − B‖₂² ≥ 2 d_H(π(A), π(B))`
uniformly in `m`, because a mismatch of permutation parts displaces a whole
block, so multiplicativity of `Θ` descends to `σ_n` and the lamps stay
covariant for it. The relief `σ_n` was granted — non-faithfulness on `G` — is
then bought back for free by tensoring with a sofic representation of `G`,
which exists because `G` is residually finite. What comes out is a genuine
sofic-action witness (`block-monomial-coordinate-collapse`).

The trace really is blind to the fiber. The obstruction simply does not live
there: it rides on the lamps, and the lamps are faithfully represented on the
coordinates whatever the fiber does.

**What survives the demolition.** The route is dead only for *exact*
block-monomiality in the ultraproduct. `growing-fiber-models` carries the
weakened form — no invariant coarse block decomposition at all — which is what
the collapse forces the specification to become.
