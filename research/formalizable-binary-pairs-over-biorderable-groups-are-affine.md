---
rg: 2
id: formalizable-binary-pairs-over-biorderable-groups-are-affine
kind: claim
title: Over a bi-orderable group, a formalizable left-inverse pair of binary one-track automata is a translation composed with a complement
distinct_from:
  formal-polynomial-strict-pairs-need-unstable-linearization: that shows a formal left-inverse identity forces bijectivity under direct finiteness; this uses that two-sided formal inverse and a degree count in the extreme variable to show that formal one-track pairs over bi-orderable groups are affine translations.
  multilinear-collapse-defect-does-not-obstruct-bijectivity: that calibrates canonical representatives of a formalizable sitewise pair on three tracks; this classifies all formalizable pairs on one track over bi-orderable groups.
artifacts:
  - research/artifacts/binary-formalizability-refutation-2026-09-12.md
  - research/artifacts/gk-vf-nonlinear-verification-2026-09-12.md
---

Let `G` carry a total order invariant under left and right multiplication. Let `tau`, `sigma` be
automata on `{0,1}^G` with `sigma o tau = id`. Suppose some polynomial representatives of their
local rules, on any finite memories, satisfy `sigma~ o tau~ = id` as a formal polynomial identity.
Then there are `m in G` and `eps in F_2` with `tau(x)(g) = x(gm) + eps`.

**Proof outline** (artifact, Section 1).
1. **Direct finiteness.** `F_2[G]` is a domain by the leading-term argument, hence directly finite.
2. **Algebraic independence.** `formal-polynomial-strict-pairs-need-unstable-linearization` makes
   `tau~ o sigma~ = id` formally. So the pullback of `tau~` is injective, and the translates of its
   local polynomial are algebraically independent.
3. **Extreme variables.** The variable at `v₊ w₊`, the product of the largest window elements,
   occurs only through `tau~` at cell `v₊`. It has degree `DE >= 1` there, with nonzero leading
   coefficient. The composite is `X_1`, so `v₊ w₊ = 1 = v₋ w₋`, and both windows are single cells.
4. **Univariate step.** A polynomial in one variable with a polynomial inverse is `t + eps`.

The one-track hypothesis is essential. On several tracks, shears between tracks are formal
involutions.
