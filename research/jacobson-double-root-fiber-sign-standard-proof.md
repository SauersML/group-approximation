---
rg: 2
id: jacobson-double-root-fiber-sign-standard-proof
kind: route
title: Exclude both doubled-root support profiles by the sign-versus-standard inequality for the shared S3
target: jacobson-double-rank-one-root-orbit-cannot-extend
requires:
  - jacobson-single-rank-one-root-orbit-cannot-extend
  - jacobson-first-root-packet-admits-coherent-relative-correction
  - binary-jacobson-gl3-k-branching-has-regular-counterprofile
artifacts:
  - research/artifacts/jacobson-double-rank-one-orbit-obstruction-2026-09-08.md
---

The doubled rank-one orbit has root negative rank 32. Comparing with
the conjugate head root forces the head stabilizer action on its
two-dimensional character fiber to be trivial. Its complement has
head negative rank four, which is too small for a tensor constituent
nontrivial on both factors of `F`. The braid trace equality then
forces the tail fiber to be two copies of the stabilizer sign.

On the `A_Q`-fixed standard `K_Q` multiplicity space, the original
packet consequently supplies `(2+t)*1+4*sign+4*standard` for some
nonnegative integer `t`. The boundary negative-rank formula leaves
exactly two support possibilities: `(m_1,m_2)=(4,0)` or `(1,1)`.
In the first, the target stabilizer's four-dimensional fiber has zero
or two negative dimensions on its normal-four-group involution. In
the second, the six fixed rank-two characters have a diagonal `S_3`
stabilizer; either one-dimensional stabilizer character contributes
one standard tail constituent to the selected multiplicity space.

In both cases, subtracting this forced nonzero-character contribution
leaves an actual `G_*` representation whose restriction to `K_P`
has more sign than standard constituents. The finite branching table
forbids this. Arbitrary head-trivial summands have no contribution to
the chosen standard `K_Q` multiplicity space.

The nonzero `N` orbit sizes and the preceding one-dimensional-fiber
exclusion give the dimension bound 147. Applying coherent correction
with the existing explicit constant leaves first-braid defect below
two, hence the exact involution trace equality needed above. This
proves the numerical bound in dimensions at most 146.
