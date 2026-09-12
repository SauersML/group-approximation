---
rg: 2
id: jacobson-root-orbit-shared-multiplicity-proof
kind: route
title: Compare the fixed-source multiplicity space in the original and boundary finite packets
target: jacobson-single-rank-one-root-orbit-cannot-extend
requires:
  - jacobson-mixed-cells-reconstruct-full-first-level-root-packet
  - jacobson-boundary-cell-reconstructs-finite-root-packet
  - binary-jacobson-gl3-k-branching-has-regular-counterprofile
  - jacobson-first-root-packet-admits-coherent-relative-correction
artifacts:
  - research/artifacts/jacobson-single-rank-one-orbit-obstruction-2026-09-08.md
  - research/artifacts/jacobson-first-root-packet-dimension-audit-2026-09-08.md
  - research/artifacts/jacobson-first-root-packet-coherent-rounding-2026-09-08.md
---

A multiplicity-one rank-one `N` orbit has dimension 49 and root
negative rank 16. Its four possible stabilizer sign twists give head
negative rank 14 or 28. The conjugacy `D=h a_1 h` forces rank 14
and leaves exactly two negative head dimensions in its complement.
The finite character table therefore makes that complement one head
representation of dimension three or six, together with arbitrary
head-trivial representations. The tail on the former is trivial.

The conjugacies of `h`, the first-braid involution, and a shifted
transvection force the nontrivial tail sign twist. Next restrict to
the `A_Q`-fixed subspace and its standard `K_Q` multiplicity space.
The boundary packet must have rank-one character multiplicity two and
no rank-two characters. Its forced contribution either already exceeds
the original packet's trivial `K_P` multiplicity, or leaves two copies
of the sign of `K_P` on the rank-zero multiplicity space. That latter
space would have to be a two-dimensional representation of `G_*`,
which is impossible. Arbitrary head-trivial summands do not affect
this standard `K_Q` multiplicity space.

The next possible nonzero `N` support has dimension at least 98.
For each smaller dimension, exact compatible finite-factor tables with
marked distance two form a compact set. The mixed error is continuous
and has no zero there. Taking the minimum over the finitely many
dimensions gives the claimed bounded-dimension gap.

For the explicit constant, suppose both errors are at most
`1/(8192*2,228,976)`. The coherent correction prerequisite gives
`delta<=1/4096`, so it preserves the dimension and head mark and
leaves first-braid error below two. The involutions `H'bH'` and
`bH'b` are then at distance less than two, hence have the same
negative rank. They are respectively conjugate to `b` and `H'`,
so the trace equality used in the exclusion holds exactly. All other
steps use only the corrected exact packets and their shared root.
The exclusion therefore still applies, contradicting dimension at
most 97 and proving the explicit lower bound.
