---
rg: 2
id: one-small-higman-generator-collapses-the-four-cycle
kind: claim
title: One sub-semicircle Higman generator collapses the whole operator-norm cycle
artifacts:
  - research/one-small-higman-generator-collapses-the-four-cycle-proof.md
distinct_from:
  higman-four-cycle-intrinsic-mf-seed: that asks for collapse with no spectral assumption; this proves the collapse with an explicit dimension-free constant as soon as one generator is at operator-norm distance at most sqrt(2) from the identity.
  periodic-higman-bs-clocks-have-three-opnorm-small-seams: that exhibits proper-subcycle clock packets whose conjugators have distance exactly 2 from the identity; this explains quantitatively why any full countermodel must remain outside the small-arc basin at every vertex.
---

**ESTABLISHED.**  Let `(U_0,U_1,U_2,U_3)` be finite-dimensional unitaries and
put

```text
delta=max_i ||U_i U_(i+1) U_i^* - U_(i+1)^2||_op,    (HAC1)
```

with indices modulo four.  If for some `j`

```text
||U_j-1||_op <= sqrt(2),                              (HAC2)
```

then

```text
max_i ||U_i-1||_op <= (15+8sqrt(2)) delta.            (HAC3)
```

In particular, in any noncollapsing operator-norm Higman microstate sequence,
every generator eventually has distance strictly greater than `sqrt(2)` from
the identity.  Thus a countermodel to `higman-four-cycle-intrinsic-mf-seed`
cannot be made by keeping one occurrence in a logarithmic/small-spectrum
basin and placing the clock behavior only at the other three vertices: all
four occurrences must carry macroscopic circle spectrum simultaneously.
