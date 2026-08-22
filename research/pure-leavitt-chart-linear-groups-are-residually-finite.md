---
rg: 2
id: pure-leavitt-chart-linear-groups-are-residually-finite
kind: claim
title: The pure s-chart and t-chart linear groups are residually finite
distinct_from:
  leavitt-rank-three-support-group-is-virtually-free: that proves residual finiteness for two specific three-generator subgroups; this proves it for the full GL2 groups over the two free coefficient subalgebras.
  openai-leavitt-unit-nonsofic: that concerns the full unit group using both Leavitt halves; this identifies two large residually finite one-sided chart subgroups inside it.
  leavitt-gl-equals-el-and-perfect-unit-group: that computes the full linear group over the whole Leavitt algebra; this uses finite truncations of the proper free subalgebras.
artifacts:
  - research/artifacts/one-nonnormal-packet-corner-correction-2026-08-21.md
---

The subalgebras

```text
R_t=F_2<t_0,t_1>,        R_s=F_2<s_0,s_1>
```

of the binary Leavitt algebra are free associative algebras, and
`GL_2(R_t)`, `GL_2(R_s)` are residually finite.  Indeed quotienting a free
algebra by all words longer than `n` gives a finite ring, and these quotients
separate every nonzero polynomial.  A nonidentity invertible matrix is
separated by a quotient detecting one nonzero entry of its difference from
the identity; its inverse descends, so the image remains in a finite general
linear group.

