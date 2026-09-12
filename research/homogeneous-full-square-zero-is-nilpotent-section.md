---
rg: 2
id: homogeneous-full-square-zero-is-nilpotent-section
kind: claim
title: In a homogeneous bundle algebra a square-zero element is full iff it vanishes at no point
distinct_from:
  full-square-zero-gap-forces-dd-torsion: that assumes a full square-zero section of a continuous-trace algebra and extracts projections from a spectral gap; this only identifies fullness with pointwise nonvanishing for a locally trivial matrix bundle.
---

**ESTABLISHED.**  Let `X` be a compact Hausdorff space, `E` a complex vector
bundle of rank `n` over `X`, and `A=Gamma(X, End E)` its algebra of
continuous endomorphism sections.  An element `x in A` is full if and only if
`x_t != 0` for every `t in X`.

Consequently `A` contains a full square-zero element if and only if the fibre
bundle `N_0(E) -> X`, whose fibre over `t` is the space of nonzero
square-zero endomorphisms of `E_t`, admits a continuous section.
