---
rg: 2
id: arrangement-bnsr-invariants-avoid-real-resonance
kind: claim
title: "For a hyperplane arrangement complement in C^l, Sigma^q(M,Z) avoids the real points of the resonance variety R^q for 1 <= q <= l-1"
artifacts:
  - research/artifacts/zp-pure-braid-bnsr-middle-range-2026-09-13.md
---

Let `M` be the complement of a complex hyperplane arrangement in `C^l`. For
`1 <= q <= l - 1`,

    Sigma^q(M, Z) ⊆ S(Trop(V^q(M)))^c ⊆ S(R^q(M; R))^c,

where `V^q` is the degree-`q` characteristic variety, `R^q` the degree-`q`
resonance variety of the cohomology ring, and `R^q(M;R)` its real points. In
particular, for the braid arrangement, `Sigma^q(P_n) ⊆ S(R^q(P_n; R))^c` for
`1 <= q <= n - 1`.

This is the "resonance upper bound": characters in the real resonance variety
are never in the invariant. Whether the bound is attained for the braid
arrangement is `pure-braid-bnsr-complements-are-real-resonance-varieties`.
