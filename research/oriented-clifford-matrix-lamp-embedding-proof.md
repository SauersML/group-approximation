---
rg: 2
id: oriented-clifford-matrix-lamp-embedding-proof
kind: route
title: Realize each Clifford generator as a Pauli string along its out-neighbours
target: oriented-clifford-skew-rings-embed-in-matrix-lamp-wreath
requires: []
artifacts:
  - research/artifacts/clifford-skew-ring-matrix-lamp-wreath-2026-09-12.md
---

The proofs are Propositions 1.1–1.4 and Example 1.2 of the artifact.

- **Relations.**
  - `p_x` anticommutes only with `s_x`.
  - So `iota(c_x)` and `iota(c_x')` anticommute exactly when `x' in N+(x)` or `x in N+(x')`, which happens
    exactly when they are adjacent, since each edge is oriented once.
  - The factor `s_x^q(x)` fixes the square.
- **Injectivity.** The `p`-support of `iota(c_T)` is `T`. The crossed product is free over the lamp algebra
  on the group tags.
- **Compressor graph.**
  - `psi` is equivariant, has no fixed points and no 2-cycles, so `{(x, psi x)}` is an invariant orientation
    with out-degree one.
  - A nonempty finite radical vector would need a child of every one of infinitely many children, so
    the form is nondegenerate.
- **Complete graph.**
  - Even vectors carry the form `|v cap w| mod 2`.
  - `{x1,x2}` and `{x2,x3}` meet once.
  - Quaternions split over finite fields.
- **Commutative form.** Fourier transform on the `s`-lamps turns the `p`-lamps into coordinate flips.

*Verification by `w4-vf-linear-b` (2026-09-12), Section 14 of `research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`: PASS. Re-derived independently:*
- *the sign count per site, `(ps)^2 = -1`, and injectivity through Pauli strings of distinct `p`-support;*
- *for the compressor graph, that `u ∉ Γ` and `u^2 ∉ Γ`, and the child argument for nondegeneracy;*
- *the even-subset form, and the uniform quaternion split giving an equivariant injective map into the complete-graph ring.*
