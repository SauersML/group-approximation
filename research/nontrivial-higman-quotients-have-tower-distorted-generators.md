---
rg: 2
id: nontrivial-higman-quotients-have-tower-distorted-generators
kind: claim
title: In every nontrivial quotient of Higman's group each generator has infinite order and tower-type distortion
distinct_from:
  higman-group-images-in-nv-force-zero-entropy-bs12-cycles: that constrains images of Higman's group in Brin--Thompson groups through entropy; this is an abstract distortion bound valid in every nontrivial quotient and every overgroup.
artifacts:
  - research/artifacts/solve-higman-sofic-2026-09-13.md
---

**ESTABLISHED** by `higman-quotient-tower-distortion-proof` (elementary; no
novelty claimed).

**Statement.** Let `Q` be a nontrivial quotient of `H4`, let `g_0, g_1, g_2, g_3`
be the images of `a, b, c, d` (indices mod 4), and let `|.|` be word length for
`S = {g_i^(+-1)}`. Put `T(0) = 1` and `T(j+1) = 2^T(j)`. Then:
1. every `g_i` has infinite order;
2. for all `i` and all `j >= 0`, `|g_(i+j)^T(j)| <= 2^(j+1) - 1`.

So the distortion function of `<g_i>` is at least `r -> T(floor(log2(r+1)) - 1)`,
which eventually exceeds every iterated exponential of fixed height.

**Consequence.** Let `psi : H4 -> Gamma` be a homomorphism into a finitely generated
group. Suppose some `psi(g_i)` either has finite order, or generates a cyclic
subgroup of `Gamma` whose distortion is bounded by an iterated exponential of fixed
height. Then `psi` is trivial.
- Word length in `Gamma` is at most a constant times word length in `psi(H4)`.
- A nontrivial `psi(H4)` is a nontrivial quotient of `H4`.

For instance, `psi` is trivial when infinite cyclic subgroups of `Gamma` are
undistorted, as in hyperbolic groups and groups acting properly and cocompactly on
CAT(0) spaces. Those are standard facts that were not re-read here.
