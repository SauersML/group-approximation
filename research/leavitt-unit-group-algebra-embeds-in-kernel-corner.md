---
rg: 2
id: leavitt-unit-group-algebra-embeds-in-kernel-corner
kind: claim
title: The Leavitt unit group algebra embeds unitally in a corner of its own evaluation kernel
distinct_from:
  leavitt-matrix-amplification-in-unit-group-algebra: that embeds matrix algebras over the group algebra in the corner eSe, which lies over the evaluation identity; this embeds the group algebra itself in the complementary corner zSz, which lies inside the evaluation kernel.
  leavitt-evaluation-kernel-hits-augmentation-one: that records the kernel idempotent z = [1] + [g] + [g^2]; this proves that the corner cut by z contains a unital copy of the whole group algebra.
artifacts:
  - research/artifacts/scalar-corner-kernel-embedding-2026-09-12.md
---

Let `R = L_(F_2)(1,2)`, `G = R^x`, `S = F_2[G]`, `pi : S ->> R` the evaluation and
`K = ker pi`. Put `u = 1 + s_0 t_1`, `v = 1 + s_1 t_0`, `g = uv`,
`z = [1] + [g] + [g^2]`, `e = [g] + [g^2] = 1 - z`, and
`delta(q) = s_0 q t_0 + s_1 q t_1`.

Then `z` is an idempotent in `K`, `pi(e) = 1`, and

    j : S -> zSz,     j(x) = delta(x) z,

is an injective unital ring homomorphism into the corner `zSz`, which lies in `K`.
Padding by `e` gives the injective unital multiplicative map

    Phi : S -> K^+ = F_2 1 + K,     Phi(x) = delta(x) z + e.

The scalar copy `delta(G)` commutes with the constant `S_3 = <u, v>` and meets it only
in `1`, so `F_2[delta(G)] (x) F_2[H]` sits inside `S`. `z` is the complement of the
`S_3` block over `1`, and it is killed by evaluation.

Proof: Theorem 3 of the artifact.
