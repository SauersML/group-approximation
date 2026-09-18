---
rg: 2
id: sl-odd-q-simple-inputs-for-gl-n-q-root-proof
kind: route
title: Jordan–Dickson simplicity of PSL_m over an infinite field, a trivial centre for odd m, and block-diagonal embeddings
target: sl-odd-q-simple-inputs-for-gl-n-q-root
requires: [gl-n-q-targets-are-cofinal-in-n]
---

**Clause 1.** `PSL_m(K)` is simple for every field `K` and every `m >= 2`,
except `m = 2` with `|K| <= 3` (Jordan–Dickson–Moore; see e.g. E. Artin,
*Geometric Algebra*, Ch. IV, or S. Lang, *Algebra*, Ch. XIII, §8). `Q` is
infinite, so `PSL_m(Q)` is simple. The centre of `SL_m(K)` is the group of
scalars `λI` with `λ^m = 1`. In `Q` the only roots of unity are `±1`, and
`(-1)^m = -1` for odd `m`. So the centre is trivial and `SL_m(Q) = PSL_m(Q)`.
It is infinite, since it contains the elementary matrices `I + qE_12`, `q in Q`.

**Clause 2.** `g ↦ diag(g, det(g)^-1)` is a homomorphism `GL_n(Q) -> SL_(n+1)(Q)`,
injective on the first block. For `m >= n + 1`, padding with an identity block
embeds `SL_(n+1)(Q)` in `SL_m(Q)`.

**Clause 3.** Odd `m` are unbounded. If `P(SL_m(Q))` holds for infinitely many
odd `m`, then for each `n` pick such an `m >= n + 1` and use clause 2. Conversely
`SL_m(Q) <= GL_m(Q)`. For general families of `n` this is also
`gl-n-q-targets-are-cofinal-in-n`.

**Clause 4.** The kernel of a homomorphism is normal. In the simple group
`SL_m(Q)` it is trivial or everything, and "nontrivial" excludes everything. ∎
