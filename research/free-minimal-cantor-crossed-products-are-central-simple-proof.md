---
rg: 2
id: free-minimal-cantor-crossed-products-are-central-simple-proof
kind: route
title: Cut a nonzero element down to a scalar on a clopen set around a free point and spread it by minimality; topological freeness kills off-diagonal central coefficients
target: free-minimal-cantor-crossed-products-are-central-simple
requires: []
---

The notation is that of the target. The proof is self-contained.

By Baire and countability, points with trivial stabilizer are dense in `X`.

**Simple.** Let `I` be a nonzero ideal and `0 ≠ b = Σ_(g ∈ F) f_g u_g ∈ I` with `F` finite.
Replacing `b` by `b u_h^(-1)` for some `h` with `f_h ≠ 0`, we may assume `f_1 ≠ 0`.
- Pick `x` with trivial stabilizer in the clopen set where `f_1` takes a nonzero value `c`.
- Choose a clopen `W ∋ x` on which every `f_g` is constant, with `W ∩ gW = ∅` for `g ∈ F \ {1}`.
- Then `1_W f_g u_g 1_W = f_g 1_(W ∩ gW) u_g = 0` for `g ≠ 1`. So `1_W b 1_W = c 1_W` and `1_W ∈ I`.
- By minimality and compactness, `X = g_1 W ∪ ... ∪ g_n W`. Each `1_(g_i W) = u_(g_i) 1_W u_(g_i)^(-1)`
  lies in `I`. Disjointify to clopen `W_i' ⊆ g_i W`; then `1_(W_i') = 1_(W_i') 1_(g_i W) ∈ I`, and
  these sum to `1 ∈ I`.

**Centre.** Let `z = Σ f_g u_g` be central. For all `f ∈ LC(X, k)`, `fz = zf` gives
`f_g (f - f ∘ g^(-1)) = 0`.
- If `f_g ≠ 0` on a nonempty clopen `V`, then `f(y) = f(g^(-1) y)` for all `y ∈ V` and all `f`.
  Clopen sets separate points, so `g^(-1)` fixes `V` pointwise, and `g = 1` by topological freeness.
- So `z = f_1`, and `u_h z u_h^(-1) = z` makes `f_1` invariant. It is locally constant, so each of its
  level sets is a clopen invariant set, and minimality forces `f_1` to be constant.

So `Z(B) = k`. ∎
