---
rg: 2
id: rank-one-rational-projective-full-group-is-flip-v
kind: claim
title: In rank one the integral projective full group of the rational Cantorization is the Röver–Nekrashevych group of the letter flip, hence finitely presented
distinct_from:
  rational-projective-full-groups-are-finitely-presented: that is the finiteness gate for every m; this settles the case m = 1 and explains why the method is special to m = 1.
  closed-mcg-embeds-in-rational-projective-full-group: that constructs the hosts T_m and embeds mapping class groups; this identifies T_1 exactly.
---

**ESTABLISHED** (lane bh-free-54, 2026-09-18). Lane proof, not independently
reviewed; no priority claimed.

## Statement

Let `𝒯_1 = [[GL_2(Z) ⋉ Ŝ_1]]`, as in
`closed-mcg-embeds-in-rational-projective-full-group`. Let `σ` be the
automorphism of the binary tree `{L,R}*` that exchanges the two letters at every
level. It is self-similar with `σ|_x = σ`. Then:

- `𝒯_1 ≅ V_{2,4}(⟨σ⟩)`, the Röver–Nekrashevych group of the order-two
  self-similar group `⟨σ⟩` on four binary trees;
- `𝒯_1` is finitely presented. `⟨σ⟩` is finite, hence contracting, and
  Nekrashevych proved that `V_{d,r}(G)` is finitely presented for contracting `G`
  (arXiv:1312.5654; recalled, not re-read here);
- `V_{2,4} ≅ V ≤ 𝒯_1`, and `SL_2(Z) = Mod(S_1) ≤ 𝒯_1`.

So the gate `rational-projective-full-groups-are-finitely-presented` holds at
`m = 1`, and the genus-one calibration of the mapping class host is complete.

## Proof

1. **Four trees.**
   - `Ŝ_1` is the circle with every rational ray doubled.
   - It is the disjoint union of the four quadrant clopens `Q_ε = cone(εe_1, ε'e_2)`
     in cyclic order. Each is unimodular, with frame determinant `+1`.
   - **Stern–Brocot tree.** In `Q = cone(e_1, e_2)`, write `L = [[1,1],[0,1]]` and
     `R = [[1,0],[1,1]]`. The frame `g = [v w]` has children `gL = [v, v+w]` and
     `gR = [v+w, w]`, the two mediant subcones.
   - `SL_2(Z) ∩ Mat_2(Z_{≥0})` is the free monoid on `L, R` (classical). The
     nodes `g ∈ {L,R}*` are exactly the unimodular subcones of `Q` with their
     positively oriented frames, since every Farey pair is a Stern–Brocot node
     (classical).
2. **`Q ≅ {L,R}^N`.**
   - Non-eventually-constant words converge to irrational rays.
   - A word `uL^∞` converges to the first vector of `u`'s frame, from inside the
     cone.
   - A word `uR^∞` converges to its second vector, from inside.
   - Every interior rational ray is the mediant of exactly one node `u`, and its
     two one-sided points are `uLR^∞` and `uRL^∞`. The two boundary rays of `Q`
     are `L^∞` and `R^∞`.
   - This is a bijection. It is a homeomorphism, because every rational
     polyhedral regular open subset of `Q` is a finite union of nodes (both
     endpoints are rational, so they occur at finite depth).
3. **Germs.**
   - Let `h ∈ GL_2(Z)` and let `ξ` lie in a node `u` of some quadrant.
   - Refining `u` to finite depth, we may assume `hu` lies inside one quadrant.
     The preimages of the axes are rational rays, which occur at finite depth.
   - Then `hu` is a unimodular cone in that quadrant, hence a node `u'`, and
     `h·(frame of u) = (frame of u')·S^ε`. Here `S` is the swap and
     `ε = 0` or `1` according to `det h = ±1`.
   - Since `S L S = R`, the map `h` sends `u w` to `u' σ^ε(w)` for every word `w`.
   - Conversely, every prefix replacement `u w ↦ u' σ^ε(w)` between nodes of
     any quadrants is the germ of `h = (frame of u')·S^ε·(frame of u)^{-1}`, which
     lies in `GL_2(Z)`.
4. **Conclusion.** The germ groupoid of `GL_2(Z) ⋉ Ŝ_1` is the groupoid of germs
   of `u w ↦ u' σ^ε(w)` on four binary trees. Its full group is by definition
   `V_{2,4}(⟨σ⟩)`. The `ε = 0` germs give `V_{2,4} ≅ V`.

## Why this is special to rank one

The proof uses that nonnegative unimodular matrices form a free monoid, so that
unimodular subcones form a tree. For `m ≥ 2` that fails. In `R^3`, the
unimodular subcones `C_1 = cone(e_0+e_1, e_1, e_2) = {x_0 ≤ x_1}` and
`C_2 = cone(e_0, e_1, e_1+e_2) = {x_2 ≤ x_1}` of `Δ` meet in the cone
`{x ≥ 0, x_0 ≤ x_1, x_2 ≤ x_1}`. That cone has the four extreme rays
`e_1, e_0+e_1, e_1+e_2, e_0+e_1+e_2`, so it is not simplicial. So:
- the monoid `GL_{m+1}(Z) ∩ Mat(Z_{≥0})` is not right-LCM for `m ≥ 2`;
- the unimodular subcones of `Δ` do not form a tree;
- neither Nekrashevych's tree framework nor X. Li's Garside-category framework
  (arXiv:2110.04505) applies as stated.

See Attempt 2 on `rational-projective-full-groups-are-finitely-presented`.
