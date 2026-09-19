---
rg: 2
id: c2-rose-mapping-torus-has-no-one-lift-core-proof
kind: route
title: Z_2 of the H-cover of a mapping torus is the phi-invariant part of H_1(N); the explicit invariant cycle pushed to an index-9 cover has two lifts of the P-cell, checked over the Nielsen ball of radius 3
target: c2-rose-mapping-torus-has-no-one-lift-core
requires:
  - two-cell-injective-maps-realize-relative-eg-pairs
  - rank-five-degree-one-two-cell-configuration-is-a-core
  - admissible-ab-nonzero-two-cell-base-exists
artifacts:
  - experiments/c2-mapping-torus-2026-09-18/RESULTS.md
  - experiments/c2-mapping-torus-2026-09-18/verify_cycle.py
  - experiments/c2-mapping-torus-2026-09-18/bases.py
  - experiments/c2-mapping-torus-2026-09-18/srq.g
---

# Proof

Notation is as in the claim. Words use capitals for inverses. Cosets are right cosets `Na`, and
`F_4` acts on `N\F_4` on the right.

## (T0) Canonical-cycle test

Let `X` be an aspherical 2-complex with `π_1 X = G`. The cover `X_H` is aspherical and
2-dimensional, so `B_2 = 0` and `Z_2(X_H) = H_2(X_H) = H_2(H)`.

**Map version.** Let `h: K → X` be a combinatorial map from a 2-dimensional `K(H,1)` that is
injective on 2-cells and induces `H ↪ G`.
- Because `h_*(π_1 K) = H`, the map `h` lifts to `h̃: K → X_H`.
- `h̃` is still injective on 2-cells. Two cells of `K` over the same cell of `X_H` would lie over
  the same cell of `X`.
- `h̃` is a `π_1`-isomorphism between aspherical complexes, so `h̃_*: H_2(K) → H_2(X_H)` is an
  isomorphism.
- A cellular map that sends 2-cells homeomorphically onto distinct 2-cells sends a 2-chain
  `Σ n_e e` to `Σ ±n_e h̃(e)` without cancellation.
- So every cycle of `Z_2(X_H)` is `h̃_*` of a cycle of `K`. Its support is a set of cells `h̃(e)`,
  and these lie over pairwise distinct cells `h(e)` of `X`.

**Subcomplex version.** Let `C ⊂ X_H` be a subcomplex whose inclusion induces `π_1 C ≅ H`.
- By Hopf's theorem, `H_2(C) → H_2(π_1 C)` is onto.
- By naturality, this map factors as `H_2(C) → H_2(X_H) → H_2(H)`, and the second map is an
  isomorphism.
- So `H_2(C) → Z_2(X_H)` is onto, and every cycle of `Z_2(X_H)` is supported in `C`.
- If `C` has at most one lift of each 2-cell, the support injects into the 2-cells of `X`.

This uses no asphericity of `C`.

**Finite covers.** Let `L ⊇ H` have finite index. The covering `X_H → X_L → X` factors the
projection. A chain whose support injects into the cells of `X` pushes forward to `X_L` with at
most one nonzero cell over each cell of `X`, and with the same coefficients. ∎

## (T1) Fibred complexes

Let `f: Γ → Γ` represent `φ`, and let `M_f` have the following cells:
- the vertices and edges of `Γ`;
- one vertical edge `t_v` from `v` to `f(v)` for each vertex `v`;
- one 2-cell `σ_e` for each edge `e`, with boundary `t_{o(e)} · f(e) · t_{τ(e)}^{-1} · e^{-1}`.

For the rose, `σ_e = y e Y φ(e)^{-1}`: `P = ypYQ`, `Q' = yqYR`, `R' = yrYS`, `S' = ysY(rrSqPRs)^{-1}`.

The cover `(M_f)_H` is described as follows.
- `H = N ⋊ ⟨y⟩` with `y ∈ H`, so this cover is the mapping torus of the lift `f_N: Γ_N → Γ_N`.
- On vertices, `f_N(Na) = Nφ(a)`. This is well defined because `φ(N) = N`: the shift `y` lies in
  `H` and preserves `F_4`.
- Its 2-cells are the `σ_ẽ`, one for each edge `ẽ` of `Γ_N`.

The boundary of a 2-chain is
`∂(Σ n_ẽ σ_ẽ) = Σ n_ẽ (f_N#(ẽ) − ẽ) + Σ n_ẽ (t_{o(ẽ)} − t_{τ(ẽ)})`.
- The vertical edges `t_v` are distinct free generators of `C_1`. So the second sum vanishes
  exactly when `n = Σ n_ẽ ẽ` is a 1-cycle of `Γ_N`.
- The first sum then vanishes exactly when `f_N# n = n`.

So `Z_2((M_f)_H) = Z_1(Γ_N)^{f_N} = H_1(N)^φ`. By (T0) this group is `H_2(H)`, and
`H_2(H) ≅ Z` by `rank-five-degree-one-two-cell-configuration-is-a-core`. ∎

## (T2) The cycle for the rose

Take the four loops `ℓ_1 = Q x_2`, `ℓ_2 = X_2 s x_2`, `ℓ_3 = pQ`, `ℓ_4 = qR` at the base vertex `N`.
They lie in `N`:
- `pQ` and `qR` are the fibre parts `y^j e y^{-j-1}` (`j = −2, −1`) of `e = xyX`;
- `X_2 s x_2 = y² c y^{-2}` with `c = XYxyx`;
- `Q x_2 = y^{-1} b y^{-2}` with `b = Xyyyx`.

Let `z` be the 1-chain of `−ℓ_1 + ℓ_2 − 2ℓ_3 − 2ℓ_4` in `Γ_N`. It is a cycle, because it is a sum of
loops. Its letter sums are `(p,q,r,s) = (−1, 0, 1, 1)`.

**Fix edge-lift labels.** The chain `z` lives on edge lifts `ẽ[Na]` that start at vertices `Na`.
Here `a` runs over the 50 reduced prefixes of the eight loops `ℓ_i` and `φ(ℓ_i)`.

**Merge equal cosets.** Two prefixes `a, b` label the same vertex iff `ab^{-1} ∈ N`. The script
merges them only when some `φ^k(ab^{-1})`, `|k| ≤ 3`, lies in the window
`T_8 = ⟨c_3, e_3, e_4, a_0..a_8, b_{-1}..b_8⟩`.
- `T_8 ⊂ N`, because its generators are fibre images of elements of `H`.
- `φ^{±1}(N) = N`.
- So every merge is a true equality of cosets. The resulting partition refines the true one.

**Check invariance.** After merging, the chains `z` and `f_N#(z)` agree. The latter is the chain
of the loops `φ(ℓ_i)`, because `f_N` fixes the base vertex. Pushing forward along the true coset
partition preserves this equality, so `f_N# z = z` exactly.

**Conclusion.** So `z ∈ Z_2((M_f)_H) ≅ Z`.
- The image of `z` in `Z_2(M_f)` is `−P + R' + S'`. This is the generator of
  `H_2(M_f) = H_2(G) ≅ Z`: the integer kernel of the boundary map on `(P, Q', R', S')` is spanned
  by `(−1, 0, 1, 1)`.
- Write `z = k z_0` with `z_0` a generator, and let the image of `z_0` be `d·(S' + R' − P)`. Then
  `kd = 1`, so `z = ±z_0`, and incidentally the pair has degree one.
- After merging, only three vertex classes carry `z`: those of `1`, `s⁻¹` and `q⁻¹`. The explicit
  form of (T2) is the output of `verify_cycle.py`. ∎

## (T3) The classes are distinct

`srq.g` finds a transitive permutation representation of `G` by low-index enumeration, and
`verify_cycle.py` checks it independently:
- `x ↦ (3,4,6,5)(7,8,9)` and `y ↦ (1,2,3)(5,7,8)`;
- the relator `w` acts trivially on `{1,…,9}`;
- the five generators of `H` fix `4`, and `4` is the only point they fix;
- `y x^{-1} y^{-1} x` sends `4 ↦ 2`, so `π(H) = Stab(4) ≅ S_8`.

Let `L = π^{-1}(Stab(4)) ⊇ H`. The vertex `Na` of `Γ_N` maps to the point `4^{π(a)}` of the
index-9 cover. The classes of `1`, `s⁻¹` and `q⁻¹` go to `4`, `2` and `1`, so they are distinct in
`X_L`, and hence in `X_H`. The pushforward is
`z_L = −2P̃_4 + P̃_2 + 2R̃_4 − 2R̃_1 + R̃_2 + 2S̃_1 − S̃_2`.

**Consequence.** By (T0), a realization inside `M_f` needs `z_L` to have at most one nonzero cell
over `P`. It has two. The cell counts in the claim are the numbers of distinct points over
`P`, `R` and `S`. ∎

## (T4) Nielsen neighbours

**Rewriting in a new basis.** Fix a basis `b_j = α(e_j)`. The rose mapping torus in that basis has
its 2-cells indexed by the `b_j`, and (T1) applies unchanged. The 1-cycle `z` in `Γ'_N` is the
chain of the loops `α^{-1}(ℓ_i)`, read in `b`-letters. Its vertices `N·α(prefix)` map to points of
`{1,…,9}` through the same `π`.

**The search.** `bases.py` does the following:
- enumerates bases by breadth-first search over the 24 elementary Nielsen moves `b_a ↦ b_a b_c^{±1}`
  and `b_c^{±1} b_a`;
- keeps `α` and `α^{-1}`, and asserts `α(α^{-1}(e)) = e` at every step;
- pushes `z` to `X_L`;
- rejects a basis if some letter has two nonzero lifts, or some coefficient has absolute value
  other than 1.

Up to depth 3 there are 57,725 distinct bases and none survives. This is a computation over the
listed bases only. It says nothing about roses outside the radius-3 Nielsen ball, about
non-rose marked graphs, or about fibrations of `G` other than the one with fibre `F_4 = ker(x ↦ 1, y ↦ 0)`.
∎

## Reproduction

In `experiments/c2-mapping-torus-2026-09-18/`, run the following.
- `python3 verify_cycle.py ../c2-free-by-cyclic-2026-09-18 8` does (T2) and (T3) in about 2 s.
- `python3 bases.py ../c2-free-by-cyclic-2026-09-18 3` does (T4) in about 20 s.
- `gap -q srq.g` finds the `S_9` representation.
