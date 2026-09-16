---
rg: 2
id: infinite-non-wedge-from-a-multiplying-chain-gadget
kind: route
title: "Reduction: translate a multiplying chain gadget to infinity, so second homology gains a nonzero element divisible by every power of m"
target: some-infinite-planar-set-has-a-non-wedge-rips-complex
requires:
  - some-planar-rips-chain-gadget-multiplies-a-sphere-class
artifacts:
  - research/artifacts/zaremsky-4-02-planar-rips-infinite-2026-09-16.md
---

Assume a gadget `(G, r, τ, A, z, m)` satisfying (G0)–(G4) of
`some-planar-rips-chain-gadget-multiplies-a-sphere-class`. Put
`X = ∪_{k ≥ 0} τ^k(G)`, `G_k = τ^k(G)` and `L_k = τ^k(G ∖ B)`. Full details are
in §3 (D1–D6) of
`research/artifacts/zaremsky-4-02-planar-rips-infinite-2026-09-16.md`.

**Step 1: separation and levels.**

- Translating (G2) by `τ^j` gives lemma (S). If `x ∈ L_j`, `y ∈ G_k` with
  `k > j`, and `|x − y| ≤ r`, then `k = j + 1` and `y ∈ τ^j(B)`.
- By (G1), `A ⊆ G ∖ B`, so `τ^k(B) = τ^{k+1}(A) ⊆ L_{k+1}`. So
  `G_k ⊆ L_k ∪ L_{k+1}`.
- The levels are pairwise disjoint: apply (S) to a common point, at distance
  `0` from itself.
- Hence `G_j ∩ G_k = ∅` for `|j − k| ≥ 2` and `G_j ∩ G_{j+1} = τ^j(B)`.
- `X` is infinite, since the `L_k ⊇ τ^k(A)` are nonempty and disjoint.

**Step 2: every simplex lies in one copy.**

- For a simplex `σ`, let `j` be the least level that `σ` meets. By (S), every
  vertex of `σ` lies in `L_j ∪ τ^j(B) = G_j`.
- So `Y_N = ∪_{k ≤ N} R(G_k)` is the full subcomplex on `∪_{k ≤ N} G_k`, and
  `Y_N ∩ R(G_{N+1}) = R(τ^{N+1}(A))`.
- `R(X) = ∪_N Y_N` is connected by (G0), since consecutive copies meet.

**Step 3: divisibility.**

- The translation `τ^k : R(G) → R(G_k)` is a simplicial isomorphism. It carries
  (G4) to the relation "image of `τ^k_* z` equals `m ·` image of
  `τ^{k+1}_* z`" in `H_2(R(G_k))`.
- Pushing forward, the images `α_k ∈ H_2(R(X))` satisfy `α_k = m α_{k+1}`. So
  `α_0 = m^k α_k` for every `k`.

**Step 4: non-vanishing.** Build compatible `φ_N : H_2(Y_N) → Q` with
`φ_0(a) = 1`. The start uses that `a` has infinite order, by (G4), and that
`Q` is injective. For the step:

1. Mayer–Vietoris for `Y_{N+1} = Y_N ∪ R(G_{N+1})`, with intersection
   `C = R(τ^{N+1}A)`, gives
   `H_2(C) → H_2(Y_N) ⊕ H_2(R(G_{N+1})) → H_2(Y_{N+1})`.
2. By (G3) the kernel of `H_2(C) → H_2(R(G_{N+1}))` is torsion, and `φ_N`
   kills torsion.
3. So `ψ(i′_* c) = φ_N(i_* c)` is well defined on the image of `H_2(C)`, and
   extends to `H_2(R(G_{N+1}))`.
4. `φ_N + ψ` vanishes on the image of `H_2(C)`, which is the kernel of the
   map into `H_2(Y_{N+1})`. So it descends to the image in `H_2(Y_{N+1})`, and
   extends to all of `H_2(Y_{N+1})`.
5. The result `φ_{N+1}` restricts to `φ_N`.

Since `H_2(R(X)) = colim_N H_2(Y_N)`, the `φ_N` give `φ` with `φ(α_0) = 1`,
so `α_0 ≠ 0`.

**Step 5: conclusion.**

- In a free abelian group, an element divisible by `m^k` for all `k`, with
  `|m| ≥ 2`, is zero. So `H_2(R_r(X); Z)` is not free.
- A connected wedge of spheres has free integral homology. So `R_r(X)` is a
  connected complex not homotopy equivalent to a wedge of spheres.

**Strict convention.** Only finitely many distances of `X` lie in `[0, r + 1]`,
since `|x − y + kv| → ∞` as `|k| → ∞`. So `R_{<r+ε}(X) = R_{≤ r}(X)` for small
`ε > 0`, and the conclusion holds in both conventions. ∎
