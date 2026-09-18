---
rg: 2
id: linear-gate-class-is-product-closed-over-tree-powers
kind: claim
title: The linear gate needs only a simple host, so the Bernoulli algebra over Γ replaces R_Γ, and the Track B scaffold may be any F_2^k; the inputs passing form a class closed under subgroups and direct products that contains every Z^n, Thompson's V and L^x, and the monomial status of Z^n over a fixed X is exactly the existence of a regular map Z^n → X
requires:
  - linear-gate-u-reduces-to-algebraic-uniform-roe-embeddings
  - lamplighter-canonical-algebra-embeds-in-leavitt-tensor-square
  - non-amenable-scaffolds-absorb-the-leavitt-factor
distinct_from:
  canonical-algebras-embed-in-algebraic-uniform-roe-algebras: that asks the one-tree gate for the Kazhdan-canonical algebras R_Γ; this shows the gate needs no Kazhdan input, replaces R_Γ by the Bernoulli algebra B_Γ, lets the number of tree factors depend on the input, and identifies a product-closed class that passes.
  lamplighter-canonical-algebra-embeds-in-leavitt-tensor-square: that proves the tree case of the abelian monomial obstruction by separation; Theorem 3 here is the exact criterion over any Cayley graph (a regular map Z^n → X), with a limit argument.
---

**ESTABLISHED** (lane proof, bh-algebra; elementary given the cited results; not reviewed; no priority claimed).
Recalled, not re-read: Farrell–Jones with coefficients in additive categories holds for CAT(0) groups (Bartels–Lück
2012; Wegner 2012).

Throughout, **the linear gate over `P` holds for `Γ`** if `Γ ≤ GL_n(S)` for some finitely generated, recursively
presented, simple `F_2`-algebra `S`, and `S` embeds unitally in a coarsely dense diagonal corner of
`M_m(K_u(P))`. By Theorem A of `linear-gate-u-reduces-to-algebraic-uniform-roe-embeddings`, this puts `Γ` into
`GL(LC(W) ⋊ P)` with `W` effectively closed and free, faithfully on every minimal subsystem. That is the input
M1 and G2 need.

## Theorem 1 (a simple host is enough: Bernoulli algebras)

For infinite finitely generated `Γ` put `B_Γ = LC(2^Γ, F_2) ⋊ (Z/2 ≀ Γ) ≅ M_2(F_2)^(⊗Γ) ⋊ Γ`.
1. `B_Γ` is simple with centre `F_2`. The groupoid is minimal, since finite flips make orbits dense. It is
   effective: a nonzero flip moves every point, and a shift `γ ≠ e` acts freely on coordinates, so it moves a
   point of every cylinder.
2. `B_Γ` has solvable word problem when `Γ` does, and `γ ↦ u_γ` embeds `Γ` in `B_Γ^x`.
3. So the linear gate for `Γ` over `P` follows from an embedding of `B_Γ` alone. The half-line overgroup and
   `H_Γ = EL_3(R_Γ)` are needed only for the Kazhdan filter of host classes, not for gate U.
4. In particular `B_Z = R_1` embeds in `L ⊗ L ⊆ K_u(F_2 × F_2)`
   (`lamplighter-canonical-algebra-embeds-in-leavitt-tensor-square`). So `Z` passes over `F_2 × F_2` through the
   bilateral shift, and the test "`R_Z`, containing `K[Z^n]` for every `n`" was an artifact of the overgroup.

## Theorem 2 (the scaffold may grow with the input; the passing class is product-closed)

1. **Every `F_2^k` is admissible.** Let `P = F_2^k × Z²` for any `k`. It is finitely presented, torsion-free and
   CAT(0), so Farrell–Jones with coefficients holds. Hence the K-gate of Track B
   (`farrell-jones-groups-acting-freely-have-k-trivial-leavitt-hosts`) and the finite-presentation input of the
   ring side hold for every `k`. No new Farrell–Jones case is needed when `k` depends on `Γ`.
2. **The class.** Let `𝒢` be the class of `Γ` passing the linear gate over `F_2^k` for some `k`. Then `𝒢` is
   closed under:
   - subgroups (trivially);
   - finite direct products. If `Γ_i ≤ GL_(n_i)(S_i)` and `S_i ⊆ K_u(F_2^(k_i))`, then `S_1 ⊗ S_2` is simple,
     since both are simple with centre `F_2`. Also `(g_1, g_2) ↦ g_1 ⊗ g_2` is injective, since
     `g_1 ⊗ g_2 = 1` forces scalar factors, which are `1` over `F_2`. Finally
     `K_u(X) ⊗ K_u(Y) ⊆ K_u(X × Y)`, with products of coarsely dense corners coarsely dense.
3. **Members.**
   - Finite groups: `M_n(F_2) ⊆ K_u(F_2)` unitally, since `F_2 × [n] ≅ F_2` by a bounded bijection.
   - `Z`, by Theorem 1, and hence every `Z^n`, since `Z^n ≤ GL_1(R_1^(⊗n))` and `R_1^(⊗n) ⊆ K_u(F_2^(2n))`.
   - Every finitely generated subgroup of `GL_n(L^(⊗j))` for some `j`, with host `L^(⊗j) ⊆ K_u(F_2^j)`. This
     includes Thompson's `V`, `L^x`, and linear groups over free algebras.
   - Products of all of these.

## Theorem 3 (the abelian monomial test is coarse geometry)

Let `X` be a Cayley graph of a finitely generated group and `K` a field. Then `K[Z^n]` has a faithful module
over `X` that is monomial for the standard generators iff `Z^n` admits a regular map into `X`, that is, a
Lipschitz map with bounded fibres.

*Proof.*
1. (⇐) The free orbit module: basis `Z^n`, placed by the regular map.
2. (⇒) As in Theorem 2 of the required lamplighter node: every orbit has a stabilizer `H`, and the Schreier
   graph of `Z^n/H` contains an embedded grid ball of radius `(r(H) − 1)/2`.
3. If `r(H) ≤ C` on every orbit, the product of the binomials `z^h − 1` over `0 < |h| ≤ C` kills the module. So
   for every `C` there are uniformly regular maps `B_(Z^n)(C) → X`.
4. Translate each so that `0 ↦ e`. By local finiteness a diagonal subsequence converges on every finite set,
   and the limit `Z^n → X` is Lipschitz with the same fibre bound. ∎

**Consequences.**
- Over a tree, no `n ≥ 2` passes monomially.
- Over `F_2^k`, `Z^n` passes monomially for `n ≤ k`, through a product of lines.
- For a *fixed* `F_2 × F_2` and `n ≥ 3`, the monomial status of `Z^n` is exactly whether `Z^n` maps
  regularly into `T × T`. We did not find this decided in the sources read, though Hume–Mackay–Tessera
  (arXiv:2303.01969) obstruct `T_3^n → T_3^(n−1) × Y`.
- Theorem 2 makes the fixed-scaffold question unnecessary for Boone–Higman.

## What is left of gate U

Linear gate U for all decidable `Γ` holds iff every decidable `Γ` lies in `𝒢`. The next test cases are:
- `B_(F_2)` and `B_Γ` for hyperbolic `Γ`, where no finite tensor power of `L` is known to contain them;
- decidable non-exact `Γ`, for which the C*-analogue fails over every `F_2^k`, since `C*_u(F_2^k)` is nuclear
  (`linear-gate-u-reduces-to-algebraic-uniform-roe-embeddings`, Theorem C).

## Lesson for general BH

Gate U never needed Kazhdan inputs or a fixed scaffold.
- Only simplicity is used, so the Bernoulli algebra of the input replaces the half-line construction.
- Farrell–Jones is known for every product of trees, so the number of tree factors may grow with the input.

The inputs that pass then form a class closed under products and subgroups, generated so far by the bilateral
shift (`Z ⊆ R_1 ⊆ L ⊗ L`) and by Leavitt tensor powers. The obstruction side is now an honest dichotomy:
- **coarse geometry, monomially:** regular maps of the input's lamplighter into powers of trees;
- **exactness, linearly.**
