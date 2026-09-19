---
rg: 2
id: c2-fibred-realizations-reduce-to-a-primitive-class-proof
kind: route
title: The support of the canonical cycle in Gamma_N maps edge-injectively to Gamma, so it splits vertices of a subgraph and carries a free factor system; the index-9 cover sees c_H as primitive with unimodular twisted Fox vector
target: c2-fibred-realizations-reduce-to-a-primitive-class
requires:
  - c2-rose-mapping-torus-has-no-one-lift-core
  - two-cell-injective-maps-realize-relative-eg-pairs
  - rank-five-degree-one-two-cell-configuration-is-a-core
  - admissible-ab-nonzero-two-cell-base-exists
artifacts:
  - experiments/c2-primitive-class-2026-09-19/RESULTS.md
  - experiments/c2-primitive-class-2026-09-19/common.py
  - experiments/c2-primitive-class-2026-09-19/lattice.py
  - experiments/c2-primitive-class-2026-09-19/coker.py
  - experiments/c2-primitive-class-2026-09-19/twisted.py
  - experiments/c2-primitive-class-2026-09-19/whitehead.py
  - experiments/c2-primitive-class-2026-09-19/search.py
  - experiments/c2-primitive-class-2026-09-19/climb.py
---

Notation is that of the claim and of `c2-rose-mapping-torus-has-no-one-lift-core` (the "rose
node"). Its parts (T0) and (T1) are used as stated there.

## (R1) Every marked graph

Let `Γ` be a finite connected graph with a marking `π_1(Γ, ∗) = F_4`. Let `f: Γ → Γ` be a cellular
homotopy equivalence with `f(∗) = ∗` and `f_* = φ`. This is the setting of (T1). A representative
with `f(∗) ≠ ∗` changes `φ` by an inner automorphism and `y` by an element of `F_4`, and the
argument below is unchanged.

**Step 1: the cycle.** Let `p: Γ_N → Γ` be the cover with `p_*π_1(Γ_N, ∗̃) = N`.
- By (T1), `(M_f)_H` is the mapping torus of the lift `f_N`.
- `Z_2((M_f)_H) = Z_1(Γ_N)^{f_N}`, and its generator is a 1-cycle `z` on `Γ_N`.
- A graph has no 1-boundaries, so `Z_1(Γ_N) = H_1(Γ_N) = H_1(N)`, and `z = ±c_H`.
- The 2-cells of `(M_f)_H` in the support of the 2-cycle are the `σ_ẽ` with `ẽ` in the support
  of `z`. The cell `σ_ẽ` lies over `σ_{p(ẽ)}`.

So `M_f` passes exactly when `p` is injective on the edges of the support of `z`.

**Step 2: the support splits vertices.** Assume `M_f` passes.
- Let `S ⊂ Γ_N` be the finite subgraph formed by the edges of the support of `z` and their
  endpoints. Let `S_1, …, S_k` be its components.
- Each `S_i` carries a nonzero cycle `z_i`, with `z = Σ z_i`. Hence `H_1(S_i) ≠ 0`.
- Let `D ⊂ Γ` be `Γ` with the open edges of `p(S)` removed. All vertices of `Γ` are kept.
- Let `Z` be `S ⊔ D` with one new edge `ε_u` from each vertex `u` of `S` to `p(u) ∈ D`.

The new edges form a forest. Each `ε_u` has the end `u` of valence one among new edges, so the
union of the new edges is a disjoint union of stars centred at vertices of `D`. Collapsing them
gives the quotient of `S ⊔ D` that identifies each `u` with `p(u)`.
- Its vertices are those of `Γ`.
- Its edges are those of `D`, together with the edges of `S`. The latter are in bijection with the
  edges of `p(S)` because `p|_S` is edge-injective, and the incidences agree.

So this quotient is `Γ`, and the collapse `c: Z → Γ` is a homotopy equivalence that restricts to
`p` on `S`.

**Step 3: a free factor system inside `N`.**
- Take the base point `o = ∗ ∈ D`, and a maximal tree `T` of `Z` containing maximal trees `T_i` of
  each `S_i`.
- The non-tree edges form a basis of `π_1(Z, o)`.
- Let `γ_i` be the `T`-path from `o` to a vertex `u_i ∈ S_i`. The non-tree edges in `S_i` give a
  basis of `γ_i π_1(S_i, u_i) γ_i^{-1}`, because `T`-paths between vertices of `S_i` stay in `T_i`.
- Hence `*_i γ_i π_1(S_i,u_i) γ_i^{-1}` is a free factor of `π_1(Z, o)`. Applying `c_*` gives a free
  factor of `F_4`.

Now move into `N`.
- Let `β_i` be a path in `Γ_N` from `∗̃` to `u_i`.
- Put `A_i = p(β_i) · p_*π_1(S_i, u_i) · p(β_i)^{-1}`. Then `A_i ≤ N` is finitely generated and
  nontrivial.
- Put `g_i = c(γ_i) p(β_i)^{-1} ∈ π_1(Γ, ∗) = F_4`. Then `g_i A_i g_i^{-1} = c_*(γ_i π_1(S_i) γ_i^{-1})`.
- So the `g_i A_i g_i^{-1}` generate their free product, and it is a free factor of `F_4`.

`H_1(A_i) = H_1(S_i)`, and the map to `H_1(N) = H_1(Γ_N)` is induced by `S_i ⊂ Γ_N`. Conjugation by
`β_i` does not change classes. So `c_H = ±Σ z_i` is in the image of `⊕ H_1(A_i)`, which is `(P_k)`.

The free factor has rank at least `k`, so `k ≤ 4`. ∎

**Remark.** For the standard rose, the support found in (T2) of the rose node has two components.
One is `{N, NS, Np}` and the other is the vertex `NQ` with its two loops. So `k ≥ 2` does occur,
although the standard rose fails anyway.

## (R2) `(P_1)` is `(P)`

`(P) ⇒ (P_1)`: take `A_1 = ⟨q⟩` and `g_1 = 1`.

`(P_1) ⇒ (P)`:
- `A = A_1` is finitely generated, and `gAg^{-1}` is a free factor of `F_4`. So `H_1(A) → H_1(F_4)` is
  split injective. Conjugation acts trivially on `H_1(F_4)`.
- Let `a ∈ H_1(A)` map to `c_H`. Its image in `H_1(F_4)` is `±v`, which is primitive, so `a` is
  primitive in `H_1(A)`.
- `Aut(A) → GL(H_1(A))` is onto, because Nielsen moves realise the elementary matrices and the sign
  changes. So `a` is the class of a basis element `q` of `A`.
- `q ∈ N`, and its class in `H_1(N)` is the image of `a`, which is `c_H`.
- `gqg^{-1}` is a basis element of the free factor `gAg^{-1}`, so it is primitive in `F_4`. Hence
  `q` is primitive in `F_4`. ∎

## (R3) Roses

(⇒) This is (R1) with `k = 1`, followed by (R2).

(⇐) Let `q ∈ N` be primitive with `[q] = c_H`. Extend it to a basis `(q, b_2, b_3, b_4)` of `F_4`, and
let `f` be the rose map of `φ` in this basis.
- The `q`-petal lifts to a loop `ℓ` at `∗̃` in `Γ_N`, because `q ∈ N`.
- The 1-cycle `ℓ` has class `[q] = c_H`. Since `Z_1 = H_1` on a graph, `ℓ` is the canonical cycle.
- Its support is one edge, so `M_f` passes, with connected support. ∎

A passing rose still needs a subcomplex `C ⊂ (M_f)_H` with `π_1 C ≅ H` and one lift per 2-cell.
Such a `C` contains the loop `ℓ` and the cell `σ_ℓ`, so passing is only the first obstruction.

## (R4) Every fibration

Let `χ: G → Z` be primitive, with kernel `F_χ` free of finite rank. Put `(a, b) = (χ(x), χ(y))`, so
that `gcd(a, b) = 1`.

**χ(H) = Z.** The generators `XyxYx, Xyyyx, XYxyx, y, xyX` of `H` have `χ`-values `a, 3b, a, b, b`,
whose gcd is 1.

**Set-up.** Pick `t_χ ∈ H` with `χ(t_χ) = 1`. Then:
- `G = F_χ ⋊ ⟨t_χ⟩` and `H = N_χ ⋊ ⟨t_χ⟩`;
- `φ_χ = (conjugation by t_χ)` preserves `N_χ`;
- for any representative `f` of `φ_χ` on a marked graph for `F_χ`, `M_f` is a 2-dimensional
  `K(G,1)`.

(T0) and (T1) of the rose node use only these facts, so `Z_2((M_f)_H) = H_1(N_χ)^{φ_χ} = H_2(H) ≅ Z`.
(R1) and (R3) then go through word for word, with `F_χ` and `N_χ` in place of `F_4` and `N`.

**Primitivity.** (R2) also needs the image of `c_H^χ` in `H_1(F_χ)` to be primitive.
- Apply (T1) with `H` replaced by `G`. This gives `H_2(G) = H_1(F_χ)^{φ_χ}`, and the map
  `H_2(H) → H_2(G)` is the map `H_1(N_χ)^{φ_χ} → H_1(F_χ)^{φ_χ}`.
- By (T2) of the rose node, the pair has degree one, so this map is an isomorphism. Hence the image
  of `c_H^χ` generates `H_1(F_χ)^{φ_χ}`.
- A fixed sublattice is saturated: if `m u` is fixed with `m ≠ 0`, then `u` is fixed. So the
  generator is primitive in `H_1(F_χ)`.

For `χ = (0, 1)` this recovers `v = (−1, 0, 1, 1)`. ∎

## (R5) Finite covers

**Lemma B.** Let `J ≤ F_4` contain `q`, with `q` primitive in `F_4`. Then `q` is primitive in `J`.

*Proof.* Write `F_4 = ⟨q⟩ * C`. By the Kurosh subgroup theorem, `J` is the free product of three
kinds of factor:
- a free group;
- the groups `J ∩ g⟨q⟩g^{-1}`, one for each double coset `J g ⟨q⟩`, with any choice of
  representatives;
- the groups `J ∩ hCh^{-1}`.

Choose `g = 1` as the representative of its double coset. It contributes the factor
`J ∩ ⟨q⟩ = ⟨q⟩`. ∎

**Consequences.** Let `N ≤ J` with `J` of finite index, let `(x_j)` be a basis of `J`, and let
`ρ: J → Z = ⟨t⟩` kill `N`.

1. The map `N → Z[t^{±1}]^m`, `n ↦ (ρ(∂n/∂x_j))_j`, is a homomorphism that kills `[N, N]`. This is
   because `ρ(∂(nn')/∂x) = ρ(∂n/∂x) + ρ(n)ρ(∂n'/∂x)` and `ρ(n) = 1`. So it defines the twisted Fox
   vector `c(t)` of any class in `H_1(N)`.
2. If `q ∈ N` is primitive in `F_4`, then Lemma B gives a basis `(q, y_2, …)` of `J`.
   - The Jacobian `(∂y_k/∂x_j)` is invertible over `Z[J]`, with inverse `(∂x_j/∂y_k)`.
   - Its first row is the Fox vector of `q`.
   - So `ρ` of that row is unimodular over `Z[t^{±1}]`, and the image of `[q]` in `H_1(J)` is
     primitive.

**The index-9 computation.** Take `L` to be the stabiliser of the point 4 under
`x ↦ (3,4,6,5)(7,8,9)`, `y ↦ (1,2,3)(5,7,8)`, and `J = L ∩ F_4`, which has rank 28. `coker.py`
computes the following:
- the `φ^{±1}`-closure of the classes of `a_0, b_0, c_0, e_0` in `H_1(J)`, which is `im H_1(N)`
  (rank 27);
- the Smith form of `H_1(J)/im H_1(N)`, which is `Z`;
- that the image of `c_H` lies in this lattice and has a coordinate equal to 1, so it is primitive.

`twisted.py` takes the unique primitive `ρ` (up to sign) that kills `N`. The twisted Fox vector of
`c_H` is constant, with entries `−2, 2, 1, −1, 2` on the generators `(1,r), (1,s), (2,r), (2,s),
(4,r)` of `J`. It is unimodular.

So every condition that (P) imposes on `J` through Lemma B holds. In particular, the least
`ℓ^1`-norm of the image of `c_H` over all bases of `J` is 1. The "two lifts of the P-cell"
certificate of the rose node depends on the basis, and it cannot be promoted to an
`Aut(F_4)`-invariant norm at this index. ∎

## (R6) Search

**The decomposition.** In `Γ_N` for the standard rose, the canonical cycle of (T2) is the sum of
the edge loops `2·F_2 + 2·F_3 + F_1`:
- `F_1 = SpSrs`: the edges `S[S]`, `R[S]`, `P[S]`;
- `F_2 = rP`: the edges `R[1]`, `P[1]`;
- `F_3 = QsRq`: the loops `S[Q]`, `R[Q]` at `NQ`.

All three words lie in `N`.
- They are closed paths at `N` in the vertex-merged graph of `verify_cycle.py` of the rose node,
  whose merges are proved equalities of cosets. This uses `NSp = N`, `NSr = NS`, `Nr = Np`, `NQs = NQ` and `NQR = NQ`.
- `F_3` also crosses the `q`-edge from `NQ` to `N` once in each direction, and that edge is not in
  the support.
- The chain identity `z = 2F_2 + 2F_3 + F_1` holds in the merged graph, and so in `Γ_N`.

As a finite shadow, `search.py check` verifies that they fix
the point 4 and that their classes add up to that of `c_H` in `H_1(J)`. Each of `F_1, F_2, F_3` is
primitive in `F_4`, but `c_H` is not a single one of them.

**The searches.**
- `search.py 0` tests every ordering of the product `F_1 F_2 F_2 F_3 F_3`.
- `search.py 2 20000` inserts random `N`-conjugators of length at most 2.
- `climb.py` hill-climbs in the coset `q_0[N, N]` by multiplying by commutators of short
  `N`-words, and scores each word by its Whitehead-minimal cyclic length.

The results are in `RESULTS.md`. No primitive element was found. This is evidence only, and it
leaves (P) open.
