---
rg: 2
id: c2-split-rose-passes-cycle-test-fails-gluing-rank-proof
kind: route
title: An explicit rank-3 free factor carries c_H, so the split-basis rose passes the canonical-cycle test. For any 2-cell-injective map from a K(H,1), K^1 has rank 1 - chi(H) + F, and the support cells must glue along zero-sum edge blocks. For the split rose the unique gluing of rank 7 leaves the d-cell open
target: c2-split-rose-passes-cycle-test-fails-gluing-rank
requires:
  - c2-fibred-realizations-reduce-to-a-primitive-class
  - c2-rose-mapping-torus-has-no-one-lift-core
  - two-cell-injective-maps-realize-relative-eg-pairs
  - rank-five-degree-one-two-cell-configuration-is-a-core
artifacts:
  - experiments/c2-split-rose-2026-09-19/RESULTS.md
  - experiments/c2-split-rose-2026-09-19/nlib.py
  - experiments/c2-split-rose-2026-09-19/pcheck.py
  - experiments/c2-split-rose-2026-09-19/closure.py
  - experiments/c2-split-rose-2026-09-19/cplx.py
  - experiments/c2-split-rose-2026-09-19/minrank.py
  - experiments/c2-split-rose-2026-09-19/dcell.py
  - experiments/c2-split-rose-2026-09-19/family.py
---

# Proof

Notation is as in the claim. Capitals denote inverses, and cosets are right cosets `Nu`.

## (S1)

**Basis.** In `B`-letters, `p = Bcba`, `q = d`, `r = cba` and `s = ccba`. Substitute these into
`a = pSr`, `b = rP`, `c = sR` and `d = q`. Each returns its own letter, and the substitution back
also returns `p, q, r, s`, as the assertions in `nlib.py` check. So `B` is a basis of `F_4`, and
`⟨a,b,c⟩` is a free factor.

**Memberships and the identity.** `pcheck.py` does this.
- It applies `φ` to `U`, `F_1`, `F_2` and `F_3`. Here `U` is the word of `c_H` from (T2) of the
  rose node.
- It finds all four images in the Stallings graph of the window `T_8`.
- It compares edge-count vectors there, and finds `[φU] = [φF_1] + 2[φF_2] + 2[φF_3]` in
  `H_1(T_8)`.

`T_8 ⊂ N` and `φ(N) = N`, so `F_i ∈ N`. The map `H_1(T_8) → H_1(N)` then gives
`φ_*[U] = φ_*([F_1] + 2[F_2] + 2[F_3])` in `H_1(N)`. Since `φ_*` is an automorphism of `H_1(N)`, the
identity holds. The conjugators `s`, `1` and `q` put `F_1`, `F_2`, `F_3` into
`s⁻¹⟨a⟩s`, `⟨b⟩` and `q⁻¹⟨c⟩q`. So `(P_3)` holds with `A_1 = ⟨F_1⟩`, `A_2 = ⟨F_2⟩`, `A_3 = ⟨F_3⟩`
and `g_i = s, 1, q`. ∎

## (S2)

Use (T1) of the rose node in the basis `B`.
- `Z_2((M_f)_H)` is the group of `f_N`-invariant 1-cycles of `Γ_N`.
- The generator corresponds to `c_H`, which is `[F_1] + 2[F_2] + 2[F_3]` by (S1).

Read the loops in `B`-letters.
- `F_1` is the path `s⁻¹`, then the edge `a`, then `s`. As a 1-chain the two copies of the path cancel,
  so the chain is the single `a`-edge at `N s⁻¹`.
- Likewise `F_3` gives the `c`-edge at `N q⁻¹`.
- `F_2 = b` is the `b`-edge at `N`.

The canonical cycle is therefore `σ_a[Ns⁻¹] + 2σ_b[N] + 2σ_c[Nq⁻¹]`.
- Its support has one cell over each of `σ_a`, `σ_b` and `σ_c`, so `M_f` passes.
- Pushing forward to any finite cover keeps one cell over each of these, so no finite-cover certificate
  of (T0) type exists.
- Nothing in this argument uses `d`, so it holds for every basis `(a,b,c,d')`.

The boundary sums computed in `minrank.py` confirm independently that the chain is a cycle. ∎

## (S3)

**Finiteness.** Let `h: K → X` be as in the claim, with `K` a possibly infinite 2-dimensional `K(H,1)`.
It has at most `F_X` 2-cells.
- Let `Y ⊂ K^{(1)}` be a finite connected subgraph that contains all cell boundaries and loops for a
  finite generating set of `H`.
- `π_1 K^{(1)} = π_1 Y * F'`, and the relators lie in `π_1 Y`. So `π_1 K = π_1(Y ∪ cells) * F'`.
- The first factor already surjects onto `π_1 K`, so `F' = 1`. Then `K^{(1)}` is `Y` with trees
  attached, and `K_0 = Y ∪ cells` is a finite `K(H,1)` with the same map.
- So assume `K` is finite.

**Rank.** `χ(K) = χ(H)`, so `rank K^{(1)} = 1 − χ(K^{(1)}) = 1 − χ(H) + F`.

**The cycle in `K`.** By the map version of (T0), `h̃_*: H_2(K) → Z_2(X_H)` is an isomorphism, and
the generator `z` is `h̃_*` of a cycle `z_K`.
- `h̃` is injective on 2-cells and preserves boundary words. So `z_K = Σ n_κ κ`, where `κ` runs over
  the cells of `K` over the support cells, `n_κ` are the coefficients of `z`, and each cell is
  oriented compatibly.
- `∂z_K = 0` in `C_1(K)`. Each `K`-edge `ε` lies over one edge `h̃(ε)` of `X_H`, and its coefficient
  in `∂z_K` is the sum of the signed coefficients of the boundary positions it occupies.
- So the occurrences of each `X_H`-edge in `∂z` are partitioned into blocks, the fibres of `h̃` on
  `D`, and each block has total zero.
- `D^{(1)}` is the quotient of the disjoint boundary circles in which the positions of one block are
  identified as one edge. Their origins are identified, and so are their ends.
- Further identifications of vertices can only add rank within a component, and they merge
  components without changing the total rank.
- `D^{(1)}` is a subgraph of `K^{(1)}`, so `rank D^{(1)} ≤ rank K^{(1)}`.

**Equality.** Suppose `rank D^{(1)} = rank K^{(1)}` and `D^{(1)}` is connected.
- Then `K^{(1)}/D^{(1)}` is a tree, so `K^{(1)}` is `D^{(1)}` with trees hanging at single vertices.
- The boundary of a cell of `X_H` is a cyclically reduced edge path, so the boundary of any cell of
  `K` is too. A backtrack in `K` would map to a backtrack in `X_H`.
- A cyclically reduced closed path in `D^{(1)} ∪ trees` stays in `D^{(1)}`. ∎

## (S4)

`cplx.py` builds `C_0`, the union of the closures of `σ_a[Ns⁻¹]`, `σ_b[N]` and `σ_c[Nq⁻¹]` in
`(M_f)_H`.
- It has 6 vertex classes. Every pair among the 41 reduced prefixes involved is decided: merged by
  some `φ^k(uv⁻¹) ∈ T_8` with `|k| ≤ 4`, or separated by the `S_9` cover. A pair of neither kind
  would raise an error, and none occurs.
- It has 16 edges and 3 cells. The boundary lengths are 20, 8 and 15.

`minrank.py` lists all block partitions.
- Edges with two occurrences `(+n, −n)` allow one block.
- `h_2c` has `(+1, +1, −2)` and allows one block.
- The five edges `h_0b, h_0c, h_3a, h_3c, h_4b` have four occurrences each, and allow 3, 3, 2, 2, 2
  partitions.
- That makes 72 partitions in total.

For each partition it computes `E − V + #components` of the forced quotient.
- The least value is 7, attained by one partition only, with 21 edges, 15 vertices and 1 component.
- `1 − χ(H) + F ≤ 3 + 4 = 7`, so equality holds.
- A `K` with `F = 3` would have `rank K^{(1)} = 6 < 7`, so it is impossible, and `K` must contain a
  cell over some `σ_d[v]`.
- By (S3.3) that cell's boundary is a closed path in this `D^{(1)}`, and so it lies over a boundary
  inside `C_0`.

Only one `σ_d[v]` has its boundary inside `C_0`.
- Its `d`-edge must be `h_0d` or `h_2d`, and it needs the vertical edges at both ends of that edge.
- The vertical edges of `C_0` are `t_0`, `t_1` and `t_2`, and `h_0d` ends at class 5, which has no
  vertical edge.
- So `v` is class 2, which is `Nq⁻¹`.

`dcell.py` tries every start vertex of `D^{(1)}` and every choice of `K`-edge over each boundary edge.
- The path `t_2, h_3c, h_4b, h_3a` is forced through the `c`-cell copies.
- It ends at the `D`-vertex that is the origin of the unique `K`-edge over `t_0`.
- The next step needs the end of that edge. The edge over `t_0` is not a loop in `D` (7 → 11), so no
  closed lift exists.
- Hence no `K` exists. ∎

## (S5)

`family.py` sets `d' = w_1 q w_2`. It recomputes `φ` in the basis `(a,b,c,d')` and moves the
`c`-support vertex to `N q⁻¹`, rewritten in the new letters. It then reruns (S3)/(S4).
- The result is 42 exclusions, all with least rank 7.
- The 7 bases with `w_2 = a` stop at a coset pair that neither the windows `T_8, T_12, T_16`
  (with `φ`-powers up to 8) nor the `S_9` cover decide.
- These are the bases listed in `RESULTS.md` and no others. ∎
