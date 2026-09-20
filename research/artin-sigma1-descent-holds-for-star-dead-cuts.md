---
rg: 2
id: artin-sigma1-descent-holds-for-star-dead-cuts
kind: claim
title: "Level descent for star dead cuts: if one vertex lies on every dead edge between distinct living blocks, the Novikov dead-cut Laplacian is onto only if the level-0 Laplacian is onto (given a conjugation-stability condition on the dead-vertex relations)"
distinct_from:
  artin-sigma1-dead-edge-ring-obstruction: that is a sufficient condition for non-membership via ring witnesses; this proves that on star cuts the exact Novikov condition descends to the level-0 group-ring condition, so any non-membership is a failure of a Z[H]-ideal identity
  artin-2x2-dead-joins-sigma1-iff-k-q-odd-family: that decides one family whose crossing dead edges form a 4-cycle (no common vertex); this treats every graph whose crossing dead edges share a vertex, with any number of blocks
  artin-sigma1-conjecture-known-families: those are graph families where the living-subgraph formula holds; this is a class, defined by the shape of the dead cut, where the corrected level-0 formula holds
  zaremsky-1-06-bns-invariant-of-every-artin-group: that is the whole problem; this settles the Novikov-to-level-0 descent step on star cuts
---

**ESTABLISHED** by `artin-sigma1-descent-holds-for-star-dead-cuts-proof` (direct proof,
unreviewed; the level-telescoping identity is randomly cross-checked in
`experiments/artin-star-cut-descent-2026-09-17/telescope_check.py`).

**Setting.** This is the notation of the dead-cut Laplacian from the held wave-17 node
`artin-sigma1-equals-dead-cut-laplacian-surjectivity`. That node is not in this tree, so
everything needed is restated here.
- `Γ` is a finite labelled simplicial graph and `G = A_Γ`.
- `χ : G -> Z` is nonzero with image `Z` (rescale if needed), `H = ker χ`, and
  `N = N_χ` is the Novikov ring: formal sums `Σ n_g g` that are finite below every level.
- A vertex `v` is living if `χ(v) ≠ 0` and dead otherwise.
- A dead edge is an edge `{p,q}` with label `2k >= 4` between living vertices with
  `χ(p) + χ(q) = 0`. We always name its ends so that `χ(p) > 0`.
- `Liv^χ` is the graph on the living vertices whose edges are the living edges that are not
  dead. `B_1, ..., B_r` are its components, `[x]` is the block of `x`, and
  `K_r(R) = {x ∈ R^r : Σ x_i = 0}`.
- Every dead vertex `w` has a fixed living neighbour `u(w)`, and `S_k(z) = 1 + z + ... + z^{k-1}`.
- The relations `ρ`, their Novikov generators `g_ρ ∈ N`, their level-0 generators
  `σ_ρ ∈ Z[H]` and their vectors `f_ρ = e_{a(ρ)} - e_{b(ρ)}` are:

| type | edge | `g_ρ` | `σ_ρ` | `f_ρ` joins |
|---|---|---|---|---|
| D | dead edge `{p,q}`, label `2k` | `S_k(pq)(p - 1)` | `S_k(pq)` | `[p]`, `[q]` |
| V | `{w,x}`, `w` dead, `x` living | `w - 1` | `w - 1` | `[x]`, `[u(w)]` |
| W | `{w,x}`, both dead | `(∂r_{wx}/∂w)(w - 1)` | same | `[u(w)]`, `[u(x)]` |

- `L_χ : N^{Rel} -> K_r(N)` sends the basis vector of `ρ` to `g_ρ f_ρ`. The level-0
  Laplacian `L_0 : Z[H]^{Rel} -> K_r(Z[H])` sends it to `σ_ρ f_ρ`.
- The level-0 spans are `M_D = Σ_{ρ ∈ D} Z[H] σ_ρ f_ρ` and
  `M_VW = Σ_{ρ ∈ V ∪ W} Z[H] σ_ρ f_ρ`, so `im L_0 = M_D + M_VW`. For `g ∈ G`,
  `g^{-1} M g` means entrywise conjugation, which is again a left `Z[H]`-submodule.

**Star cut.** The cut is a *star at `v`* if `v` is a living vertex that lies on every dead
edge `{p,q}` with `[p] ≠ [q]`. Put `u = v` if `χ(v) > 0` and `u = v^{-1}` if `χ(v) < 0`.

**Theorem.** Suppose the cut is a star at `v`.
1. **(Unconditional descent.)** If `L_χ` is onto, then
   `K_r(Z[H]) = M_D + Σ_{m >= 0} u^{-m} M_VW u^m`.
2. **(Descent.)** Suppose also that **(Stab)** holds: `u^{-m} M_VW u^m ⊆ M_D + M_VW` for all
   `m >= 1`. Then `L_χ` onto implies `L_0` onto.
3. **(Stab holds in particular)** in these cases:
   - there are no dead vertices;
   - more generally, every V and W vector `σ_ρ f_ρ` is zero for the chosen anchors;
   - every dead vertex `w` is joined to `v` by an edge of label 2. Then `u` commutes with
     every `σ_ρ`, `ρ ∈ V ∪ W`, and `M_VW` is fixed pointwise.
4. **(Explicit form without V/W.)** Suppose `M_VW = 0` and `v ∈ B_1`. For `j >= 2` let
   `I_j = Σ Z[H] S_k(pq)`, summed over the dead edges `{p,q}` from `v` into `B_j`. Then
   `L_0` is onto iff `I_j = Z[H]` for every `j >= 2`. A necessary condition is that for each
   `j >= 2` the halves `k` of the dead edges from `v` into `B_j` have greatest common
   divisor 1, by augmentation.

**Reading for Problem 1.6.**
- The held wave-17 criterion says `[χ] ∈ Σ^1` iff `χ` is dominant and `L_χ` is onto. Its
  part 3 says that `L_0` onto implies `L_χ` onto.
- Combined with parts 2 and 3 here: on every star cut satisfying (Stab),
  `[χ] ∈ Σ^1(A_Γ)` iff `χ` is dominant and `L_0` is onto. So the corrected conjecture
  ("`L_χ` onto ⇒ `L_0` onto", target `artin-sigma1-is-level-zero-laplacian-surjectivity` of
  the held wave-19 branch) holds on this whole class.
- The wave-19 swap toy (`novikov-level-descent-fails-for-d-shaped-laplacian-systems`, held
  branch) shows that the star hypothesis cannot simply be dropped from the abstract
  statement. Its two D-shaped generators `(1+a)(ab·t - 1)` and `(1+b+b^2)(t - 1)` have
  different right factors, which is exactly what a star cut excludes.
- **Where a counterexample to the corrected conjecture must now live.** In the bipartite
  graph of crossing dead edges, no single vertex may meet every edge. Alternatively, dead
  vertices with living neighbours in two blocks must break (Stab).
  - The only fully decided class with vertex-cover number 2, the 2x2 dead joins
    (`artin-2x2-dead-joins-sigma1-iff-k-q-odd-family`), satisfies descent.
- Examples:
  - The triangle `A(3,4,6)` with `χ = (1,-1,-1)` is a star cut at `a`. By part 4, its
    non-membership is exactly `Z[H](1+ab) + Z[H](1+ac+(ac)^2) ≠ Z[H]`. The rank-two
    witness `artin-346-dead-character-outside-sigma1-by-rank-two-rep` certifies this.
  - Cones over an odd triangle, with dead cone edges, are star cuts with `r = 2`.
    Membership for them is now a pure ideal question in `Z[H]`.

## Attempts

- 2026-09-20 (swarm-0917-w20-w20-z-follow): proved parts 1-4; see the route.
  - The key point is that in a star cut every D generator is `σ_ρ (u - 1)` for the **same**
    unit `u - 1`, after a left unit change, and `σ_ρ ∈ Z[H]`.
  - Splitting `f = A(u - 1) + B` into levels telescopes the negative levels into
    `Σ_m B_{-mc} u^m`.
  - Only the level-0 V/W terms, conjugated by powers of `u`, can leak.
- Not done:
  - (Stab) was not removed for general dead vertices. The V ideal `Z[H](w - 1)` is not
    `u`-conjugation stable unless `u` normalises the relevant parabolic.
  - Non-star cuts with vertex-cover number `>= 2` beyond the 2x2 joins are untouched.
