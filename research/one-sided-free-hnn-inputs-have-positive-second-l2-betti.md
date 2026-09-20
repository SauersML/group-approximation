---
rg: 2
id: one-sided-free-hnn-inputs-have-positive-second-l2-betti
kind: claim
title: A free-base HNN input F*_phi with positive Euler characteristic, in particular every non-ascending one-sided input ([F:A] = m >= 2, rk F = r >= 2), has b_2^(2) >= (m-1)(r-1) > 0, so it embeds in no group with a finite 2-dimensional K(pi,1) and vanishing second L2-Betti number (ascending HNN extensions of free groups, free-by-cyclic, torsion-free one-relator, graphs of free or Z^2 groups with cyclic edges) and in no 3-manifold group
distinct_from:
  negative-euler-inputs-get-infinitely-generated-tree-stabilizers: that uses chi < 0 to force infinitely generated stabilizers in locally finite tree hosts; this uses chi > 0 (the opposite sign, the one-sided case that node leaves untouched) to exclude whole host classes through the second L2-Betti number.
  ascending-hnn-of-free-groups-satisfy-boone-higman: that proves BH for ascending HNN extensions of free groups; this shows that no non-ascending one-sided input is a subgroup of any of them, so that theorem cannot be transported to the one-sided case by an embedding.
  almost-all-one-relator-groups-satisfy-boone-higman: that embeds generic one-relator groups in ascending HNN extensions of free groups; this shows that inputs with positive Euler characteristic lie in no torsion-free one-relator group and in no such extension.
  bh-embeddability-survives-decidable-edge-hnn: that is the open permanence statement; this is an obstruction to one class of strategies for its one-sided free case, not a proof or refutation of it.
  finite-2-complex-with-zero-second-l2-betti-is-aspherical: that derives asphericity from b_2^(2) = 0 for a finite 2-complex; this uses b_2^(2) = 0 of a host to force b_2^(2) = 0 on every subgroup.
artifacts:
  - experiments/l2-one-sided-hnn-2026-09-17/stallings_check.py
  - experiments/l2-one-sided-hnn-2026-09-17/stallings_check.out
---

**ESTABLISHED** (lane proof, not reviewed). The new part is the subgroup lemma (step 2) and its
application to the BH inputs. The vanishing theorems for the hosts are cited from the literature,
as listed under "Imports".

## Statement

Let `F` be free of rank `r`, let `A, B <= F` be finitely generated, let `φ : A -> B` be an
isomorphism, and put `G = F*_φ`.

1. **Euler characteristic and L2.** `G` has a finite 2-dimensional `K(G,1)` and
   `χ(G) = rk A - r`. If `χ(G) > 0`, then `b_2^(2)(G) >= χ(G) > 0`.
   - In the **one-sided case**, `[F:A] = m` and `B` arbitrary, `rk A = m(r-1) + 1`. So
     `χ(G) = (m-1)(r-1)`, which is positive exactly when `m >= 2` and `r >= 2`, that is, for every
     one-sided input that is neither ascending (`m = 1`) nor Baumslag--Solitar (`r = 1`).
   - The Artin reduction `F_3 *_{F_7}` of Attempt bh-last1 has `χ = 4`.
2. **Subgroup lemma.** Let `K` have a finite 2-dimensional `K(K,1)` with `b_2^(2)(K) = 0`. Then
   `b_2^(2)(H) = 0` for every subgroup `H <= K`, finitely generated or not.
3. **Host classes killed.** So a group with `b_2^(2) > 0`, and in particular every `G` of item 1, is
   a subgroup of no group in the following classes.
   - (H1) Ascending HNN extensions `F_n *_ψ` of finitely generated free groups by injective
     endomorphisms, including every free-by-cyclic group `F_n ⋊ Z`.
   - (H2) Torsion-free one-relator groups.
   - (H3) Fundamental groups of finite graphs of groups whose vertex groups are free, `Z^2`, closed
     surface groups or torsion-free one-relator groups, and whose edge groups are infinite cyclic.
     These include GBS groups (all `BS(m,n)`), tubular groups, and cyclic amalgams and cyclic HNN
     extensions of free groups.
   - (H4) Fundamental groups of 3-manifolds, compact or not, orientable or not. This one uses only
     `χ(G) > 0`, not L2.
4. **Explicit instance.** `F = F(x,y)`, `A = <x^2, y, xyx^-1>` (index 2), and
   `B = <x^2, y^2, xy^2x^-1>` (infinite index, rank 3). The map `φ` sends
   `x^2 -> x^2`, `y -> y^2`, `xyx^-1 -> xy^2x^-1`, and `χ(G) = 1`. `G` contains `BS(1,2) = <t, y>`,
   so it is not residually nilpotent, and so it is not a subgroup of a right-angled Artin group either.
   The ranks and indices are checked by `experiments/l2-one-sided-hnn-2026-09-17/stallings_check.py`.

## Proof

1. **Item 1.**
   - Let `R` be a rose with `r` petals and `R_A` a graph with `π_1 = A`. Realize `ι : A -> F` and
     `φ` by graph maps `R_A -> R`. The double mapping cylinder with its two ends glued to `R` is a
     finite 2-complex. It is a graph of aspherical spaces with `π_1`-injective edge maps, so it is
     aspherical with fundamental group `G`.
   - Its Euler characteristic is `χ(R) - χ(R_A) = (1 - r) - (1 - rk A) = rk A - r`.
   - The L2 Euler--Poincaré formula on the universal cover gives
     `χ = b_0^(2) - b_1^(2) + b_2^(2)`. `G` is infinite, so `b_0^(2) = 0`, and therefore
     `b_2^(2) = χ + b_1^(2) >= χ`.
   - For `[F:A] = m`, Schreier gives `rk A = m(r-1) + 1`.
2. **Item 2.**
   - Let `X` be the universal cover of the finite 2-dimensional `K(K,1)`. It is a contractible,
     locally finite, free cocompact `K`-CW complex. Its cellular L2 chain complex has bounded
     differentials. There are no 3-cells, so `H_2^(2)(X) = ker(∂_2 : ℓ²C_2(X) -> ℓ²C_1(X))` is a
     closed `K`-invariant subspace, of von Neumann dimension `b_2^(2)(K) = 0`. By faithfulness of
     the dimension, `ker ∂_2 = 0`: **X carries no nonzero square-summable 2-cycle.**
   - Now let `H <= K`. `X` is a contractible free `H`-CW complex, so `C_*(X)` is a free
     `ZH`-resolution of `Z`. In Lück's extended sense,
     `b_2^(2)(H) = dim_{N(H)} ker(id ⊗ ∂_2 : N(H) ⊗_{ZH} C_2(X) -> N(H) ⊗_{ZH} C_1(X))`.
   - Choose `H`-orbit representatives `Σ` of the 2-cells, possibly infinitely many. An element of
     `N(H) ⊗_{ZH} C_2(X) = ⊕_{σ∈Σ} N(H)` is a finitely supported family `(a_σ)`.
   - Evaluate at `δ_e`, using the injective `N(H)`-map `N(H) -> ℓ²(H)`, `a -> a(δ_e)`. This sends
     `(a_σ)` to the chain `Σ_σ Σ_{h∈H} a_σ(δ_e)(h) · hσ`. That chain is square-summable, because
     finitely many `σ` occur and the cells `hσ` are pairwise distinct.
   - `∂_2` is given by the same finite `ZH`-matrix on both sides, so evaluation commutes with
     `∂_2`. A kernel element therefore gives a square-summable 2-cycle on `X`. That cycle is 0, and
     since evaluation is injective, the element is 0.
   - So the kernel is 0, and `b_2^(2)(H) = 0`.
3. **Item 3, (H1)--(H3).** Each class has a finite 2-dimensional `K(π,1)` with `b_2^(2) = 0`.
   - (H1) The mapping torus `T_f` of a graph map `f : R_n -> R_n` realizing `ψ` is a finite aspherical
     2-complex with `π_1 = F_n *_ψ`. Lück's mapping torus theorem, for arbitrary cellular self-maps,
     gives `b_p^(2)(T̃_f) = 0` for all `p`.
   - (H2) If the relator is not a proper power, the presentation complex is aspherical (Lyndon), and
     `b_2^(2) = 0` (Dicks--Linnell).
   - (H3) The graph of spaces, with edge spaces `S^1 × [0,1]`, is a finite aspherical 2-complex. The
     Mayer--Vietoris sequence of L2-homology, with additive extended dimension and induction
     preserving dimension, gives
     `b_2^(2)(K) <= Σ_v b_2^(2)(K_v) + Σ_e b_1^(2)(K_e) = 0`. The vertex groups have `b_2^(2) = 0`: for
     free groups trivially, for `Z^2` because it is amenable, for closed surfaces with `χ < 0`
     because `b_2^(2) = b_0^(2) = 0` by Poincaré duality, and by (H2) for one-relator groups. The edge
     groups have `b_1^(2)(Z) = 0`.
   - Then apply item 2 to the subgroup `G`.
4. **Item 3, (H4).**
   - Suppose `G <= π_1(M)` for a 3-manifold `M`. `G` is finitely generated, so by Scott's core
     theorem, applied to the cover of `M` with group `G`, we get `G = π_1(N)` for a compact
     3-manifold `N`.
   - Pass to the orientation cover, of index at most 2: `G'` has `χ(G') = [G:G'] χ(G) > 0`. Cap off
     boundary spheres and write `N' = N_1 # ... # N_k` (Kneser--Milnor). `G'` is torsion-free, since
     it has finite cohomological dimension, and nontrivial. So each `N_i` with nontrivial `π_1` is
     either `S^1 × S^2` (`χ(Z) = 0`) or irreducible with infinite `π_1`.
   - An irreducible `N_i` with infinite `π_1` is aspherical, and it has no sphere boundary
     components. So `χ(π_1 N_i) = χ(N_i) = χ(∂N_i)/2 <= 0`.
   - Then `χ(G') = Σ_i χ(π_1 N_i) - (k-1) <= 0`, a contradiction.
5. **Item 4.** Both generating sets have 3 elements and generate free groups of rank 3
   (`stallings_check.out`). By the Hopf property they are free bases, so `φ` is an isomorphism.
   `B` is not of finite index, because its folded core graph is not a covering. The relation
   `t y t^-1 = y^2` gives `BS(1,2) <= G`. In `BS(1,2)` the lower central series stabilizes at
   `Z[1/2] ≠ 1`, and right-angled Artin groups are residually torsion-free nilpotent. ∎

## What dies, and where

**Invariant.** `b_2^(2)`, or for (H4) `χ`.

**Step where every member dies.** Any strategy for the one-sided (or any `χ > 0`) free case of
`bh-embeddability-survives-decidable-edge-hnn` that first embeds `G` into a host from (H1)--(H4) and
then quotes that host's Boone--Higman theorem dies at the first step. The host has `b_2^(2) = 0` on
every subgroup, while `b_2^(2)(G) >= (m-1)(r-1)`. Concretely:

- reduction to `ascending-hnn-of-free-groups-satisfy-boone-higman` or to free-by-cyclic hosts
  (`baumslag-solitar-and-free-by-cyclic-satisfy-boone-higman`), for instance by "untwisting" `t`
  into a stable letter of an ascending or mapping-torus overgroup;
- reduction to one-relator hosts through Sapir--Spakulova-type embeddings
  (`almost-all-one-relator-groups-satisfy-boone-higman`);
- GBS or tubular hosts, and cyclically split hosts over free vertex groups;
- 3-manifold hosts.

**What survives.** Hosts with `b_2^(2) > 0`. The Hall hosts `Y*_Φ ∈ BS_{F_2}` of Attempt bh-free-05
survive: `χ(Y*_Φ) = (M - 1) r > 0` for `[Y:C_1] = M >= 2`. So do identity-edge HNN overgroups
`M *_C (C × Z)` with `rk C >= 2` (Attempt 9 and bh-free-10), and RAAG-type or higher-dimensional
hosts, although item 4 shows that RAAGs fail for inputs containing `BS(1,2)`. Together with
`negative-euler-inputs-get-infinitely-generated-tree-stabilizers` this pins the free case in both
directions:

- for `χ < 0`, locally finite tree hosts must have infinitely generated stabilizers;
- for `χ > 0`, every 2-dimensional host must have `b_2^(2) > 0`.

## Imports

- Lück, *L2-Invariants*, Thm 1.39: the mapping torus of a cellular self-map of a finite CW complex
  is L2-acyclic.
- Lück, the same book, Ch. 6: extended dimension, additivity, and induction.
- Dicks--Linnell, "L2-Betti numbers of one-relator groups", Math. Ann. 2007.
- Lyndon's identity theorem.
- Scott's compact core theorem.
- Kneser--Milnor prime decomposition.
