# Referee report (gq-referee-a, proof-gap lens): BS classes over virtually quotient-free groups have big kernels

**Reviewed** (lane bh-cat0), read on origin/main:
- `bs-classes-over-virtually-quotient-free-groups-have-big-kernels` (text as of bcec5f995);
- its route `bs-quotient-free-big-kernel-proof` (b57b718b4).

Referee b has already passed the citations and scope.

**Verdict: PASS.**
- There is one required fix (W1): the word "infinite" is missing from the statement.
- There are three nits. N1 notes that the proof of item 3 covers only a finite centre, while the statement needs no
  such restriction. The gap closes in two lines, given there.
- The three-tree reduction is correct as stated: an infinite outer action forces a non-discrete projection.

## Step 1 (the author asked about this)
- **`R(U) = R(V)` for `U` of finite index in `V`.**
  - Finite-index subgroups of `U` are finite-index subgroups of `V`, so `R(V) ⊆ R(U)`.
  - For `W` of finite index in `V`, `W ∩ U` has finite index in `U`, so `R(U) ⊆ W`. Hence `R(U) ⊆ R(V)`. ✓
- **`[V : R(V)] < ∞` for `V` commensurable with `G`.**
  - Take `V' ≤ V` of finite index with `V' ≅ G'`, where `G'` has finite index in `G`. Then `R(G) ⊆ G'` and
    `R(V) = R(V') ≅ R(G') = R(G)`.
  - `[V' : R(V')] = [G' : R(G)] ≤ [G : R(G)]`. ✓
  - `R(V)` is then the smallest finite-index subgroup of `V`, and it is characteristic.

## Step 2 (the author asked about this)
- **The edge maps.** `α_e(R(E_e)) = R(α_eE_e) = R(V_(o(e)))` by Step 1, and likewise for `ω_e`.
- **One subgroup `N`.**
  - Along tree edges, `α_e(a) = ω_e(a)` in `H`, so the subgroups `R(V_x)` all coincide; call the common subgroup
    `N`.
  - For the other edges, `t_eNt_e^(−1) = ω_e(R(E_e)) = N`.
- **`N` is normal and fixes the tree.**
  - `N` is characteristic in each `V_x`, so it is normalized by every vertex group and every stable letter. So `N`
    is normal in `H`.
  - `N` lies in the vertex groups of a lift of a maximal tree. By normality it lies in every vertex stabilizer, so
    `N ⊆ K` and `K` has finite index in each `V_x`. ✓

## Step 3 (the author asked about this)
- **`H/K`.** It acts with finite vertex stabilizers `V_x/K` and finitely many orbits, so it is finitely generated and
  virtually free.
- **Item 2.** The extension `K → H_1 → F_m` splits, because `F_m` is free. ✓
- **Item 3, splitting.** `H_2 = K·C_(H_2)(K)`. See N1 for the case of infinite `Z(K)`.
- **The branch with finite `Out(R(G))` and trivial centre.**
  - Let `H_3` be the kernel of `H → Out(N)`, of finite index. Then `H_3 = N·C` with `C = C_(H_3)(N)` and
    `N ∩ C = Z(N) = 1`, so `H_3 ≅ N × C`.
  - *Finite stabilizers.* `N` is normal in `H`, so for any `h ∈ H`, `C ∩ hV_xh^(−1) ⊆ C_(hV_xh^(−1))(N)`. That
    centralizer meets `N` in `Z(N) = 1`, so it embeds in the finite group `hV_xh^(−1)/N`.
  - *Finitely many orbits.* `N` acts trivially, so `C`-orbits are `H_3`-orbits, and there are finitely many.
  - So `C` is finitely generated and virtually free. ✓
- **The `B_A` conclusion.** `K` is commensurable with `G`. So a finite-index subgroup of `K` embeds in any given
  finite-index subgroup of `G` that lies in `B_A`, up to finite index. Free groups, finite products and
  finite-index overgroups then finish the argument. ✓

## The three-tree application: does the reduction leave only a non-discrete normalizer? (the author asked me to attack this)
- **Setting up the projection.**
  - `K ⊆ G` has finite index, and it acts properly and cocompactly on `T_1 × T_2`.
  - Let `p` be the projection `Γ → Aut(T_1) × Aut(T_2)`. `p` is injective on `K`, since `K` is trivial on `T_3` and
    `Γ` acts faithfully.
  - So the conjugation action of `Γ` on `K` is conjugation by `p(Γ)` on the lattice `p(K)`.
- **Discrete implies finite outer action.**
  - If `p(Γ)` is discrete, it contains the cocompact lattice `p(K)` with finite index, by covolume (N3).
  - So the image of `Γ` in `Out(K)` is a quotient of the finite group `p(Γ)/p(K)`. ✓
- **The contrapositive is the node's gap statement.** An infinite outer action forces `p(Γ)` to be non-discrete. So
  the normalizer of `p(K)` containing it is non-discrete.
  - The node claims only this direction, "realized by a non-discrete normalizer". It does not claim that every
    non-discrete projection gives an infinite outer action, and it does not need to.
  - After item 3, the uncovered lattices are exactly those with infinite image in `Out(K)`, and each of them has
    non-discrete projection. `K ⋊ F_m` is again such a lattice. So the reduction statement is accurate. ✓
- **The fibre.** `G ∈ B_A` follows from the product-of-two-trees node when some factor has more than two ends.

## Required fix
- **W1 (Theorem, item 1).** "No member of `BS_G` is faithful" needs `G` infinite, which gives `R(G) ≠ 1`.
  - For finite `G`, `R(G) = 1` and `[G : R(G)] < ∞`, but a free group acting on its tree is a faithful member of
    `BS_(1)`.
  - Add "infinite" to the hypothesis. All the examples are infinite.

## Nits
- **N1 (Step 3, item 3).** The case split on `Z(K)` is incomplete but also unnecessary.
  - `K` can have infinite centre. A central extension of an infinite simple group by `Z` can have no finite
    quotients, for example Thompson's `T̃`.
  - In general: `C = C_(H_2)(K)` satisfies `C ∩ K = Z(K)`, and `C/Z(K) ≅ H_2/K ≤ F_m` is free.
  - The central extension splits, so `C = Z(K) × F`. Then `H_2 = KC = KF`, with `K ∩ F = 1` and `[K,F] = 1`.
  - So `H_2 = K × F` exactly, for any centre. Replace the two cases with this.
- **N2 (Theorem, item 3).** "For example, this happens when `Out(R(G))` is finite and `R(G)` has trivial centre" should
  say that in this case `H` is virtually `N × F`, by the finite-`Out` branch. What that branch proves is the conclusion
  of item 3, not its hypothesis of finite image in `Out(K)`.
- **N3 (the three-tree application).** Add the reason a discrete `p(Γ) ⊇ p(K)` contains `p(K)` with finite index:
  `p(K)` is a cocompact lattice, so `[p(Γ) : p(K)] = covol(p(K))/covol(p(Γ))`. Say also that `p` is injective on
  `K`.
