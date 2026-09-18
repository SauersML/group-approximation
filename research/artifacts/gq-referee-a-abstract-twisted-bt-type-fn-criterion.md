# Referee report (gq-referee-a, proof-gap lens): abstract twisted Brin–Thompson groups — the colored-subgroup realization and the F_n criterion for every action

**Reviewed** (lane bh-typeA-universal, 55f205b7f), read on origin/main:
- `abstract-twisted-bt-group-is-colored-subgroup-of-faithful-one`, with route `abstract-twisted-bt-colored-subgroup-proof`;
- `abstract-twisted-bt-type-fn-criterion`, with route `abstract-twisted-bt-type-fn-colored-stein-proof`.

The BZ sections were read at `gq/src/bh-free-17/bz22/twisted_Brin_Thompson.tex`, l.588–870: §§5–7, including
`lem:VE_conn`, the merge link, both split-link lemmas and `prop:E_hi_conn`.

**Verdict: PASS for both.** There are four nits.
- One nit (N1) concerns a sentence in BZ's `lem:VE_conn`. It is imprecise, but its conclusion holds by a join
  decomposition, which I checked. So it does not affect this route, or the faithful one.
- As with the faithful criterion (16bd2d9b5), this node claims an open conjecture: FFWZ §1.2. I recommend the
  independent second pass already requested of gq-referee-c, and referee b on:
  - Brown's presentation theorem (1984);
  - Brown's result that finitely presented plus `FP_n` gives `F_n`;
  - FFWZ Corollary 4.18.

## 1. `SV_G ≅ Σ`, the `S`-colored subgroup of `S'V_G`
- **`Ψ` is well defined.** The generating relations of `SV_G^(abs)` hold in `S'V_G`:
  - the `SV` relations, on the `C^S` factor;
  - twist composition;
  - `x_(gs) τ_g = (τ_g ⊕ τ_g) x_s` and the twist–permutation relation, `lem:Relations` (6) and (7), for every
    `s ∈ S ⊆ S'`, including `g ∈ K`.

  `Ψ` is compatible with direct sums. ✓
- **`Ψ` is injective.** Take the normal form `F_−^(−1)p_σ(g_i)F_+`.
  - If its image is the identity, each leaf brick `B_i` maps onto `B'_(σ i) = B_i` by
    `canon ∘ τ_(g_i) ∘ canon^(−1)`, so `τ_(g_i) = id` on `C^(S')`.
  - A coordinate permutation of `C^(S')` is the identity iff the permutation of `S'` is trivial. The action on the
    summand `G` is free, so `g_i = 1`.
  - The remaining `SV`-element acts as the identity homeomorphism, so it is trivial in `SV`, hence in `SV_G^(abs)`. ✓
- **The image.** Twists pass S-colored forests into S-colored forests by relation (7), so every element has the form
  `f_2^(−1)tf_1` with `S`-colored `f_i`.
- **The kernel `SK_G`.**
  - It fixes the `S`-coordinates and translates the `C^G`-coordinates.
  - Elements of `Σ` preserve the product `C^S × C^G`, because bricks are cut only in `S` and twists preserve both
    summands.
  - So "forget `C^G`" is a homomorphism `Σ → SV_(G/K)`, as stated. ✓

## 2. The criterion, risk point (a): the transfer of BZ §§5–7 (the author asked about this)
- **Vertices and stabilizers.** Vertices of `F_m` correspond to partitions of `C^(S')(m)` into `S`-bricks, as in
  `prop:JoinForests`, because twisted permutations do not change the domain partition.
  - `lem:vtx_stab` goes through inside `Σ`: `𝒢(m) ≅ G ≀ Σ_m` acts faithfully, since `G ↷ S'` is faithful. So vertex
    stabilizers are the true `G ≀ Σ_m`, not their preimages under a quotient. This is exactly the repair of the gap
    node.
  - In `lem:stab_spectrum` and `prop:stabs`, `τ_γ` preserves the bricks of `f` when `γ` fixes `Spec(f) ⊆ S`
    pointwise. The `G`-coordinates are never cut.
  - The setwise stabilizers `Stab_G(C)`, for `C ⊆ S`, are the same for `G ↷ S'` and for `G ↷ S`, and they contain
    `K`.
- **Contractibility.** `prop:directed` and `prop:elem_core` go through: common upper bounds come from the
  `S`-colored normal form, and there is a simple split below every nontrivial forest. So `prop:cible` holds. ✓
- **`lem:VE_conn`.** The combinatorics is in leaves, `S`-colors and twist data only.
  - The twist data of different roots is independent, since `𝒢` acts rootwise.
  - So the lemma transfers verbatim. On the lemma itself, see N1.
- **`lem:all_big`.** An atom is minimal, so its star is the order complex of the up-set `Q_(≥z)`. Intersections are
  up-sets of joins, taken in the lattice of `S`-partitions. This is the same computation as the grid-sphere lemma.
  ✓
- **The merge link, and `lem:some_small`.** Pruning uses only which leaves go to which roots. ✓
- **Descending links.** Descending links of rank-`m` vertices are all `E_m`, because `Σ` is transitive on each rank:
  `h^(−1)h'` is `S`-colored. With contractibility of `X^S` and Morse theory, `X^S_m` is `(n−1)`-connected for
  large `m`. ✓

## 3. Risk point (b): the `π_1` filtration and Brown's presentation theorem (the author asked about this)
- **Van Kampen.**
  - Simplices of `F_d ∖ F_(d−1)` lie in a unique interval of length `d`, so `|I| ∩ F_(d−1) = ∂I` and different
    `|I|` meet inside `F_(d−1)`.
  - `|I|` is a cone. For `d ≥ 2`, `(v,w) ≠ ∅`, so `∂I = Σ|(v,w)|` is connected (N2).
  - Attaching cones along connected subspaces gives `π_1(F_d) = π_1(F_(d−1))/⟨⟨im π_1 ∂I⟩⟩`. ✓
- **Only `e = 2` kills anything.**
  - Non-grid intervals have contractible `∂I`.
  - For `e ≥ 3`, `Σ S^(e−2)` is simply connected.
  - For `e = 2`, `(v,w)` has two contractible components, so `π_1(∂I) = Z`.
    - The square: splits at two leaves, with `(v,w)` = two points.
    - The hexagon: one leaf in colors `{r,b}`. I recomputed the six intermediate partitions: `x_r` and `x_b`, and four
      3-brick partitions. The two components are the cones on `x_r` and on `x_b`.
    - The stated hexagon uses only short edges and runs through both components, so it generates `π_1(∂I)`.
  - The relation loops lie in `F_1`, so `π_1(X^S_m) = π_1(Γ_sh)/⟨⟨ℓ_I⟩⟩`. ✓
- **The complex `Y` and Brown's theorem.**
  - `Y` is simply connected, because every attached loop generates its `π_1(∂I)`.
  - Edges are oriented by rank, and there is one 2-cell per based oriented loop, so the action is rigid.
  - Under `[A_2]`:
    - vertex stabilizers `G ≀ Σ_r` are finitely presented;
    - short-edge stabilizers are commensurate with `Stab_G(s) × G^(r−1)` (`prop:stabs`, with `Spec = ∅` on the other
      roots), hence finitely generated.
  - The orbit counts are finite:
    - vertices, over ranks `≤ m`;
    - short edges, from `G`-orbits on `S`;
    - `e = 2` intervals, from `G`-orbits on pairs of `(leaf, color)` data (independent twists at distinct leaves) and
      on 2-subsets;
    - finitely many loops per interval.
  - Brown's theorem needs no condition on 2-cell stabilizers. So `Σ` is finitely presented. ✓
- **Steps 2 and 4.** The faithful `FP_n` argument carries over, with grid stabilizers `∏ Stab_G(C_i)` for
  `G ↷ S` and orbit counts on `S^n`. Nothing uses faithfulness. Finitely presented plus `FP_n` then gives `F_n`. ✓

## Nits
- **N1 (BZ `lem:VE_conn`, as used by both criteria).** BZ write that `VE_m^(i,j)` is the union of the stars of its
  rank-`(m−1)` vertices matching `i` and `j`. As stated, this misses the vertices that match neither `i` nor `j`.
  - For example, at `m = 4` the merge of `(3,4)` alone is incomparable with every merge of `(1,2)`, so it lies in no
    such star.
  - The conclusion still holds. `VE_m^(i,j)` is the order complex of `(A ∪ {⊤}) × (VE_(m−2) ∪ {⊤}) ∖ {(⊤,⊤)}`, with
    `A` the nonempty discrete set of `(i,j)`-merge data. So it is `|A| * |VE_(m−2)|`, which is at least
    `ν(m−2) ≥ ν(m) − 1` connected. The `r`-fold intersections are joins of `r` discrete sets with `VE_(m−2r)`, which
    satisfies the Nerve Lemma bound.
  - Record this in the route, since the transfer claim reads BZ's §7 line by line.
- **N2 (Step 3).** Say why `(v,w) ≠ ∅` for elementary intervals of length `≥ 2`: a refinement by `≥ 2` bricks factors
  through an intermediate dyadic partition, using `prop:JoinForests`.
- **N3 (Step 3).** Say that separate 2-cells are attached for all hexagon choices, four per one-leaf interval, and
  that this keeps the cell set `Σ`-invariant and the action rigid.
- **N4 (colored subgroup, Step 1).** Quote FFWZ's generating relations (l.437–455) explicitly, so that it is visible
  that none involves `K` beyond relation (7) with `gs = s`.
