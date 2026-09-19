---
rg: 2
id: abstract-twisted-bt-type-fn-colored-stein-proof
kind: route
title: Run the faithful interval-filtration argument on the S-colored Stein complex of S'V_G, and get finite presentation from a pi_1 version of the filtration
target: abstract-twisted-bt-type-fn-criterion
requires:
  - abstract-twisted-bt-group-is-colored-subgroup-of-faithful-one
  - stein-complex-elementary-intervals-are-grid-spheres
  - twisted-brin-thompson-type-fn-criterion
  - twisted-brin-thompson-type-fn-implies-type-an
---

Notation: `G ↷ S` with kernel `K`, `S' = S ⊔ G`, and `Σ ≅ SV_G` the `S`-colored subgroup of
the faithful `S'V_G`. BZ = arXiv:2001.04579 (TeX on MSI); FFWZ = arXiv:2603.24687v2.
Necessity is `twisted-brin-thompson-type-fn-implies-type-an`; only sufficiency is proved here.

## Step 1. The S-colored Stein complex

- Let `P^S_1` be the set of classes `[h] = 𝒢(m) h` of corank-one elements `h` of the
  `S`-colored subgroupoid. Here `𝒢(m) ≅ G ≀ Σ_m` are the twisted permutations; they involve
  no splits, so they lie in it.
- Order `P^S_1` by expansion along `S`-colored forests. Let `X^S` be its Stein complex
  (elementary chains) and `X^S_m` the rank `≤ m` part. `Σ` acts by right multiplication.

**Transfer of BZ §§5–7.** The following hold for `P^S_1` with the same proofs:
- `prop:directed`: by the normal form `f_2^{-1} t f_1` with `S`-colored forests;
- `prop:JoinForests`: classes of `S`-colored forests of corank `m` correspond to dyadic
  partitions of `C^{S'}(m)` into `S`-bricks, ordered by refinement;
- `prop:elem_core` and `prop:cible`: `X^S` is contractible;
- `lem:vtx_stab`: `Stab_Σ([h]) = h^{-1} 𝒢(m) h ≅ G ≀ Σ_m`;
- `lem:stab_spectrum` and `prop:stabs`: an elementary interval with trees of spectra `C_i ⊆ S`
  has stabilizer commensurate with `∏ Stab_G(C_i)`;
- `prop:E_hi_conn`: descending links are `min(ν(m/2)−2, log_2(m/2)−2)`-connected.

Each of these proofs is carried out inside the faithful groupoid `S'V_G` of homeomorphisms.
They use only:
- multicolored forests in the split colors;
- twisted permutations;
- the relations `lem:Relations`(1)–(8) for split colors;
- the fact that elements are determined by their action.

None of them uses that the split colors exhaust the coordinates, or that `G` acts faithfully
on the split colors. `Stab_G(C)` for `C ⊆ S` is the same group for `G ↷ S'` and for
`G ↷ S`.

**Checked.** Referees a and c checked the transfer line by line and passed it. The labels
here are `S`-colors with twists in `G`.

**BZ `lem:VE_conn` is true, but its published proof has two errors.** Referee c (W1,
`research/artifacts/gq-bh-referee-c-conjecture-h-and-ffwz.md`, 488bd5ce1) gives the corrected
proof used here.
- *The errors.*
  - `VE_m^{i,j}` also contains vertices that avoid `i` and `j` (referee a).
  - For `m ≥ 5` the covering sets meet for non-disjoint pairs as well: the merge of leaves
    4, 5 lies in both `VE_5^{1,2}` and `VE_5^{1,3}`. So BZ's nerve is larger than the
    matching complex, and the Nerve-Lemma computation does not go through.
  - The join description `|A_{ij}| * |VE_{m−2}|` recorded earlier is correct for one pair,
    but intersections for non-disjoint families are not joins.
- *Correct argument.* A vertex of `VE_m` is a nonempty set of disjoint merged pairs of the `m`
  leaves. Each pair carries a label, the class of (color, twist, twist) modulo the left
  twisted permutations. The order is reverse inclusion of labelled matchings, since
  un-merging pairs expands. So `VE_m` is the order complex of the face poset of the labelled
  matching complex `M_L(K_m)` of the complete multigraph, and is homeomorphic to it. Every
  label set is nonempty, because `S ≠ ∅`.
  - The projection `M_L(K_m) → M(K_m)` is a complete join complex in the sense of
    Hatcher--Wahl: surjective, injective on simplices, and with preimage of each simplex the
    join of the label sets.
  - `M(K_m)` is `(ν(m)−1)`-connected, with `ν(m) = ⌊(m−2)/3⌋` (Björner--Lovász--Vrećica--
    Živaljević, J. London Math. Soc. 49 (1994), Thm 4.1, as BZ cite). The link of a
    `p`-simplex is `M(K_{m−2p−2})`, and `ν(m) − ν(m−2p−2) ≤ ⌈(2p+2)/3⌉ ≤ p+1`. So `M(K_m)`
    is weakly Cohen--Macaulay of dimension `ν(m)`.
  - By Hatcher--Wahl, Duke Math. J. 155 (2010), Proposition 3.5 (recalled by referee c, not
    re-read at source), `M_L(K_m)` is weakly Cohen--Macaulay of dimension `ν(m)`, hence
    `(ν(m)−1)`-connected.
  - The rest of `prop:E_hi_conn` stands: the merge link is `≅ VE_{μ_1}`, and the split-link
    lemmas are reproved by `stein-complex-elementary-intervals-are-grid-spheres`.

With Bestvina--Brady Morse theory, as in FFWZ Proposition 4.8(ii): for every `n` there is
`M` with `X^S_m` `(n−1)`-connected for `m ≥ M`.

## Step 2. FP_n (item 1)

Repeat Steps 0 and 2–6 of `twisted-bt-type-fn-interval-filtration-proof` with `Σ ↷ X^S_m`:
- interval filtration;
- `stein-complex-elementary-intervals-are-grid-spheres`, which uses only the lattice of
  `S`-colored partitions;
- grid stabilizers `∏ Stab_G(C_i)` with `|C_i| ≤ e`, of type `FP_{n−e}` under `[HA_n]`;
- finitely many orbits of grid intervals with `e ≤ n`;
- vertex stabilizers `G ≀ Σ_r` of type `FP_n`;
- extension closure of `n`-finite complexes.

Faithfulness of `G ↷ S` is not used. So `[HA_n] ⇒ FP_n`.

## Step 3. Finite presentation from [A_2] (item 2)

Fix `m` with `X^S_m` simply connected. Filter by interval length, `F_1 ⊆ F_2 ⊆ ...`. Every
`∂I` with `d ≥ 2` is connected and non-empty, so attaching does not merge components. For
`d ≥ 2`, `(v, w) ≠ ∅` because the partition of `w` refines some atom `z_i^s < w`, the root
split of a nontrivial tree (N2).
Since `X^S_m` is connected, `F_1` is connected too.
- `F_1` is the graph `Γ_sh` of short edges (intervals of length one).
- For `d ≥ 2`, the realization `|I|` of an interval of length `d` is attached to `F_{d−1}`
  along `∂I = Σ|(v,w)|`, which is connected because `(v,w) ≠ ∅`. By van Kampen:
  `π_1(F_d) = π_1(F_{d−1}) / ⟨⟨ im π_1(∂I) : |I| = d ⟩⟩`.

By `stein-complex-elementary-intervals-are-grid-spheres`:
- `∂I` is contractible if `I` is not a grid interval;
- `∂I ≃ S^{e−1}`, which is simply connected, if `I` is a grid interval with `e ≥ 3`;
- `∂I ≃ S^1` if `e = 2`. Then `(v,w)` has two contractible components, and `π_1(∂I)` is
  generated by any short-edge loop `ℓ` that runs from `v` to `w` through one component and
  back through the other.

Such loops exist:
- for two splits at different leaves, `ℓ` is the square;
- for one leaf split in colors `{r, b}`, `ℓ` is the hexagon
  `v → x_r → (x_b on one half) → w → (x_r on one b-half) → x_b → v`.

So `π_1(X^S_m) = π_1(Γ_sh) / ⟨⟨ ℓ ⟩⟩`, over all `e = 2` grid intervals and such loops.

Let `Y` be `Γ_sh` with a 2-cell attached along every such oriented based loop. For a hexagon
interval these are all four choices of half in each leg, in both orientations (N3). Then `Y` is a
simply connected `Σ`-CW complex. Edges are oriented by rank, and an element stabilizing a
based oriented loop fixes all its vertices, so the action is rigid.

Under `[A_2]`:
- vertex stabilizers `G ≀ Σ_r` are finitely presented;
- short-edge stabilizers are commensurate with `Stab_G(s) × G^{r−1}` (by `prop:stabs`),
  hence finitely generated;
- there are finitely many orbits of vertices (ranks `≤ m`), of short edges (orbits on `S`),
  and of 2-cells (orbits on ordered pairs and on 2-subsets, times finitely many loops).

By Brown's presentation theorem (K. S. Brown, J. Pure Appl. Algebra 32 (1984); the form used
by Zaremsky, quoted as FFWZ Citation 4.11; not re-read at source), `Σ ≅ SV_G` is finitely
presented. Referee b (W3) adds Khanh, arXiv:2609.08428, lines 458–460, as a second citation.
There the two-dimensional Borel-construction presentation argument is written out.

## Step 4. F_n (item 3)

For `n ≥ 2`:
- `[A_n] ⇒ [A_2]` gives finite presentation (Step 3);
- `[A_n] ⇒ [HA_n]` gives `FP_n` (Step 2);
- finitely presented and `FP_n` implies `F_n` (Brown, *Cohomology of Groups*, §VIII.7).

For `n = 1`, `FP_1 = F_1`. For `n = ∞`, apply this for all `n`.
