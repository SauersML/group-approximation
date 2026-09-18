# Referee report (gq-referee-c, independent second proof-gap pass): Belk–Zaremsky Conjecture H and the FFWZ §1.2 conjecture

**Reviewed** (lane bh-typeA-universal), read with `git show 2921c743f:<path>`. The nodes are
unchanged in mathematical content at origin/main b72d5921a; only status lines changed since.
- **Item (1).** `twisted-brin-thompson-type-fn-criterion`, with route
  `twisted-bt-type-fn-interval-filtration-proof`, input `stein-complex-elementary-intervals-are-grid-spheres`
  (route `stein-interval-grid-sphere-proof`), and necessity `twisted-brin-thompson-type-fn-implies-type-an`.
- **Item (2).** `abstract-twisted-bt-group-is-colored-subgroup-of-faithful-one` (route
  `abstract-twisted-bt-colored-subgroup-proof`) and `abstract-twisted-bt-type-fn-criterion` (route
  `abstract-twisted-bt-type-fn-colored-stein-proof`), plus the gap node
  `ffwz-nonfaithful-stein-stabilizers-contain-canonical-kernel`.

**Independence.** I rechecked every step myself and did not use referee a's reports
(16bd2d9b5, efa4f3b5c) or the earlier referee-c reports as evidence.

**Sources read at source on MSI:**
- **BZ** = Belk–Zaremsky arXiv:2001.04579, `gqsrc/bh-openq/2001.04579/twisted_Brin_Thompson.tex`
  (md5 76e00cd6…): l.157–227, §§2–7 (l.296–870).
- **FFWZ** = arXiv:2603.24687v2, `/scratch.global/sauer354/bh-reviewer/2603.24687.txt`
  (md5 be32b748…): l.83–125, 437–535, 740–1193.

## Verdicts

| Claim | Verdict |
|---|---|
| (1) Faithful `SV_G` is `F_n` ⟺ `(A_n)`, and `FP_n` ⟺ `(HA_n)`; this is BZ Conjecture H | **PASS**, with one required documentation fix (W1) |
| (2a) Abstract `SV_G` ≅ the `S`-colored subgroup of the faithful `(S⊔G)V_G` | **PASS** |
| (2b) Abstract `SV_G` is `F_n` ⟺ `[A_n]`, `FP_n` ⟺ `[HA_n]`, fp ⟺ `[A_2]`; this is the FFWZ §1.2 conjecture | **PASS**, with the same W1 |
| The FFWZ gap claimed in the gap node | **Confirmed**, and genuine |

W1 concerns a published lemma both proofs import (BZ `lem:VE_conn`). Its **conclusion is true**; I
supply a repair below. The repair recorded on the nodes (the "N1 join" note) fixes one error in BZ's
proof but misses a second one.

## 1. The conjectures match what is proved

- **BZ.** BZ l.220–227 state the conjecture (unnumbered in this TeX; FFWZ cite it as "Conjecture
  H"), for `G` acting faithfully (l.153). `SV_G` is `F_n` iff:
  - (1) there are finitely many orbits of `n`-subsets;
  - (2) `G` is `F_n`;
  - (3) for `1 ≤ k < n`, `k`-subset stabilizers are `F_{n−k}`.

  This is equivalent to `(A_n)`. From (1), Cameron's monotonicity (infinite `S`; trivial for finite
  `S`) gives finitely many orbits on `k`-subsets for all `k ≤ n`. So there are finitely many orbits
  on `S^n`: tuples with support `T` form finitely many `Stab(T)`-orbits of surjections. Setwise and
  pointwise stabilizers of finite sets are commensurate. The converse is immediate. Cameron is
  cited, not read, as the node says.
- **FFWZ.** FFWZ l.115–117: "we conjecture that SV_G is of type F_n if and only if G ↷ S is of type
  [A_n]. This is even open for G ↷ S faithful [BZ22, Conjecture H]". Definition 1.3 (l.83–89) gives
  `[A_n]`: `G` is `F_n`; `Stab_G(T)` is `F_{n−|T|}` for finite `T`; finitely many orbits on `S^n`.
  This matches node (2b), item 3 exactly. l.1188–1193 also pose the `[HA_n]` ⇒ `FP_n` question,
  which is item 1.

## 2. Item (1): the interval-filtration proof

Every step was checked line by line. What each step rests on:
- **Step 0 (homological algebra).**
  - The extension lemma (d): the `P ⊕_ε Q` construction is a chain complex because `dε + εd = 0`.
    `Φ` is a chain map by the identity `dλ − λd = ατ` and `τ − φε = ds − sd`. The five and four
    lemmas give bijectivity for `i < n` and surjectivity at `n`, with the correct index bookkeeping.
  - (a) is dimension shifting of a partial resolution. For `e = n` only `FP_0` is used.
  - (b) holds because bounded-below free complexes are K-projective.
  - (c) holds because homology commutes with direct sums.
  - (e) reads off a length-`n` partial free resolution.
- **Step 2 (interval filtration).**
  - A simplex's minimal enclosing interval is `[v_0, v_k]`.
  - Sub-intervals of elementary intervals are elementary (BZ l.628).
  - So `C(F_d)/C(F_{d−1}) = ⊕_I C(|I|, ∂I)` with `∂I = |[v,w)| ∪ |(v,w]|`.
  - Simplices are canonically ordered chains, so each `C_k` is a permutation module and there are
    no sign issues.
- **Step 3, the grid-sphere lemma.** Correct, via Quillen's fiber lemma. Its inputs:
  - BZ `prop:JoinForests` (l.601–609): classes are unordered dyadic partitions, ordered by
    refinement.
  - The atoms `z_i^s` for `s ∈ SSpec(f_i)`; the root split of a nontrivial tree is one of them.
  - Joins `z_U`, with `z_A = w` exactly in the grid case.
  - Every fiber `{z ≥ z_U}` has minimum `z_U ∈ Q`.
  - So `|Q| ≃ ∂Δ^{|A|−1}` in the grid case and contractible otherwise. The relative homology is
    `Z_χ[e]`, with `χ` the sign of the permutation of the atoms.

  This avoids BZ's own nerve step in `lem:all_big` (l.837). That step says "any intersection of
  complexes Z_i^s equals the star … of the join", which is imprecise: the intersection is
  `|Q_{≥ join}|`, a cone, not the star. It is still contractible, so nothing breaks.
- **Step 4 (stabilizers).** BZ `prop:stabs` (l.703–710, read) says the stabilizer of a simplex is
  commensurate with `∏ Stab_G(Spec(f_i))`, and the proof is valid for the edge `(v, w)`. For a grid
  tree, `Spec(f_i) = C_i`. `Z_χ` is `FP_{n−e}` via the ring automorphism `g ↦ χ(g)g`.
- **Step 5 (finitely many orbits).** The vertex stabilizer `𝒢(r) ≅ G ≀ Σ_r` (`lem:vtx_stab`).
  Twists move spectra by `γ^{-1}` (`lem:Relations`(7), l.375). So the orbits of grid intervals with
  `e ≤ n` are finite in number.
- **Steps 6–7 (assembly).** Induction on `d`. `X_m` is `(n−1)`-connected (see §4), so the
  augmentation satisfies Step 0(e). `(A_n)` gives `(A_2)`, and so finite presentation (Zaremsky). A
  finitely presented group of type `FP_n` is `F_n`.

No gap other than W1.

## 3. Item (2): the colored realization and the colored Stein complex

- **(2a), well-definedness.** FFWZ Definition 2.12 (l.437–455, 502–510) generates the abstract
  groupoid by `SV` and `G(n)`. The relations are `x_{g.s} g = (g⊕g) x_s` and the permutation
  relation, closed under composition and direct sum. In `S'V_G` (`S' = S ⊔ G`) these are BZ
  `lem:Relations`(7), (6) and (3). The twist map is injective because `G ↷ S'` is faithful, and the
  `S`-colored part of `S'V` is `SV × id`.
- **(2a), injectivity.** This uses the normal form of l.476. If `Ψ(h) = id`, then the leaf bricks
  agree, each `τ_{g_i} = id` on `C^{S'}`, and `g_i = 1` because `G` acts freely on the second
  summand. The remaining element is an `SV`-element acting as the identity on `C^S`, which is
  faithful. **PASS.**
- **(2b), transfer of BZ §§5–7.** I rechecked each item for the `S`-colored poset:
  - the normal form `f_2^{-1}tf_1` with `S`-colored forests, since `γ S ⊆ S` in `lem:Relations`(7);
  - joins of `S`-brick partitions;
  - elementary core and contractibility;
  - `Stab = h^{-1}𝒢(m)h ≅ G ≀ Σ_m`, since twisted permutations are `S`-colored;
  - `lem:stab_spectrum`, where `Stab_G(C)` for `C ⊆ S` is the same for `S` and for `S'`;
  - the descending-link analysis, where merge labels are the `G`-orbits of `(s, a, b)` with
    `s ∈ S`. These are nonempty and need no faithfulness on `S`.

  **PASS.**
- **(2b), finite presentation (Step 3).** For `d ≥ 2`, `∂I = Σ|(v,w)|` is connected. `|I|` is the
  cone on `∂I`, and different intervals of length `d` meet only in `F_{d−1}`. So van Kampen kills
  exactly the images of `π_1(∂I)`: nontrivial only for grid intervals with `e = 2`, where it is `Z`.
  - I checked the hexagon `v → x_r → x_r b(h) → w → x_b r(h') → x_b → v`. It lies in `∂I`, passes
    once through each of the two cone components of `(v,w)`, and consists of short edges.
  - Brown's hypotheses hold under `[A_2]`: fp vertex stabilizers, fg short-edge stabilizers
    `≈ Stab_G(s) × G^{r−1}`, finitely many cell orbits, and a rigid action.
  - **PASS.**
- **The FFWZ gap is genuine.** FFWZ Lemma 4.9(i) (l.943) asserts that the stabilizer in `SV_G` of a
  vertex of `SX_{G/K}` is conjugate to `W(n) ≅ Σ_n ⋉ G^n`. The proof says "all the results are
  immediate from the faithful case" (l.987). But that stabilizer is the full preimage of `W(n)` of
  `SV_{G/K}`, so it contains the canonical kernel `SK_G`.
  - For `k ∈ K∖1`, the element `[x_s, id, (k,1), x_s] ∈ SK_G` acts in the realization as `τ_k` on
    one half and the identity on the other. It is not a twisted permutation.
  - So Props 4.10 and 4.12 and Cor 4.14 (hence Theorem 4.1(ii), (iii) and Cor 4.19) are not proved
    for non-faithful actions as written.
  - Node (2b) restores them.
- **Note (not a gap).** The necessity half, FFWZ Prop 4.17 (l.1107–1165), uses germinal twists in
  `G` although it says "via the quotient", which only sees `G/K`. The label of the leaf containing
  `κ` is well-defined in `G`: in the realization (2a) it is the germinal twist in `S'V_G`. So
  necessity stands, and it is best cited together with (2a).

## 4. W1: BZ `lem:VE_conn` (l.760–770) has two errors, not one

Both items rest on `X_m` being highly connected. That comes from FFWZ Prop 4.8(ii) (l.906–918) ←
BZ `prop:E_hi_conn` (l.856–862) ← BZ `lem:VE_conn`.

- **Error 1 (recorded on the nodes).** "VE_m^{i,j} is the union of the stars of its rank-(m−1)
  vertices that match i and j" misses the vertices that avoid `i` and `j`. Correct: `VE_m^{i,j}`
  is the join `|A_{ij}| * |VE_{m−2}|`, where `A_{ij}` is the set of labelled merges of `i, j`.
- **Error 2 (not recorded).** "VE_m^{i_1,j_1},…,VE_m^{i_r,j_r} have non-empty intersection if and
  only if the sets {i_1,j_1},…,{i_r,j_r} are pairwise disjoint" is **false** for `m ≥ 5`.
  - The vertex merging leaves 4 and 5 lies in both `VE_5^{1,2}` and `VE_5^{1,3}`.
  - So the nerve is strictly larger than the matching complex of `K_m`.
  - The nodes' sentence "the intersections are joins too" is false for non-disjoint families: those
    intersections are complexes on the complementary leaves.
  - So BZ's Nerve-Lemma computation, and the recorded fix, do not prove the lemma.
- **Repair (the conclusion holds).**
  - `VE_m` is the order complex of the poset of nonempty labelled matchings of `[m]`. A vertex is a
    set of merged pairs, each carrying a label (a `G`-orbit of `(color, twist, twist)`), and
    `v ≤ v'` iff the matching of `v'` is contained in that of `v`.
  - So `VE_m` is homeomorphic to the matching complex `M_L(K_m)` of the complete multigraph. Every
    label set is nonempty.
  - The projection `M_L(K_m) → M(K_m)` is a complete join complex: surjective, injective on
    simplices, with fibers over a simplex equal to joins.
  - `M(K_m)` is weakly Cohen–Macaulay of dimension `ν(m) = ⌊(m−2)/3⌋`. It is `(ν(m)−1)`-connected
    (Björner–Lovász–Vrećica–Živaljević, Thm 4.1, as BZ cite), and the link of a `p`-simplex is
    `M(K_{m−2p−2})`, with `ν(m) − ν(m−2p−2) ≤ ⌈(2p+2)/3⌉ ≤ p+1`.
  - Hatcher–Wahl (Duke Math. J. 2010, Prop. 3.5; recalled, not re-read) then make `M_L(K_m)` wCM of
    the same dimension. So `VE_m` is `(ν(m)−1)`-connected, as BZ claim.
- The rest of `prop:E_hi_conn` (merge link ≅ `VE_{μ_1}`; the split-link lemmas, which the
  grid-sphere lemma reproves) is fine.

**Required fix.** Replace the "N1 join" sentence in `twisted-bt-type-fn-interval-filtration-proof`
Step 1 and `abstract-twisted-bt-type-fn-colored-stein-proof` Step 1 by the labelled-matching /
complete-join argument above. Error 2 is also an error in the published BZ proof; its conclusion is
unaffected.

## 5. Literature check (bounded)

I ran arXiv API searches: `abs:twisted AND abs:Brin`, 40 results sorted by date, and
`all:"Brin-Thompson" AND all:finiteness`. The latest relevant entries are FFWZ 2603.24687 (Mar 2026),
2510.16879 (acyclic groups, which uses BZ's sufficient theorem), and 2506.02319 (obstructions for
oligomorphic stabilizers). None proves Conjecture H or the FFWZ conjecture, and FFWZ v2 records both
as open. MathSciNet was not searched.

## 6. Nits

- The node's "Referee c PASS" status lines refer to earlier reports. This report is an additional
  independent pass and agrees with them, except for W1.
- `lem:all_big`'s "equals the star of the join" is imprecise (see §2). It is not needed.

## Lesson for general BH

The Stein-complex obstruction "bad simplex stabilizers" was an artifact of the cell structure:
filtering by intervals and computing local homology puts each stabilizer in exactly the degree its
colors count. Every descending-link input should be rechecked at the level of the actual poset,
since published nerve arguments can overcount intersections. Here the fix is to recognize a labelled
matching complex, a complete join over `M(K_m)`.
