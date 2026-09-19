---
rg: 2
id: v-times-subshift-full-group-finiteness-is-horizontal
kind: claim
title: For V times any topologically free subshift over a finitely generated group, descending links of the domain-filtered Stein space are highly connected in every degree, so type F_n is exactly essential (n−1)-connectivity of the domain filtration and P2′ and E3′ are purely the horizontal condition (A_N)
distinct_from:
  v-times-quantum-rigid-sft-full-groups-are-fp: that is P2′. Its Attempt 1 set up the domain filtration, left the descending-link step (B_N) unchecked and used only the "if" direction; this proves (B_N) in every degree and makes the reduction to (A_N) an equivalence.
  v-times-rigid-topologically-free-sft-full-groups-are-fp: that is the open gate E3′; this reduces it, and every F_n analogue of it, exactly to essential connectivity of the domain filtration.
  cuntz-stabilized-garside-full-groups-are-f-infinity: that is the finite-type (Garside) case, where Cuntz stabilization supplies Li's packing; this is the infinite-type case, where stabilization supplies packing at every domain level and all remaining finiteness is horizontal.
  thumann-finiteness-without-finite-type: that runs Thumann's corona-from-core estimate for operads with a calculus of fractions; here the domain levels have no calculus of fractions, and the same estimate is used level by level, where block sizes are bounded, so its condition (G) holds vacuously.
---

**ESTABLISHED** (lane proof, bh-invent-17, 2026-09-18; not independently reviewed; no priority
claimed). This closes the descending-link step (B_N) of P2′ Attempt 1 in every degree.
Imported inputs:
- Brown's criterion with its converse (K. Brown, *Finiteness properties of groups*, JPAA 44
  (1987), Thms 2.2 and 3.2);
- the Bestvina–Brady Morse lemma;
- the Hatcher–Vogtmann bad-simplex lemma (*Tethers and homology stability for surfaces*,
  Prop. 2.1);
- Walker's product formula for open intervals of bounded posets;
- the ordered matching complex bound already used in `twisted-bt-type-fn-interval-filtration-proof`;
- the corona-from-core estimate of `thumann-finiteness-without-finite-type`, reproved below.

## Setting

- `Λ` is finitely generated, with balls `B_N`.
- `X ⊆ A^Λ` is any subshift on which `Λ` acts topologically freely. No minimality, finite type
  or rigidity is assumed.
- `F = F(G_V × (Λ ⋉ X))`, acting on `C × X`.
- A **formal cone** is `c = (u, F_c, π)`: a word `u`, a nonempty finite `F_c ⊂ Λ`, and a pattern
  `π` on `F_c` that occurs in `X`. Its set is `[u] × [π]`.
- There are two **elementary splits**:
  - the C-split `(u,F,π) → (u0,F,π), (u1,F,π)`;
  - the X-split at `g ∉ F`, into all occurring extensions of `π` to `F ∪ {g}` (possibly a
    single one).
- A **joint split** of `c` along a set `J` of directions (C and/or sites) is their common
  refinement.
- A cone's **type** is its translation class `(F, π)`. Level `N` allows `F` inside a translate
  of `B_N`. `T_N` is the number of level-`N` types, and `β_N = 2|A|^{|B_N|}` bounds the size of
  a level-`N` joint split.
- `𝒫` is the standard Stein poset: labelled formal partitions `[g, P]` of the root, with
  `[g,P] = [gσ, σ^{-1}P]` when `σ` maps pieces to pieces by canonical similarities (prefix
  replacement times translation), ordered by reachability through elementary splits.
- The **height** is `h = Σ_i |F_i|`, which increases strictly along every split. `𝒫^(N)` is the
  full subposet of level-`N` partitions.

## Statement

1. **The engine.**
   - `|𝒫|` is contractible and `F` acts with finite cell stabilizers.
   - Every height-sublevel of `𝒫^(N)` is `F`-cocompact.
   - `𝒫^(N)` is closed under intervals.
   - In each level, `|𝒫^(N)|` deformation retracts onto the Stein space `𝔛^(N)`, the chains whose
     top is a joint-split expansion of their bottom.
2. **(B_N) in every degree.** Let `κ_m = (3m+7)·T_N`. At a vertex with `k` pieces, the descending
   link of `𝔛^(N)` is `(n−2)`-connected as soon as `k ≥ max(κ_{n−2}, (n−1)β_N + κ_{n−3})`.
   Since `k ≥ h/|B_N|`, this holds above a height depending only on `n` and `N`.
3. **Exactness.** For every `n ≤ ∞`:
   - `F` is of type `F_n` iff the domain filtration `{|𝒫^(N)|}_N` is essentially
     `(n−1)`-connected;
   - `F` is of type `FP_n` iff it is essentially `(n−1)`-acyclic.

   In particular, `F` is finitely presented iff for every `N` there is `N' ≥ N` such that every
   loop in `|𝒫^(N)|` bounds in `|𝒫^(N')|`. That is the essential form of Attempt 1's (A_N).

## Proof

**1a. Swap lemma.** Suppose a cone partition `R` of `c` is reachable from `c`, and every piece of
`R` has site `g` in its domain (resp. a prefix longer than `u`). Then `R` is reachable from the
X-split of `c` at `g` (resp. from the C-split).

Induct on the number of splits. If the first split is not the one wanted, apply induction to
each of its pieces and swap the two consecutive splits: "at `g'`, then at `g`" and "at `g`, then
at `g'`" give the same formal cones, and C-splits commute with X-splits. With no splits, the
hypothesis cannot hold.

**1b. Unique maximal expansion.** For `Q < P`, let `Q̂_P` split each piece `q` of `Q` jointly
along:
- C, if every `P`-piece in `q` has a longer prefix;
- every site of `∩_{p ⊆ q} F_p \ F_q`, a finite set.

By 1a, `Q̂_P ≤ P`. It contains every joint-split expansion of `Q` below `P`. Its domains lie in
the `F_p`, so it stays in level `N`. Intervals also stay in level `N`, since domains only grow.
Stein's argument now applies:
- for `P` not an elementary expansion of `Q`, the map `R ↦ Q̂_R` is a conical contraction
  `R ≥ Q̂_R ≤ Q̂_P` of the open interval `(Q, P)`;
- so gluing the non-elementary intervals in order of length does not change the homotopy type.

**1c. Other clauses.**
- *Contractibility.* `𝒫` is directed. Every element of `F` is canonical on the pieces of some
  formal partition, and a set-wise refinement becomes a formal one after adding forced sites.
- *Finite stabilizers.* A canonical similarity `(u, F, π) → (u', F', π')` has `λF = F'`, which
  leaves finitely many `λ`. Topological freeness makes the label unique.
- *Cocompactness.* Vertex orbits correspond to multisets of types.

**2a. Descending links are block posets.** The descending link of `P` in `𝔛^(N)` is the order
complex of the poset `E(P)` of nonempty systems of disjoint **blocks**, ordered by reachability.
A block is a set of pieces of `P` that is the joint split of a formal cone.
- Coarsenings of an elementary partition are elementary: a piece of an intermediate partition
  contains exactly the atoms of its own joint split. So `E(P)` is the whole descending link.
- A block is **minimal** if it is a single elementary split. That is either a C-pair (an ordered
  pair of same-type pieces), or all extensions at one site.
- Minimal blocks have no proper sub-blocks.

**2b. Core.** Let `L(P)` be the flag complex of pairwise disjoint minimal blocks.
`E_min(P)` is its face poset, and `L(P)` is `m`-connected when `k ≥ κ_m`, by the following
argument.
- **C-merges.** The C-merge subcomplex `L_C` is a join over types of ordered matching complexes.
  Each is a complete join over `M(K_q)`, hence `(⌊(q+1)/3⌋ − 2)`-connected. Some type has at least
  `k/T_N` pieces.
- **Bad simplices.** Call the nonempty all-X-merge simplices bad. For a bad `σ` with `s`
  vertices, the good link is the C-merge complex on the at least `k − 2sT_N` pieces outside
  `supp σ`. Here a minimal X-block has at most `T_N` pieces, at most one per occurring symbol.
- **Arithmetic.** It remains to check that `k ≥ κ_m` makes this good link `(m+1−s)`-connected and
  `L_C` `m`-connected. Then Hatcher–Vogtmann applies.

**2c. Corona from core.** Attach the elements of `E(P) \ E_min(P)` in increasing order of
`f(Q) = (number of non-minimal blocks of each size, largest size first; then the piece count)`,
compared lexicographically. Elements with equal `f` are incomparable.

When `Q` is attached, the comparable elements already present are exactly two sets. Both
characterizations follow by comparing `f` at the largest block size that changes.
- `U`: the refinements of `Q` that refine at least one non-minimal block.
- `W`: the systems `Q + σ` with `σ` a nonempty set of minimal blocks on the untouched pieces.

So the attaching link is the join `U * W`, with `|W| ≃ L(untouched pieces)`.
- **Mixed `Q`** (some minimal block `μ`). The map "keep `μ`" gives a conical contraction of `U`:
  `x ≥ h(x) ≤ c`, where `c` releases everything except `μ`. So the link is contractible.
- **Pure `Q`** (non-minimal blocks `θ_1, …, θ_𝔫` and `𝔩` untouched pieces).
  - `U` is the open interval of `∏_i [θ_i, released]`. By Walker it is an `(𝔫−1)`-fold suspension of the join
    of the splitting posets `(θ_i, released)`.
  - Each splitting poset is nonempty: split along one direction `j ∈ J` first, then jointly along
    `J \ j`.
  - So `conn U ≥ 𝔫 − 2`, and `conn(U * W) ≥ 𝔫 + conn W`.
  - If `𝔫 ≥ n` this is at least `n − 2`.
  - Otherwise `𝔩 ≥ k − (n−1)β_N ≥ κ_{n−3}`, so `conn W ≥ n − 3` and `conn ≥ 1 + n − 3`.

All attaching links are therefore `(n−2)`-connected, so `E(P)` has the `(n−2)`-type of
`E_min(P) ≅ sd L(P)`, which is `(n−2)`-connected. This is Thumann's estimate. Block sizes are
bounded by `β_N` in each level, so his splitting condition (G) is vacuous here.

**3. Exactness.**
- Put `X_N = 𝔛^(N)_{h ≤ H_N}`, with `H_N` chosen by clause 2 so that descending links above it
  are `(N−1)`-connected.
- The `X_N` are cocompact, with finite stabilizers, and exhaust the contractible `𝔛 ≃ |𝒫|`. So
  Brown's criterion and its converse say: `F` is `F_n` iff `{X_N}` is essentially
  `(n−1)`-connected.
- By Bestvina–Brady, `X_N ↪ 𝔛^(N)` is `N`-connected, so `π_i(X_N) ≅ π_i(|𝒫^(N)|)` for `i < N`.
  Essential connectivity is therefore the same for the two filtrations.
- The homological statement is identical. `∎`

## What this does for the gates

- **Rigidity enters only horizontally.** Descending links never obstruct finiteness, in any
  degree, for any topologically free subshift, rigid or not.
  - So E3′ (`v-times-rigid-topologically-free-sft-full-groups-are-fp`) is exactly: *for a quantum
    rigid SFT, loops of `|𝒫^(N)|` die in `|𝒫^(N')|`.*
  - P2′ is the same statement for free `X`.
  - The necessity theorem (`topologically-free-subshift-full-groups-force-quantum-rigidity`) says
    that this horizontal condition forces quantum rigidity and finite type. By
    `quantum-family-representations-are-exhausted-at-rigidity`, rigidity is its linear shadow.
- **Higher finiteness is free of new local conditions.** The `F_∞` question is the same filtration
  in all degrees. No further packing, Perron or thin-cycle condition can arise. This complements
  `cuntz-stabilized-garside-full-groups-are-f-infinity` beyond finite type.
- **Test cases have no new link obstruction.** The fold and Busemann scaffolds, and Labbé's shift
  (with (A_N) and `J_D = 0` still open), carry no descending-link obstruction.

## Lesson for general BH

In a Cuntz-stabilized full group, finiteness has only one direction left, and it is horizontal.
Stabilization turns every cone type into a V-colour, so merges of equal types are always
available. Thumann's corona-from-core estimate then makes descending links highly connected at
every domain level, in every degree, with no SFT condition at all.

What remains is whether loops made at a bounded domain radius can be filled at a larger but
still bounded radius. Rigidity is the linear shadow of exactly this statement, and the ring side
proves its algebraic version. So the group-side master-route gate (E3′/P2′) is a single
local-to-global filling problem for cone partitions: nothing about links, packing or heights
remains open.

## Referee (bh-ref-kourovka-a, 2026-09-18): PASS, with three presentation fixes

I checked the proof line by line: 1a–1c, 2a–2c and 3, at its current version (after 5e00ad7ce).

- **1a–1c.**
  - The swap lemma's induction is correct: X-splits at distinct sites commute, and C-splits commute
    with X-splits.
  - For 1b, `Q̂_P ≤ P` follows from 1a, and levels are preserved because domains only grow. Stein's
    conical contraction then applies.
  - Stabilizers are finite: finitely many `λ` have `λF = F'`, and topological freeness makes the map
    determined by its formal data.
  - Height increases strictly along every split.
- **2b.**
  - `L_C` is `(⌊(k/T_N + 1)/3⌋ − 2)`-connected, since some type has at least `k/T_N` pieces and the
    connectivity is that of the ordered matching complex.
  - Hatcher–Vogtmann applies with "bad" meaning all vertices are X-merges. Condition (i) holds
    because a simplex with no bad face lies in `L_C`, and (ii) holds because unions of bad faces
    are bad.
  - The good link of a bad `σ` is the C-merge complex off `supp σ`.
  - **The arithmetic the node leaves "to check" holds.** With `k >= (3m+7)T_N`, `L_C` is
    `m`-connected. For every `s >= 1`, the good link on `>= k − 2sT_N` pieces is `(m+1−s)`-connected,
    because `⌊(3m+8−2s)/3⌋ >= m+3−s` exactly when `s >= 1`. The vacuous range `s >= m+3` and the
    nonemptiness case `s = m+2` are both fine.
- **2c.**
  - The comparable elements already present are exactly `U ∪ W`. `f` drops under refining a
    non-minimal block and under adding minimal blocks; releasing only minimal blocks raises the
    piece count. Every `u ∈ U` is comparable to every `w ∈ W` through `Q`.
  - The mixed case contracts via `x ≥ h(x) ≤ c`, and `h(x)` stays in `U`.
  - In the pure case, Walker gives `conn U >= 𝔫 − 2`, and `W ≃ L(untouched)`. The counts
    `𝔩 >= k − (n−1)β_N` hold.
- **3.** Brown's criterion with its converse and the Bestvina–Brady Morse lemma apply. The
  `N`-connected inclusion identifies essential connectivity of the two filtrations.

**Fixes (presentation; none changes the result).**
1. **Blocks carry their parent cone.** An X-split at a forced site gives a single-piece block
   `{p}` whose parent has a smaller domain. The same set of pieces can be the joint split of
   different formal cones. So `E(P)` should be systems of (block, parent) pairs.
   - With that reading, every step holds.
   - In particular, the splitting posets `(θ_i, released)` in 2c are nonempty: split first along a
     direction that is non-forced for the parent, and the intermediate may consist of single-piece
     blocks with smaller parents.
   - Read as bare sets of pieces, those intervals can be empty.
2. **Degree 0.** "In particular, `F` is finitely presented iff every loop in `|𝒫^(N)|` bounds in
   `|𝒫^(N')|`" omits essential 0-connectivity. Level-`N` partitions need not have common
   refinements inside level `N`, so `|𝒫^(N)|` need not be connected. Type `F_2` is essential
   `1`-connectivity, which includes the `π_0` condition, equivalently `F` finitely generated.
3. **The arithmetic.** The Hatcher–Vogtmann arithmetic in 2b is verified above; the phrase "it
   remains to check" can be dropped.

**Not checked.** The "What this does for the gates" bullets, which cite other lane nodes.
