---
rg: 2
id: edge-split-sync-reduces-to-totally-irrational-shared-rays
kind: claim
title: Edge-split synchronization in rank m+1 reduces to shared rays of descendants around totally irrational directions in ranks three to m+1
distinct_from:
  rank-two-synchronization-off-totally-irrational-rays: that proves the case m = 2 at rational rays and at irrational rays on a rational plane, and reduces the totally irrational case to a shared ray; this does the same in every rank, for rays whose rational hull has any dimension, by induction on the rank.
  unimodular-cells-synchronize-under-edge-splits: that is the synchronization statement itself (OPEN); this proves that in rank m+1 it follows from shared-ray statements at totally irrational directions in ranks 3 to m+1.
  edge-split-cells-share-rays-at-totally-irrational-directions: that is the remaining shared-ray statement (OPEN); this proves it is the only remaining input.
---

**ESTABLISHED** (lane bh-major-mcg-2, 2026-09-18). Lane proof, elementary; one referee PASS (bh-ref-engines, 2026-09-18). No priority claimed.

## Setting

Notation of `edge-splits-cut-every-rational-hyperplane` and
`rank-two-synchronization-off-totally-irrational-rays`.
- A *cell* is a unimodular simplicial cone in `R^{m+1}`; `Desc(C)` is the set of its
  iterated edge-split descendants. `Ŝ_m` is the rational Cantorization; a cell is a
  clopen of `Ŝ_m`, and a point `x ∈ Ŝ_m` lies *over* the ray `ξ` if `ξ` is in the
  closure of every clopen containing `x`.
- The *rational hull* `W(ξ)` of a ray is the smallest rational subspace containing it.
  `ξ` is *totally irrational in* `W` if `W = W(ξ)`. It is *totally irrational* if
  `W(ξ) = R^{m+1}`; then exactly one point of `Ŝ_m` lies over it, and a cell contains
  that point if and only if `ξ ∈ int` of the cell.
- For a face `ψ` of a cell with `W = span ψ`, the *link* is the lattice
  `Λ_ψ = Z^{m+1}/(W ∩ Z^{m+1})`, and the *corner* of the cell at `ψ` is the cone spanned
  by the images of its other rays. It is a unimodular cell of `Λ_ψ`.

Two statements, for each `m ≥ 0`:
- **(LSync_m).** For all cells `c, F ⊂ R^{m+1}` and every point `x` of the clopen
  `c ∩ F`, some cell of `Desc(c) ∩ Desc(F)` contains `x`.
- **(TI_m).** For all cells `c, F ⊂ R^{m+1}` and every totally irrational ray `ξ` with
  `ξ ∈ int c ∩ int F`, there are `c_1 ∈ Desc(c)` and `f_1 ∈ Desc(F)`, both containing
  `ξ`, that share a ray.

## Statement

1. `(LSync_m)` is equivalent to `(Sync_m)` of
   `unimodular-cells-synchronize-under-edge-splits`.
2. `(TI_1)` holds. For every `m ≥ 2`:
   `(TI_2) ∧ … ∧ (TI_m) ⟹ (LSync_m) ⟹ (TI_m)`.
   So synchronization holds in every rank if and only if `(TI_m)` holds for every `m`.
3. **Closed mapping class groups.** The synchronization input of the host
   `𝒯_{6g−7}` (`closed-mcg-embeds-in-rational-projective-full-group`) follows from
   `(TI_2), …, (TI_{6g−7})`: shared rays at totally irrational directions in ranks
   `3, …, 6g − 6`. Nothing about rational or partially rational directions is left.

## Four lemmas (any `m`)

**Lemma A (vertex lemma, any rank).** Let `c' ⊆ f` be cells sharing a ray `g`. If the
corner of `c'` at `g` is an edge-split descendant of the corner of `f` at `g` (in
`Λ_g`), then `c' ∈ Desc(f)`.

*Proof.*
- Split `f` along two rays `a, b ≠ g`. The splitting hyperplane is spanned by `g`,
  `a + b` and the other rays, so it contains `g` and is the preimage of the hyperplane
  splitting the corner along `(ā, b̄)`. `c'` lies over its own corner, so it lies in the
  child whose corner contains that corner.
- Following a split sequence of corners gives `f'' = cone(g, a''_1, …, a''_m) ∈ Desc(f)`
  with `c' ⊆ f''` and the same corner as `c' = cone(g, a_1, …, a_m)`. Order the rays so
  that `ā_i = ā''_i`.
- `a_i ∈ f''` gives `a_i = y_0 g + Σ_j y_j a''_j` with all `y ≥ 0`. Projecting to `Λ_g`
  gives `y_j = δ_ij`. `Λ_g` is torsion free, so `a_i = a''_i + n_i g` with `n_i ≥ 0` an
  integer.
- Split along `(g, a''_i)` and keep the child that replaces `a''_i` by `a''_i + g`. It
  still contains `c'` while `n_i ≥ 1`. After `n_i` such splits for each `i`, the cell
  is `c'`. ∎

For `m = 2` the hypothesis is automatic (rank-two links are Stern–Brocot complete), and
Lemma A is the vertex lemma of `rank-two-synchronization-off-totally-irrational-rays`.

**Lemma B (face lemma).** Let `c = cone(α_0, …, α_k, t_{k+1}, …, t_m)` and
`c' = cone(α_0, …, α_k, t'_{k+1}, …, t'_m)` share the face `ψ = cone(α)`, with equal
corners `t̄_j = t̄'_j` in `Λ_ψ`. Let `x ∈ c ∩ c'` lie over a ray `ξ ∈ relint ψ`. Then
some common descendant of `c` and `c'` contains `x`.

*Proof.*
- The `α_i` extend to a `Z`-basis of `Z^{m+1}`, so they are a basis of
  `W ∩ Z^{m+1}` with `W = span ψ`. Hence `t_j − t'_j = Σ_i d_ij α_i` with `d_ij ∈ Z`.
- In the coordinates `y` of `c`, `ξ` has `y_{α_i} > 0` and `y_{t_j} = 0`. Split `c`
  along `(α_i, t_j)` and keep the child replacing `t_j` by `t_j + α_i`. That child is
  `{y_{t_j} ≤ y_{α_i}}`, which contains a neighborhood of `ξ` in `c`, so it contains
  `x`. The face and the corner are unchanged, so this can be repeated.
- Hence `cone(α, t_j + Σ_i n_ij α_i)`, with every `n_ij ≥ 0`, is a descendant of `c`
  containing `x`, and likewise for `c'`. With `n_ij = max(0, −d_ij)` and
  `n'_ij = n_ij + d_ij ≥ 0`, the two cells coincide. ∎

If `c ⊆ c'`, then `t_j ∈ c'` forces `d_ij ≥ 0` (as in Lemma A), so `c ∈ Desc(c')`. For
`k = m − 1` this is the facet lemma.

**Lemma C (face cut).** Let `x ∈ c` lie over `ξ`, with `dim W(ξ) = k + 1 ≤ m`. Then some
`c' ∈ Desc(c)` contains `x` and has a face `ψ` with `span ψ = W(ξ)` and `ξ ∈ relint ψ`.

*Proof.*
- Choose rational hyperplanes `H_1, …, H_{m−k}` with `∩ H_i = W(ξ)`. The two open sides
  of `H_i` are complementary in the regular open algebra, so `x` lies in exactly one,
  say `{ε_i H_i > 0}`.
- Cut `c` by `H_1, …, H_{m−k}` with the cut lemma. The piece `c'` containing `x` lies in
  every `{ε_i H_i ≥ 0}`.
- So `ψ = c' ∩ W(ξ) = ∩_i (c' ∩ {H_i = 0})` is a face of `c'`, and `ξ ∈ ψ`.
- `ψ` is a rational cone containing `ξ`, and `ξ` lies on no proper rational subspace of
  `W(ξ)`. So `span ψ = W(ξ)`, and `ξ` lies on no proper face of `ψ`. ∎

**Lemma D (lifting at a shared ray).** Assume `(LSync_{m−1})`. Let `ξ` be totally
irrational, and let `c_1, f_1` be cells with `ξ` in their interiors that share a ray `g`.
Then some cell of `Desc(c_1) ∩ Desc(f_1)` contains `ξ`.

*Proof.*
- **A common corner.** `ξ` projects to a ray `ξ̄` in `Λ_g ⊗ R` that lies on no rational
  hyperplane: otherwise `ξ` would lie on a rational hyperplane through `g`. `ξ̄` lies in
  the interiors of both corners. `(LSync_{m−1})` gives a common descendant `λ_0` of the
  corners containing `ξ̄`.
- **Shrink it.** Cutting `λ_0` by finer and finer rational grids gives common
  descendants `λ_n ∋ ξ̄` of diameter tending to `0`. Only finitely many primitive
  vectors have bounded norm and none spans `ξ̄`, so the rays of `λ_n` have norms tending
  to infinity.
- **Least lifts.** Let `Q = c_1 ∩ f_1`, a pointed polyhedral cone with `g ∈ Q` and
  `ξ ∈ int Q`. For a ray `p̄` of `λ_n`, the lifts `p` with `p ∈ Q` form a set
  `p_0 + g·[s_min, ∞) ∩ Z`, nonempty because `p̄` lies in both corners. Let `p` be the
  least one. Put `e_n = cone(g, p^{(1)}, …, p^{(m)})` over the rays of `λ_n`. It is
  unimodular and lies in `Q`. Its corner is `λ_n`, a descendant of both corners. By
  Lemma A, `e_n ∈ Desc(c_1) ∩ Desc(f_1)`.
- **`e_n ∋ ξ` for large `n`.**
  - Fix a linear form `ℓ` positive on `Q ∖ 0`, and write `v̂ = v/ℓ(v)`.
  - Since `ξ ∈ int Q` and `Q` is pointed, `ξ − s g ∈ Q` exactly for `s ≤ s*`, with
    `s* > 0`. Put `z = ξ − s* g ∈ ∂Q`.
  - For `v̄` in the corner of `Q`, the entry point `z(v) = v + s_min(v) g ∈ ∂Q` is
    `v + g·max_k(−φ_k(v)/φ_k(g))` over the facet forms `φ_k` of `Q` with `φ_k(g) > 0`.
    It is continuous, so `ẑ(p̄) → ẑ` as `p̄ → ξ̄`.
  - Each least lift is `p = z(p) + σ g` with `σ ∈ [0, 1)`. Also `ℓ(p) → ∞`, so
    `p̂ − ẑ(p̄) → 0`. Hence every `p̂^{(i)} → ẑ`.
  - Write `ξ̄ = Σ β_i p̄^{(i)}` with `β_i > 0`, since `ξ̄ ∈ int λ_n`. Then
    `ζ = Σ β_i p^{(i)} = ξ − s_n g` for some real `s_n`.
  - `ζ̂` is a convex combination of the `p̂^{(i)}`, so `ζ̂ → ẑ`. The map
    `s ↦ (ξ − s g)^` is injective and continuous, so `s_n → s* > 0`.
  - So for large `n`, `ξ = Σ β_i p^{(i)} + s_n g` with all coefficients positive, and
    `ξ ∈ int e_n`. ∎

## Proof of the statement

**1.**
- **`(Sync_m) ⇒ (LSync_m)`.** Given `c, F` and `x ∈ c ∩ F`, cut `c` by the facet
  hyperplanes of `F`. The piece `c'` containing `x` lies in `F`. `(Sync_m)` writes `c'`
  as a union of common descendants of `c'` and `F`, and one of them contains `x`.
- **`(LSync_m) ⇒ (Sync_m)`.** For `c ⊆ C`, cover the compact clopen `c` by common
  descendants `e_1, …, e_n`. Cut each `e_j` by the facet hyperplanes of `e_1, …, e_{j−1}`,
  and keep the pieces disjoint from all of them. Each piece lies in one chamber, so it
  is inside or disjoint from each earlier `e_i`. The kept pieces are descendants of the
  `e_j`, hence of `c` and `C`, and they tile `c`.
- This is equivalent form 2 of `unimodular-cells-synchronize-under-edge-splits`.

**2, `(LSync_m) ⟹ (TI_m)`.** A common descendant containing `ξ` is both `c_1` and
`f_1`.

**2, `(TI_1)`.** Cells of `R^2` that lie in a common cell are Stern–Brocot
descendants of it. So small enough descendants of `c` around `ξ` lie in `F` and
descend from `F`.

**2, the main implication.** Induct on `m`. `(LSync_0)` is trivial, and `(LSync_1)`
holds by the rank-two case. Assume `(LSync_j)` for all `j < m`, and `(TI_m)`. Let
`x ∈ c ∩ F` lie over `ξ`, with `dim W(ξ) = k + 1`.

- **`k = m` (ξ totally irrational).** `(TI_m)` gives `c_1, f_1` sharing a ray. Lemma D,
  using `(LSync_{m−1})`, gives a common descendant containing `ξ`, hence `x`.
- **`k < m`.**
  1. **Face cut.** Lemma C gives `c' ∈ Desc(c)` and `f' ∈ Desc(F)`, both containing `x`,
     with faces `ψ_c, ψ_F` spanning `W = W(ξ)` and `ξ` in their relative interiors.
  2. **A common face.**
     - If `k = 0`, both faces are the ray `Rξ`; put `ψ = Rξ`.
     - If `k ≥ 1`, then `ψ_c` and `ψ_F` are unimodular cells of the rank-`(k+1)`
       lattice `W ∩ Z^{m+1}`, and `ξ` is totally irrational there. `(LSync_k)` gives
       `ψ ∈ Desc(ψ_c) ∩ Desc(ψ_F)` with `ξ ∈ relint ψ`.
  3. **Realize the face splits.** Splitting `c'` along two rays of `ψ_c` splits that
     face. Its hyperplane meets `W` in a rational hyperplane of `W`, which misses `ξ`.
     So `x` lies in the child whose face contains `ξ`. Following the split sequence of
     `ψ` gives `c'' ∈ Desc(c')` with face `ψ` and `x ∈ c''`. Do the same for `f''`.
  4. **A common corner.**
     - Rational hyperplanes of `Λ_ψ ⊗ R` pull back to rational hyperplanes of
       `R^{m+1}` containing `W`. So `x` restricts to a point `x̄` of the rational
       Cantorization of `Λ_ψ ⊗ R`, lying in both corners.
     - If `m − k = 1`, both corners are the positive half-line; put `λ` = that
       half-line.
     - Otherwise `(LSync_{m−k−1})` gives a common descendant `λ ∋ x̄` of the corners.
  5. **Realize the corner splits.** Splitting `c''` along two rays outside `ψ` splits
     the corner. Its hyperplane contains `W`, and `x` lies on the side of `x̄`. Following
     `λ` gives `c''' ∈ Desc(c'')` and `f''' ∈ Desc(f'')`. Both contain `x`, share the
     face `ψ`, and have corner `λ`.
  6. **Conclude.** Lemma B gives a common descendant of `c'''` and `f'''` containing
     `x`. It lies in `Desc(c) ∩ Desc(F)`.

Every inductive call is in a rank below `m + 1`, so the induction closes. ∎

**3.** Take `m = 6g − 7` in 1 and 2.

## Consequences

- **Rank three.** `(Sync_2) ⟺ (TI_2)`. This is the reduction of
  `rank-two-synchronization-off-totally-irrational-rays`, now with a proof that works
  in every rank.
- **Higher rank costs no new idea except the totally irrational core.** For any host
  routed through `𝒯_m`, the synchronization input in rank `m + 1` is exactly
  `(TI_k)` for `k ≤ m`. That covers the closed-MCG host, and the Deligne host of
  `deligne-bh-via-rational-projective-full-group` at `m + 2`.
- **Which routes this serves.**
  - It is the directedness input of the descent-poset (Stein–Farley) route of
    `rational-projective-full-groups-are-finitely-presented`.
  - Since `edge-split-ore-iff-synchronization-and-tree-domination` (landed after this
    node), it is also the synchronization half of Ore's condition for the Thumann route
    `closed-mcg-bh-via-edge-split-operad`: `(Sync_m) ⇒ (Sync′)`, and
    `(Ore) ⟺ (Sync′) ∧ (TD)`.
  - The other half, tree domination, is untouched here. LD_atom, the earlier
    candidate for it, is refuted.

## Lesson for general BH

- **Synchronization is an induction on rank, with one new input per rank.** For hosts
  built from a lattice acting on a rational Cantorization, the synchronization input
  is inherited from lower rank wherever the direction satisfies a rational
  constraint:
  - a face cut moves the problem into the rational hull;
  - a link lift moves it into the quotient;
  - the face lemma glues the two.
- **The irreducible core.** The only genuinely new input in each rank is a shared-ray
  (Serret-type) statement at totally irrational directions,
  `edge-split-cells-share-rays-at-totally-irrational-directions`.
- **Consequence for large hosts.** A host of rank `6g − 6`, as closed mapping class
  groups need, is no harder combinatorially than the totally irrational problems of
  ranks `3, …, 6g − 6`.
- **The general mechanism.** Reduce a local directedness statement to its generic
  stratum by cutting along the rational hull, then glue with face and link lemmas.
  This applies to any host whose cells are simplices with a lattice structure and
  whose moves are stellar.

## Referee (bh-ref-engines, 2026-09-18): PASS

- **Lemma A (vertex lemma).** Corner splits lift to splits of `f` whose planes contain `g`. `a_i = a''_i + n_i g`
  with integer `n_i ≥ 0`, because `g` is primitive and the corner is a basis. The splits `(g, a''_i)` then reach
  `c'`. Correct.
- **Lemma B (face lemma).** Splitting at `(α_i, t_j)` keeps `x`, because `ξ` has `y_(t_j) = 0 < y_(α_i)`, so
  `x` cannot lie in the other child. The two choices `n_ij, n'_ij` coincide. Correct.
- **Lemma C (face cut).** Correct, given the cut lemma, which is imported and not re-checked here.
- **Lemma D (lifting at a shared ray).** Correct.
  - The least lifts are unimodular and in `Q`, and Lemma A applies.
  - Convergence works because `ẑ(v̄)` depends continuously on `v̄` alone, `σ ∈ [0,1)`, and `ℓ(p) → ∞`.
  - `ζ = ξ − s_n g ∈ Q` gives `s_n ≤ s*`. The arc `s ↦ (ξ − sg)^` on `[−∞, s*]` is a homeomorphism onto its
    image, since `z` is not parallel to `g`. So `s_n → s* > 0`, and `ξ ∈ int e_n`.
- **Main induction.** Correct.
  - Totally irrational case: `(TI_m)` plus Lemma D.
  - Otherwise: face cut, a common face by `(LSync_k)`, face splits that miss `ξ` in `W`, a common corner by
    `(LSync_(m−k−1))`, corner splits whose planes contain `W`, then Lemma B.
  - Every call is in lower rank.
- Statement 1, the equivalence `(LSync) ⇔ (Sync)`, is correct.
