---
rg: 2
id: one-ended-hyperbolic-subgroups-of-v-locally-fixed-proof
kind: route
title: Proof that one-ended hyperbolic subgroups of V are locally fixed everywhere and, if torsion-free, have no north–south elements
target: one-ended-hyperbolic-subgroups-of-v-are-locally-fixed
requires:
  - topologically-free-fg-subgroups-of-v-are-virtually-free
---

Lane proof (bh-scout-bbmz, 09-19), not reviewed.

## Imports

- `topologically-free-fg-subgroups-of-v-are-virtually-free`, parts 3(a)–(c). Refereed PASS by bh-ref-t0, 6a216bf0dc.
- **Standard facts about hyperbolic groups, recalled and not re-read:**
  - `Γ` is one-ended iff `∂Γ` is connected.
  - For one-ended `Γ`, `∂Γ` is locally connected (Bestvina–Mess, Bowditch, Swarup), so it is a Peano continuum.
  - `∂Γ` has no isolated points when `Γ` is non-elementary.
  - An infinite-order `c` has exactly two fixed points `c^±` on `∂Γ`, and `c^{±n} x → c^±` for every `x ∈ Γ ∪ ∂Γ`
    other than `c^∓`.
  - `⟨c⟩` is quasiconvex.
  - In a torsion-free hyperbolic group, commuting nontrivial elements lie in a common cyclic subgroup.
- **Connected open subsets of a Peano continuum are arcwise connected** (Mazurkiewicz–Moore–Menger), and components
  of open subsets of a locally connected space are open.
- **Bottleneck necessity.** If a geodesic space `Y` is quasi-isometric to a tree, then there is `Δ` such that for
  all `x, y ∈ Y`, every geodesic `[x,y]` with midpoint `m`, and every path `p` from `x` to `y`, `p` meets `B(m, Δ)`.
  This is the easy direction of Manning's bottleneck criterion (Geom. Topol. 9, 2005, Thm 4.6).
  - Proof: push forward by the quasi-isometry.
  - The image of a path is a coarse path between the images of `x` and `y`. It must pass near every point of the
    tree geodesic between them.
  - The image of `[x,y]` is a quasi-geodesic, so it stays near that tree geodesic, and the image of `m` is near it.

## Lemma L

Let `X = Cay(Γ,S)` be `δ`-hyperbolic, `o = 1`, `H = ⟨c⟩`. The Schreier graph on `Γ/H` is isometric to the quotient
graph `H\X`. In the right-action convention of HSZ this is the right-coset version, up to the inversion isometry.
The metric is `d̄([x],[y]) = min_n d(x, c^n y)`. The action of `H` on vertices is free. Set `ht([x]) = d̄([x],[o])`.
Throughout, `C_1, C_2, …` are constants independent of `R`.

**Choice of boundary data.**
- Let `U` be a component of `∂Γ ∖ {c^±}` with more than one point. When `Γ` is one-ended, `∂Γ ∖ {c^±}` is open in a
  Peano continuum, so its components are open, hence infinite, and arcwise connected.
- `U` is uncountable and `H`-orbits are countable, so we can pick `ξ, η ∈ U` with `ξ ∉ Hη`.
- Let `J ⊆ U` be an arc from `ξ` to `η`. It is compact and disjoint from `{c^±}`.

**(E1) Heights on rays over `J` are ≈ R.**
- Let `M = sup{(ζ | c^n o)_o : ζ ∈ J, n ∈ Z}`. Then `M < ∞`. Otherwise take `ζ_k ∈ J` and `n_k` with
  `(ζ_k | c^{n_k} o)_o → ∞`. For bounded `n` the product is at most `d(o, c^n o) + δ`, so `|n_k| → ∞`. Passing to
  subsequences, `ζ_k → ζ ∈ J` and `c^{n_k} o → c^+` (say), so `ζ = c^+`, which is impossible.
- For `x` on a geodesic ray `[o, ζ)` with `ζ ∈ J` and `d(o,x) = R`:
  `d(x, c^n o) = R + d(o, c^n o) − 2(x | c^n o)_o ≥ R − 2M − 8δ`,
  using `(x|y)_o ≤ (ζ|y)_o + 4δ`. So `ht([x]) ≥ R − C_1`.

**(E2) A high path.**
- Choose `t_0 = ξ, …, t_N = η` along `J` with `(t_i | t_{i+1})_o ≥ R`, which is possible by uniform continuity of
  `J` in a visual metric.
- Let `x_i` be the point at distance `R` on a ray `[o, t_i)`. Then `d(x_i, x_{i+1}) ≤ C_2` (fellow traveling).
- Join consecutive `[x_i]` by quotient geodesics. The resulting path `P` from `[x_ξ]` to `[x_η]` has every point of
  height `≥ R − C_1 − C_2`.

**(E3) Every quotient geodesic from `[x_ξ]` to `[x_η]` has its midpoint at bounded height.**
- Let `D = d̄([x_ξ],[x_η]) ≤ d(x_ξ, x_η) ≤ 2R`.
- A quotient geodesic of length `D` lifts to a path of length `D` from `x_ξ` to some `c^n x_η`. Since `D` is the
  minimum, this lift is an `X`-geodesic `g`.
- **Claim:** `(x_ξ | c^n x_η)_o ≤ C_3` for all `n` once `R ≥ R_0`.
  - The point `c^n x_η` lies on the ray `[c^n o, c^n η)`. In the thin triangle `(o, c^n o, c^n η)` it is `δ`-close
    to `[o, c^n o]` or to `[o, c^n η)`.
  - The first is impossible for large `R`. `[o, c^n o]` is `K`-close to `H o` by quasiconvexity, which would give
    `ht([x_η]) ≤ δ + K`, contradicting (E1).
  - So `c^n x_η` is `δ`-close to a point `y ∈ [o, c^n η)`, and
    `(x_ξ | c^n x_η)_o ≤ (ξ | c^n η)_o + C_4`.
  - Finally, `M' = sup_n (ξ | c^n η)_o < ∞`, by the same compactness argument as in (E1). The key inputs are
    `c^n η → c^±`, `ξ ≠ c^±`, and `ξ ≠ c^n η` for every `n`.
- **Conclusion.** So `g` passes within `C_3 + 4δ` of `o`, at a point `q` with `ht([q]) ≤ C_3 + 4δ`.
  - The endpoints have height `≥ R − C_1`, and `D ≤ 2R`.
  - So `|d̄([x_ξ],[q]) − D/2| ≤ C_5`, and the midpoint `m` has `ht(m) ≤ C_6`.

**Contradiction.** Every point of `P` is at distance `≥ ht(·) − ht(m) ≥ R − C_1 − C_2 − C_6` from `m`. For `R` large
this exceeds any `Δ`, so the bottleneck necessity fails, and `H\X` is not quasi-isometric to a tree. ∎

(Sanity check: for virtually free `Γ`, `∂Γ` is a Cantor set, `U` never exists, and indeed `Γ/⟨c⟩` is a quasi-tree.)

## The theorem

**Item 1.**
- One-ended `Γ` is not virtually free.
- By `topologically-free-fg-subgroups-of-v-are-virtually-free` 3(b), every `x ∈ K = C ∖ ⋃_{g≠1} int Fix(g)` has
  `Stab_Γ(x) = ⟨c_x⟩ ≅ Z`.
- By 3(c), `Γ/⟨c_x⟩` is quasi-isometric to a tree. Lemma L forbids that, so `K = ∅`.
- Compactness gives the finite clopen cover, and refining gives disjoint pieces.

**Item 2.** Let `Γ` be torsion-free.
- **Disjoint supports.** Suppose `h, k ≠ 1` have disjoint open supports. They commute, so `h = z^i` and `k = z^j`
  with `i, j ≠ 0`. Then `h^j = k^i`, with `supp(h^j) ⊆ supp(h)` and `supp(k^i) ⊆ supp(k)`. Those supports are
  disjoint, so `z^{ij}` has empty support and `z^{ij} = 1`, which is impossible.
- **North–south dynamics.** Suppose `w` has north–south dynamics with attractor `a` and repeller `r`.
  - By item 1, pick clopen `A ∋ a` and `B ∋ r` with nontrivial pointwise fixers `g_a`, `g_r`. Pick `n` with
    `w^n(C ∖ B) ⊆ A`.
  - Then `k = w^{-n} g_a w^n` fixes `w^{-n}(A) ⊇ C ∖ B`, so `supp(k) ⊆ B`, while `supp(g_r) ⊆ C ∖ B`.
  - These are disjoint nontrivial supports, which the previous paragraph excludes. ∎

## What is left for Question 4.7 (open)

**Compression lemma (open).** For `Γ ≤ V` one-ended and torsion-free, there are `γ ∈ Γ` and nontrivial `g` with
`γ(cl supp g)` inside a clopen set that has a nontrivial pointwise fixer. By item 2 this gives a contradiction.

**Why it is not yet done.** An infinite-order `w ∈ V` has, after passing to a power, a decomposition
`C = P ⊔ F` (recalled from the flow-graph description of elements of `V`, Bleak et al., "Centralizers in
R. Thompson's group V_n"; not read at source):
- `P` is clopen and `w|_P = id`;
- `F` carries finitely many attracting and repelling fixed points;
- points of `F` flow from repellers to attractors.

The north–south argument goes through when `P = ∅` and there is one attractor and one repeller. With several
attractors, one needs a single nontrivial element fixing neighborhoods of all of them at once. With `P ≠ ∅`, points
of `P` never flow. Both are the remaining gaps.
