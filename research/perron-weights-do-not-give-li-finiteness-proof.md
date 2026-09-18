---
rg: 2
id: perron-weights-do-not-give-li-finiteness-proof
kind: route
title: The F_2 reduced-word coding has Perron weights but non-simply-connected Witzel complexes at x_N = (a, a^-1, N b, N b^-1); Li's link lemma needs the packing number, and a hitting set plus a thin cycle bounds it
target: perron-weights-do-not-give-li-finiteness
requires:
  - perron-substitution-finiteness-for-garside-full-groups
  - pointed-cube-categories-are-li-garside-categories
---

**Lane proof, not independently reviewed.** All labels are X. Li's (arXiv:2110.04505v2), read
at source in `$GQ/src/kep/li-garside-II-2110.04505v2.tex`. The two uses that matter:
- (`t<d`) appears only in the height lemma after `thm:Wit` (l.1662–1665).
- The packing number `ρ'` (l.1652) is the hypothesis of `lem:link:n-conn_3`: "for all
  `x ∈ 𝐗(*)` with `ρ'(x) ≥ R`" (l.1729).

## 1. The datum

Let `𝔠` be the path category of the graph with:
- vertices `*` and the letters `ℓ ∈ {a^{±1}, b^{±1}}` (take `k = 2`; general `k` is
  identical);
- edges `* → ℓ` for every letter;
- edges `ℓ → ℓ'` for `ℓ' ≠ ℓ^{-1}`.

This is the pointed-cube category of the 4-valent tree. Its base object is the pointed
`0`-cube; the other objects are the letters, i.e. the last edges.

The hypotheses hold:
- `𝔠` is free, so it is left and right cancellative, finitely aligned, and has trivial
  units; (F) holds.
- `𝔖` is the set of edges. It is a locally finite Garside family, and the paths of length
  `≤ L` are closed under left divisors. `X = Ω_∞` is the set of infinite paths.
- `𝔛 = {X(v;∅)}` (cone types) and `Γ = {γ(∅,𝔖)}` (one-layer expansions).
- The expansion of `X(ℓ;∅)` has pieces `X(ℓ';∅)` for `ℓ' ≠ ℓ^{-1}`, and its leftover is
  empty.
- (St): (`1_𝔛`) is trivial; (`2_𝔛`) holds because every `X(v;𝔢)` is a union of child
  cones; (`1_Γ`) holds by the choice of `Γ`.
- (`2_Γ`) is vacuous: `‖cs‖ = ‖c‖ + 1` for every edge `s`.
- `𝒞` has lcms: two families of one-layer expansions have a common refinement, and
  expansions of distinct pieces commute.
- The Perron weight exists: `w = 𝟙` on letters and `w_* = 1`. Each letter has 3
  children and `*` has 4, so every generator raises `⟨w, 𝐦⟩` by at least `2`.

## 2. The objects `x_N`

**Reachable objects.** `*` expands to `(a, a^{-1}, b, b^{-1})`. Expanding the `a`-piece
`N − 1` times gives

  `x_N = (a, a^{-1}, b_1, …, b_N, b'_1, …, b'_N) ∈ 𝐗(*)`, with `b' = b^{-1}`.

- Each letter-expansion keeps exactly one child of its own type. So no letter count ever
  decreases, and every reachable object other than `*` contains an `a`-piece and an
  `a^{-1}`-piece.
- A piece of type `*` never coexists with other pieces, since there are no edges into `*`.

**The complex `E(x_N)`.** Its vertices are the classes `[α]` of non-unit left divisors
`α` of `Δ(𝐭(α))` with `𝐝(α) = x_N`. In other words, `x_N` arises from `𝐭(α)` by expanding
a set of pieces of `𝐭(α)` one layer each. So `[α]` is a nonempty set of pairwise disjoint
**merges**, and `𝐭(α)` must lie in `𝐗(*)`.

- Classes are taken modulo units on the target side, so the partition of `x_N`'s index
  set determined by `α` is an invariant of `[α]`.
- The order `[α] ≤ [β]` is inclusion of merge sets. Two-layer merges are not left
  divisors of `Δ`.

**The possible merges.** A merge collapses the full child pattern of one letter.
- Merges into `b` or `b^{-1}` use both `a` and `a^{-1}`, so their target has no
  `a`-piece and is not in `𝐗(*)`.
- A merge into `*` would produce a `*`-piece alongside other pieces, which never happens
  in `𝐗(*)`.
- What remains:
  - `A(i,j)`, the merge `{a, b_i, b'_j} → a`;
  - `B(i,j)`, the merge `{a^{-1}, b_i, b'_j} → a^{-1}`.

  Both targets have the form `(a, a^{-1}, (N−1)b, (N−1)b')`, which is reachable.
- Two `A`'s share `a`, and two `B`'s share `a^{-1}`. The set `{A(i,j), B(i',j')}` is
  disjoint iff `i ≠ i'` and `j ≠ j'`, and its target is reachable when `N ≥ 3`.

**Conclusion.** `|E(x_N)|` is the barycentric subdivision of the bipartite graph on the
`A`'s and `B`'s, and it has no 2-simplices. For `N ≥ 3` this graph contains the 4-cycle

  `A(1,1) – B(2,2) – A(3,1) – B(2,3) – A(1,1)`,

so `H_1 ≠ 0` and `|E(x_N)|` is not simply connected. For general `k`, the same computation
works with `b` replaced by the `2k − 2` other letters.

## 3. No height function can help

Witzel's `thm:Wit` asks for `(n−1)`-connected `|E(x)|` at every `x` with `ρ(x) ≥ N₀`, for
some height `ρ` with finite sublevels.
- The `x_N` are pairwise non-isomorphic: units preserve the type multiset, and the sizes
  differ.
- So any such `ρ` has `ρ(x_N) → ∞`, and the hypothesis fails for `n = 2`.

In particular it fails for `ρ_w`. Step §1 of `perron-substitution-finiteness-proof` says
the link lemmas use `ρ` only through (H1) and (H2). That is false: `lem:link:n-conn_3` needs
`ρ'(x) ≥ R`, and for `x_N` we have `ρ'(x_N) ≤ 2` (§5).

The conclusion survives for `F_k` itself:
- `Y = X(*;∅)` is carried by the edges `* → ℓ` onto the unit space of the letter graph.
- That graph is irreducible and not a permutation, so its groupoid is an irreducible
  one-sided SFT groupoid.
- Li's `cor:ProdGraphs` with `k = 1` (l.2151–2160) makes its full group `F_∞`. Its proof
  quotes Matui's recoding to `#𝔳𝔠𝔳 ≥ 2`, i.e. the recoding is essential.

## 4. The repair

Replace Li's `ρ` by a height `ρ_h` with finite sublevels, both in `thm:Wit` and in the
Morse function `h⃗ = (n_+, ρ(μ_0))`. Only the height property is used there: for
`[μ] < [ν]` with equal `n_+`, the target of `ν_0` is coarser. Keep Li's `ρ'` as the
hypothesis of `lem:link:n-conn_3`.

Li's reduction in `cor:link:n-conn` (`E(x) ≅ E(x')` for unit-isomorphic `x, x'`) gives
`(n−1)`-connected `|E(x)|` whenever `ρ(x) ≥ R(n)` in the max-over-units form.
- By (Pack), only finitely many classes have `ρ(x) < R(n)`.
- Let `N₀` exceed `ρ_h` on those classes.
- Then every `x` with `ρ_h(x) ≥ N₀` has `(n−1)`-connected `|E(x)|`.
- `lem:Stab` is unchanged, and `thm:Wit` gives `F_n`.

The piece count is a height whenever every non-unit generator has at least two nonempty
pieces. Under (`t<d`), Li's height lemma shows that `ρ` is itself a height with finite
sublevels, and that is (Pack).

**The example `u → u, w`, `w → w, w`.**
- Reachable objects are `(u, m·w)`.
- Packing `γ_w` `m` times gives `ρ' ≥ m`, so (Pack) holds.
- The expansion of `u` has a single `u`-child, so (`t<d`) fails at `u`.

## 5. Thin-cycle lemma

Suppose `R` satisfies (i) and (ii) of item 4 of the target.
- **Bound.** Summing the packing constraint over the types in `R` gives
  `Σ_γ ρ_γ · #(𝔛(𝐝γ) ∩ R) ≤ 𝐦_𝐔(R)`. Every term has `#(…) ≥ 1` by (i), so
  `ρ'(𝐔) ≤ 𝐦_𝐔(R)`. Units preserve `R`, so the same bound holds for `ρ`.
- **The chain.** Start from a reachable object containing the cycle's first type and
  apply the cycle `n` times to its successive `R`-pieces. By (ii), `𝐦(R)` stays
  constant, while the objects grow (by the further piece in (ii)) and so are pairwise
  non-isomorphic.
- So `ρ` is bounded on infinitely many classes, and (Pack) fails.

For `F_k`, take `R = {a, a^{-1}}`.
- (i): the expansion of `ℓ` contains every letter except `ℓ^{-1}`, so it contains `a` or
  `a^{-1}`; the expansion of `*` contains both.
- (ii): the expansion of `a` has the single `R`-child `a`.
- So `ρ'(x_N) ≤ 𝐦_{x_N}(R) = 2`.

## Lesson for general BH

Reading Li's proof line by line, the only thing a finiteness certificate must add to a
height is merge packing. The failure of packing has a finite, checkable witness: a hitting
set of types together with a thin cycle. That is the test to run on any proposed host
coding before investing in it. A spectral condition is never the test.
