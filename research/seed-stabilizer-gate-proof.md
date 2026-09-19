---
rg: 2
id: seed-stabilizer-gate-proof
kind: route
title: Seed orbits carry all finitary permutations, so the finitary-overgroup theorem gives the stabilizer, and a split full group is the regular lampshuffler
target: seed-stabilizer-gate-is-free-and-split-seed-full-groups-die
requires:
  - fp-finitary-permutation-overgroups-are-type-a-actors
  - lampshuffler-groups-are-not-fp2-over-q
---

Notation as in the target.

## Preliminaries

- **`O` is countably infinite.** `Γ` is countably infinite, and `g ↦ g·y_*` is injective by (S2).
- **`F` preserves `O`.** `f(g·y_*) = c(g·y_*) g·y_* ∈ O`, and the same holds for `f^(-1)`.
- **`FSym(O) ≤ F`.** Each point of `O` is isolated by (S1), so `{o}` is clopen. The
  transposition of `o_1 = g_1·y_*` and `o_2 = g_2·y_*` has cocycle `g_2 g_1^(-1)` on `{o_1}`,
  `g_1 g_2^(-1)` on `{o_2}` and `1` on the clopen rest. Finitary permutations are products of
  transpositions.
- **Faithfulness.** If `f ∈ F` fixes `O` pointwise, it fixes `Y = cl(O)` by (S3) and
  continuity. So restriction `F → Sym(O)` is injective.

## Item 1

By the preliminaries, `F` is a subgroup of `Sym(O)` containing `FSym(O) ⊇ Alt_fin(O)`, with `O`
countably infinite. Suppose `F` is finitely generated. By
`fp-finitary-permutation-overgroups-are-type-a-actors`:
- item 1 there: the action is faithful and highly transitive, with one orbit on 2-subsets;
- item 2 there: every point stabilizer `Stab_F(o)` is finitely generated.

These are conditions 1, 3 and 4 of type (A). Condition 2 is finite presentation of `F`. A
finitely presented group is finitely generated, so in the SEED claim condition 2 implies
condition 3. ∎

## Item 2

- **(a) ⇒ (b).** Write `f = σγ` with `σ ∈ FSym(O)`, `γ ∈ Γ`. Then `f(y) = γ(y)` unless
  `γ(y) ∈ supp σ`, that is, outside the finite set `γ^(-1)(supp σ) ⊂ O`.
- **(b) ⇒ (a).** If `f = γ` outside a finite `E ⊂ O`, then `fγ^(-1)` is the identity outside
  the finite set `γ(E) ⊂ O`. Being a bijection of `Y` that fixes the complement of `γ(E)`
  pointwise, it permutes `γ(E)`. So `fγ^(-1) ∈ FSym(O)`.
- **The splitting.**
  - `FSym(O)` is normal in `F`, since `f` preserves `O` and `fσf^(-1)` is supported on the
    finite set `f(supp σ)`.
  - `Γ ∩ FSym(O) = 1`. If `γ(g·y_*) = g·y_*`, then `g^(-1)γg ∈ Stab_Γ(y_*) = 1` by (S2). So a
    nontrivial `γ` moves every point of the infinite set `O` and is not finitary.
  - So under (a), `F = FSym(O) ⋊ Γ`, with `Γ` acting on `FSym(O)` by transport of supports.
- **The lampshuffler.** The bijection `Γ → O`, `g ↦ g·y_*`, intertwines left multiplication
  with the action on `O`. It carries `FSym(O) ⋊ Γ` onto `FSym(Γ) ⋊ Γ`, where `Γ` acts on itself
  by left multiplication, freely and transitively.
- **One boundary point.** Let `∂ = {z}`. `∂` is `Γ`-invariant, so `z` is fixed by `Γ`. For
  `f ∈ F` the cocycle is locally constant, so `c ≡ γ` on a clopen neighbourhood `U` of `z`.
  - `Y ∖ U` is compact and misses `∂`, so it lies in `O`.
  - It is covered by the open singletons of its points, so it is finite.
  - So `f = γ` outside the finite set `Y ∖ U ⊂ O`, which is (b). ∎

## Item 3

By item 2, `F ≅ FSym(X) ⋊ Γ` with `X = Γ` a free `Γ`-set with one orbit. `Γ` is finitely
generated and virtually maps onto `Z`. So Corollary B of `lampshuffler-groups-are-not-fp2-over-q`
applies: `F` is not of type `FP_2` over `Q`, hence not finitely presented. ∎

## Item 4

- **The seed.** For `Y = cl(Z·y_*)` with `y_* = …0001000…`, the only limit of shifts
  `n·y_*` with `|n| → ∞` is `0^Z`. So `Y = O ∪ {0^Z}`.
  - *(S1).* `[y(0) = 1] ∩ Y = {y_*}`.
  - *(S2).* The shifts of `y_*` are distinct.
  - *(S3).* This holds by construction.
- **The full group.** `∂` is one point, so by item 2, `F ≅ FSym(Z) ⋊ Z`. This is Houghton's
  `H_2`, and it is not finitely presented by item 3 with `Γ = Z`.
- **The boundary full group.** The germ map at `0^Z` sends `σ·n` (`σ ∈ FSym(O)`, `n ∈ Z`) to
  the germ of `n`, because `supp σ` is finite and `0^Z` is not isolated. The germ of `n ≠ 0` is
  nontrivial, since `n` moves every nearby point `m·y_*`. So `F_∂ ≅ Z`, which is finitely
  presented. ∎
