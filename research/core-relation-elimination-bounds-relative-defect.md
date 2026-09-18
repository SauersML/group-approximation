---
rg: 2
id: core-relation-elimination-bounds-relative-defect
kind: claim
title: In a one-relator group, dropping core relations x = phi(x) along basis elements that occur once in successive 2-cell words lowers the relative defect by one each; full elimination only ever reaches w-one-relator subgroups, which realize trivially, and it is blocked on any core whose 2-cycles use two cells
distinct_from:
  relative-realization-is-relative-efficiency: that proves rho(H,G) <= n(C) - 1 by deleting the single w-cell. This deletes core relations instead, one per eliminable basis element, giving rho <= n(C) - 1 - m(C), and it identifies which subgroups the whole core-elimination family can realize.
  two-cell-injective-maps-realize-relative-eg-pairs: its (3b) realizes w-disc subgroups. This shows that full core elimination produces only subgroups F(B'')/<<u>> with phi(u) conjugate to w^{+-1}, which already realize by one Tietze move, and that for n(C) = 2 a single-occurrence elimination succeeds iff a decidable Magnus conjugacy test holds.
  relative-eg-pair-base-meets-its-conjugates-in-free-groups: that gives free conjugate intersections and H_2 injectivity from pd I_{G/H} <= 1. This adds the H_1 statement (ker(H_1 H -> H_1 G) is free abelian modulo the image of H_2 G, so degree-one admissible bases have torsion-free H_1) and the resulting normal form of a two-cell core.
artifacts: []
---

**ESTABLISHED** via `core-relation-elimination-bounds-relative-defect-proof` (unreviewed).

## Setting

`G = ⟨S | w⟩`, with `w` cyclically reduced and not a proper power, and `X` its presentation
complex. `H ≤ G` is finitely generated, and `C ⊂ X_H` is a finite core with 2-cells
`e_1, …, e_n` (`n ≥ 1`). Let `F = π_1(C^1, v) ≅ F_r` and let `φ: F → F(S)` be the injective map
induced by the immersion `C^1 → X^1`. Each `e_j` gives a boundary element `u_j ∈ F`, defined up
to conjugacy and inversion, with `φ(u_j)` conjugate to `w^{±1}` in `F(S)`. Then
`H = F/⟨⟨u_1, …, u_n⟩⟩`.

For a free basis `B` of `F` and `B' ⊆ B`, the **core elimination presentation** is

`P_{B'} = ⟨H, S | x = φ(x) (x ∈ B')⟩`.

For `B' = B` it presents `G` with defect `n - 1`: this is the `Y_1` of Theorem 3 of
`relative-realization-is-relative-efficiency`. Defect means `ρ = (|R| - |T|) - (χ(G) - χ(H))`
for a relative presentation `⟨H, T | R⟩` of `G`.

**Elimination chain.** A chain of length `m` is a free basis `B`, distinct basis elements
`y_1, …, y_m`, and an ordering `e_0, e_1, …, e_m` of `m + 1` distinct 2-cells, such that:

- `u_0` can be written without any `y_l`;
- for each `k ≥ 1`, `u_k` can be written (up to conjugacy) with `y_k` occurring exactly once and no
  `y_l` with `l > k` occurring.

Cells outside the chain are unrestricted. Let `m(C)` be the maximal chain length over all free
bases. The chain is **full** when `m = n - 1`. A full chain is the same as a Nielsen change of
basis of the rose presentation `⟨B | u_1, …, u_n⟩` of `H` followed by `n - 1` successive
elementary free-face collapses.

## Statement

**(E1) Elimination bound.** Given a chain, `P_{B ∖ {y_1..y_m}}` presents `G`, with `H → G` the
inclusion, and has defect `n - 1 - m`. So

`ρ(H,G) ≤ n(C) - 1 - m(C)`.

No admissibility hypothesis is used. If `C` has a full chain, then `RP(H,G)` holds.

**(E2) Full elimination only reaches w-one-relator subgroups.** If `C` has a full chain, then
`H ≅ F(B'')/⟨⟨u_0⟩⟩`, where `B'' = B ∖ {y_1..y_{n-1}}` spans a free factor of `F` and `φ(u_0)` is
conjugate to `w^{±1}`. Conversely, for any `H ≤ G` of this form (a free group `F(B'')` with an
injective map `φ` to `F(S)`, and a relator `ū` with `φ(ū) ∼ w^{±1}`, such that
`F(B'')/⟨⟨ū⟩⟩ → G` is injective), the single presentation `⟨H, S | x = φ(x) (x ∈ B'')⟩` has
defect 0, so `RP(H,G)` holds without any core. Full core elimination therefore realizes no pair
outside this w-one-relator class.

**(E3) The case `n(C) = 2`, single occurrence.** Let `y ∈ B` occur exactly once in `u_1`, and put
`B' = B ∖ {y}`. Write `u_1 ∼ y^ε c` with `c ∈ F(B')`. Then `P_{B'} ≅ ⟨S | ψ(u_0)⟩`, where
`ψ = φ` on `B'` and `ψ(y) = φ(c)^{-ε}`. This has defect 0. It presents `G` (so `RP(H,G)`) iff
`ψ(u_0)` is conjugate to `w^{±1}` in `F(S)`, by Magnus' conjugacy theorem, and this test is
decidable. Whenever it holds, `H ≅ F(B')/⟨⟨u_0'⟩⟩` with `u_0' = u_0[y := c^{-ε}]` and
`φ(u_0') = ψ(u_0)`, so `H` is in the w-one-relator class of (E2).

**(E4) Support obstruction for full chains.** Suppose `C` has a full chain. Then for every right
`ZH`-module `M`, every 2-cycle of `C` with coefficients in `M` is supported on the single cell
`e_0`. Equivalently: if some 2-cycle of `C`, with coefficients in any `ZH`-module, has nonzero
coefficient on two cells, then `m(C) ≤ n(C) - 2` and core elimination cannot reach defect 0 on
`C`. The test is a finite computation on the Fox matrix of `C`.

**(E5) H_1 of admissible bases.** If `pd_{ZG} I_{G/H} ≤ 1` (any groups `H ≤ G`), then
`ker(H_1 H → H_1 G) ≅ H_1(G; I_{G/H}) / im(H_2 G)`, and `H_1(G; I_{G/H})` is free abelian.
Suppose `H` is a **degree-one admissible base** in a one-relator group: `w ∈ [F(S),F(S)]`,
`H_2(H) → H_2(G) = Z` is onto, and `pd I_{G/H} ≤ 1`. Then `H_1(H)` is torsion-free. For a
two-cell core, this puts `C` in the following normal form:

- `L = ⟨[u_0],[u_1]⟩ ⊂ H_1(C^1) = Z^r` is a rank-one direct summand `Zp`;
- `[u_0] = a p` and `[u_1] = b p` with `gcd(a,b) = 1`;
- `ε_0 b - ε_1 a = ±1`, where `ε_j = ±1` is the degree of `e_j` on the `w`-cell;
- the fundamental class is `b e_0 - a e_1`.

By (E4), elimination on `C` requires `ab = 0`. Torsion-freeness allows `ab ≠ 0`, for example
`(a,b) = (1,2)`, so homology of `H` alone does not decide elimination.

## What this decides for the lane

The step asked whether the core presentation of defect `n(C) - 1` can be reduced to defect 0 by
adding generators. It was posed in its natural form: keep `C` and the generators `S`, and drop core
relations. In that form the answer is as follows.

- Triangular elimination gives the bound (E1).
- Full elimination never realizes anything outside the w-one-relator class, and that class
  realizes trivially (E2).
- For `n(C) = 2` with a single-occurrence generator, success is a decidable Magnus test that
  again forces the w-one-relator class (E3).
- Elimination is impossible on any core whose 2-cycles use two cells (E4), and in the degree-one
  admissible case the obstruction is visible only in the core, not in `H_1(H)` (E5).

So the relative Eilenberg--Ganea problem for f.g. pairs in torsion-free one-relator groups has this
surviving profile:

- `H` is admissible;
- `H` is **not** of the form `F(B'')/⟨⟨ū⟩⟩` with `φ(ū) ∼ w^{±1}`. For example `H` is freely
  decomposable with two non-free factors, or `H` needs two relators;
- every finite core of `X_H` has a 2-cycle supported on at least two cells;
- any realization must use a non-triangular elimination, where the dropped basis elements occur
  more than once, or new generators beyond `S`.

The exact open test in the smallest case, `n(C) = 2`, is whether
`⟨S, y | λ(u_0), λ(u_1)⟩ → G`, `y ↦ φ(y)`, is an isomorphism, where `λ = φ` on `B ∖ {y}` and
`λ(y) = y`. This is a two-relator Andrews--Curtis-type question and is not settled here.
