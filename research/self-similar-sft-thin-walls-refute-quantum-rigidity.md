---
rg: 2
id: self-similar-sft-thin-walls-refute-quantum-rigidity
kind: claim
title: In a Z^2 SFT with an injective constant-size block substitution into itself, two configurations that agree on one column and differ on both sides refute quantum rigidity at every scale; so rigid self-similar SFTs have one-sided determining columns and no information-free macrotile column
requires:
  - sft-crossed-product-fp-iff-quantum-rigid
distinct_from:
  self-similar-sfts-are-quantum-rigid-iff-rigid-at-one-scale: that substitutes a non-commuting operator family, which needs scale at least D_0 >= 3; this substitutes a pair of configurations, so a wall of width ONE (below every operator scale) already refutes rigidity, and it gives the geometric necessary condition of one-sided columns.
  determinism-closure-certifies-quantum-rigidity: that obstructs one proof method through fault slabs (configurations differing only inside a slab); this refutes rigidity itself through thin walls (configurations agreeing on a slab and differing on both sides).
  permutive-triangle-sfts-are-quantum-rigid: that is a sufficient mechanism giving one-sided determinism in every direction; this shows that for self-similar SFTs one-sided determinism of every column and row is necessary.
---

**ESTABLISHED (2026-09-18)** through `self-similar-sft-thin-wall-substitution-proof`. Lane proof (bh-free-35),
elementary, not independently reviewed. No priority is claimed.

## Setting

`Ω ⊆ A^(Z^2)` is an SFT. `σ : A → A^([0,N)^2)`, with `N >= 2`, is injective with `σ(Ω) ⊆ Ω`, where `σ(x)` places
`σ(x_Z)` on `NZ + [0,N)^2`. This is the hypothesis of `self-similar-sfts-are-quantum-rigid-iff-rigid-at-one-scale`.
Durand–Romashchenko–Shen fixed-point tile sets satisfy it. So does Ledrappier's shift, with `N = 2` and block
`σ(a) = [[a, a], [0, a]]` (top row first) on `{2i−1, 2i} × {2j−1, 2j}`, since `y = (1 + u^(-1) + v^(-1)) x^((2))`, the
Frobenius image of a configuration, satisfies the rule again.

## Statement

1. **Thin walls.** Suppose `x, y ∈ Ω` agree on one column `{i_0} × Z` and differ at some site left of it and at some
   site right of it. Then `Ω` is not `D`-quantum rigid for any `D`, and `LC(Ω, k) ⋊ Z^2` is not finitely presented over
   any field. The same holds for rows.
   - For a primitive `ν ∈ Z^2`, agreement on a strip `{a <= ⟨t, ν⟩ <= b}` with `b − a + 1 >= |ν|_1 + 2`, together with
     differences on both sides, suffices.
2. **One-sided columns.** If `Ω` is quantum rigid, then for every column `C` occurring in `Ω`, either all configurations
   with column `C` at `0` agree on the left half-plane `{i < 0}`, or all agree on `{i > 0}`. The same holds for rows,
   and for strips of the width in item 1 in rational directions.
3. **Information-free columns.** Suppose no configuration of `Ω` has period `e_2` (for instance, `Ω` is free). If for
   some `i ∈ [0, N)` the column `i` of `σ(c)` is the same for all `c ∈ A`, then `Ω` is not quantum rigid.
   - More generally, write `c ~_i c'` when `σ(c)` and `σ(c')` have the same column `i`. Two configurations that agree
     on column `0` modulo `~_i` and differ on both sides of it refute rigidity.
4. **Calibration.**
   - Ledrappier's shift passes item 2: a column determines the right half-plane. It is quantum rigid
     (`ledrappier-crossed-product-is-finitely-presented`).
   - Full shifts fail item 1 at once, consistent with `positive-entropy-sft-crossed-products-are-not-fp`.

## Lesson for general BH

Self-similarity lifts refutations by configurations just as it lifts refutations by operator families, and it needs
only a wall of width one.
- **Design rule for a programmable fixed point.** Every column and every row of the macrotile must carry information
  about the macro colour, and in a one-sided way.
  - No coordinate-only strips are allowed.
  - Through item 3's equivalence `~_i`, an edge line of the macro tiling with two-sided freedom (a vertical line of
    edge colours with two left and two right completions) already kills rigidity, whenever the columns crossed by the
    wires of `W(c)` carry nothing else.
  - A rigid fixed-point tile set must therefore propagate information in one direction across every axis line, as
    Ledrappier does.
- **Pre-filter.** This is a cheap filter before any operator computation. Its positive counterpart is the
  bounded-range test `fixed-point-tile-set-rigidity-is-a-bounded-range-test`.
