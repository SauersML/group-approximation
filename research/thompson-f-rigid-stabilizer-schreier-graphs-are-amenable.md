---
rg: 2
id: thompson-f-rigid-stabilizer-schreier-graphs-are-amenable
kind: claim
title: "Every subgroup of Thompson's group F that contains a rigid interval subgroup F[a,b] (a < b) is co-amenable, because a limit of its conjugates contains F′; the Chabauty condition is exact"
distinct_from:
  thompson-f-end-rigid-schreier-graphs-are-amenable: that needs H ⊇ F[0,c] or F[c,1] (an interval touching an end) and uses x_0-rays; this allows any interior interval and uses a Chabauty limit of conjugates, so it covers every stabilizer of a non-dense subset of [0,1].
  thompson-f-confined-subgroups-fix-finite-sets: that imports the classification of confined subgroups, whose Schreier graphs Chaudkhari notes are amenable; this covers the much larger class of subgroups containing some F[a,b], which includes the confined ones.
  jones-subgroup-is-co-amenable-in-thompson-f: that proves co-amenability of one specific subgroup; this proves co-amenability of every subgroup containing a rigid interval subgroup.
  thompson-f-commensurated-subgroups-are-trivial-or-normal: that classifies commensurated subgroups; this is about co-amenability of arbitrary subgroups with a rigid interval piece.
---

**ESTABLISHED** by `thompson-f-rigid-stabilizer-schreier-graphs-are-amenable-proof` (direct proof from the
imported facts (F1), (F2), (F4) of `thompson-f-rigid-interval-subgroups-facts`; elementary and very likely
folklore, no priority claimed). It decides nothing about amenability of `F`.

**Notation.** For dyadic `0 ≤ a < b ≤ 1`, `F[a,b]` is the set of elements of `F` that are the identity on
`[0,1] ∖ [a,b]`. `S` is a finite symmetric generating set, and `Sch(F/H)` is the Schreier graph of
`F ↷ F/H`.

**Theorem A.** Let `H ≤ F` contain `F[a,b]` for some dyadic `a < b`. Then `Sch(F/H)` is amenable: for every
`ε > 0` there is a finite set `A ⊆ F/H` with `|∂A| ≤ ε|A|`. Equivalently, `H` is co-amenable in `F`.

**Theorem A′ (the Chabauty condition is exact).** For `H ≤ F` the following are equivalent:
1. `H ⊇ F[a,b]` for some dyadic `a < b`;
2. `H` contains a nontrivial normal subgroup of some `F[a,b]`;
3. some Chabauty limit of conjugates `g_n H g_n⁻¹` contains `F′`.

**Instances** (each contains some `F[a,b]`, so its Schreier graphs are amenable):
- the stabilizer (setwise or pointwise) of any subset of `[0,1]` whose closure is not all of `[0,1]`;
- the stabilizer of a Borel set that contains an interval, and of a measure whose support omits an interval;
- every confined subgroup (it contains a germ stabilizer `St0_F′(S)`, `S` finite), every nontrivial
  commensurated subgroup (`thompson-f-commensurated-subgroups-are-trivial-or-normal`), and every
  overgroup of one of these.

**Why it matters.** A Schreier-graph certificate of non-amenability of `F` (a Ponzi scheme, a paradoxical
decomposition or a spectral gap on `F/H`) must use a subgroup `H` that contains no rigid interval subgroup,
equivalently (A′) whose conjugates never accumulate on a subgroup containing `F′`. This upgrades the
end-rigid kill to all interior intervals. See `thompson-f-subgroup-pair-certificates-collapse`.

Proof route: `thompson-f-rigid-stabilizer-schreier-graphs-are-amenable-proof`.
