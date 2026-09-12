---
rg: 2
id: ternary-three-address-injective-automata-have-balanced-rules
kind: claim
title: Over every group, an injective three-symbol automaton with three memory elements has a balanced rule
distinct_from:
  binary-three-address-injective-automata-have-balanced-rules: that settles two symbols, where every unbalanced rule has a blind coordinate to flip; this is the three-symbol case, where blind pairs of different coordinates can disagree and single-site changes are never invisible.
artifacts:
  - research/artifacts/small-memory-balance-census-2026-09-12.md
---

**OPEN.** Let `G` be any group, `M` a subset of `G` with `|M| = 3`, and `mu : F_3^M -> F_3`. If
`tau(x)(g) = mu((x(g m))_(m in M))` is injective, then `mu` is balanced.

This is a case of `every-injective-ca-has-uniform-single-site-output-law`. A counterexample
refutes Gottschalk's conjecture.

## Attempts

- **Two addresses and constant tests.**
  - `|M| <= 2` is settled for every alphabet, because the memory group is cyclic.
  - Constant configurations force the diagonal `c -> mu(ccc)` to be a permutation.
- **Common blind pair.** Suppose one pair `{c, d}` is blind in all three coordinates. Then a
  single-site change is invisible on every Sidon placement (artifact, Proposition 5.1). The
  relation cases would need the analysis of Section 4, which was not done here.
- **Rigid rules survive single-site changes.** Dies here.
  - **Example.** `R` = `x - y + z` with the value at `(0, 2, 2)` changed to `1`.
  - **Its data.** Blind pairs `{0,1}`, `{1,2}` and `{0,2}`. It is unbalanced, with 10 preimages of
    `1` and 8 of `0`, and its diagonal is the identity.
  - **Consequence.** No single-site change of any configuration is invisible for it, over any group.
- **Avoidable patch filter.**
  - **The filter.** `R` agrees with `x - y + z` on every pattern that does not contain `2`. So by
    `avoidable-patches-of-affine-rules-inherit-linear-injectivity`, an injective realization over
    `G` needs `1 - a + b` to be a unit of `F_3[G]`, or `G` to carry a linear strict automaton.
  - **Not decisive.** Units of this shape exist, for example over `Z x Z/3` with `b = ac`. So the
    filter does not decide `R`.
  - **Open.** `R` over a nonsofic 2-generated group in which `1 - a + b` is a unit. A collision must
    use the patched pattern, either in a closed finite perturbation or in an infinite one.
