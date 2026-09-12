---
rg: 2
id: ternary-three-address-injective-automata-have-balanced-rules
kind: claim
title: Over every group, an injective three-symbol automaton with three memory elements has a balanced rule
distinct_from:
  three-address-binary-injective-rules-are-balanced: that settles two symbols, where every unbalanced rule has a blind coordinate to flip; this is the three-symbol case, where blind pairs of different coordinates can disagree and single-site changes are never invisible.
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
- **Pre-injective on free memory** (w3-bal-design, `pair-distinct-ternary-rules-pre-injective-on-free-memory`).
  - **Their result.** Suppose each address has one fixed blind pair and the three pairs are distinct.
    Then the automaton is pre-injective whenever `a, b` generate a free group.
  - **`R` qualifies,** with pairs `{0,1}`, `{1,2}` and `{0,2}`, each at a single context.
  - **Consequence.** Free groups are sofic, so `R` is not injective there. But any two configurations
    with the same image differ at infinitely many sites. So a finite-perturbation exclusion of `R`
    has to use relations among `a, b`.
  - **Pressure point.** Their example `x + y + z + [x = (0,1,2)]` sends all three constants to `0`.
    So it is only a pre-injectivity example, never a candidate for injectivity.
- **Constant background with a unit linear part** (w3-bal-design, `constant-background-kills-unit-linear-defect-rules`, Theorems 13 and 13'; checked in artifact Section 7).
  - **Unit case for `R`.** Suppose `1 - a + b` is a unit. Then `R` is not injective unless, for every symbol
    `c`, Theorem 13' leaves a nontrivial absorbed translate of `{1, a, b}` that shows `(0,2,2)`.
    With background `1`, only the perturbed configuration can carry such a translate.
  - **Non-unit case.** By avoidable patches, an injective `R` gives a linear strict automaton over `G`. So `R`
    would not be a new kind of counterexample.
  - **Residue for `R`.** Groups where `1 - a + b` is a unit and every background symbol has an absorbed
    translate.
- **Rigid rules with repeated pairs.**
  - **Example.** `x + y + 2z` with `(0,1,2)` moved from `2` to `0`. Pairs `{0,1}`, `{1,2}`, `{1,2}`; identity
    diagonal; counts `10, 9, 8`.
  - **Coverage.** Its pattern uses every symbol with augmentation `1`. The distinct-pairs corollary misses it,
    and Theorem 13' covers it.
- **Patches repeating a symbol reduce to linear strictness** (w4-bal-rigid,
  `single-patch-ternary-rules-reduce-to-linear-strictness`, artifact
  `single-patch-ternary-rules-linear-reduction-2026-09-12.md`).
  - **Result.** Let an affine rule be patched at one pattern `(s_0, s, s)`, on any placement
    `{1, a, b}`. If `a` and `b` do not commute and the linear part `L` is surjective, the automaton is
    not injective. If `L` is bijective, it is not even pre-injective.
  - **Method.** A preimage of `-epsilon delta_h` is filled greedily. `s` is kept off every site except
    `hM`, and in the involution case `(a^-1 b)^2 = 1` one extra site stays off `s_0`. Then the
    pattern occurs only at `h`.
  - **For `R`.** The unit case and its absorbed-translate residue are closed. `R` is injective over
    `G` only if `x - y + z` is a linear strict automaton over `G`.
  - **What remains.**
    - Single patches with three distinct symbols. The collision attempt dies only when the preimage
      is a constant `kappa` on `M` with `kappa (c_1 + c_2 + c_3) = -epsilon`, and only under further
      value coincidences (artifact 2.2).
    - Rules at distance at least 2 from every affine rule.
- **Every single patch now reduces to linear strictness** (w5-bal-distinct,
  `distinct-symbol-patch-ternary-rules-reduce-to-linear-strictness`, artifact
  `distinct-symbol-patch-collision-2026-09-12.md`).
  - **Distinct symbols.** The danger case closes over every placement with no commutation hypothesis.
    Break every window at coordinate `i`, break the one dangerous window at a second site, and read
    the failure off `L(d_0)(m_(i+1) m_i^-1) = 0`. All three indices stuck gives `c_1 = c_2 = c_3 = -S`,
    so `S = 0`, contradicting `kappa S = -epsilon`.
  - **Constant patches.** Constant configurations collide.
  - **Net.** A rule differing from an affine rule at one pattern is injective only where its linear
    part is a linear strict automaton over `F_3`.
- **Several patches** (same artifact, Section 3; open claim
  `two-patch-ternary-rules-reduce-to-linear-strictness`).
  - **Transfer.** If the patches share a symbol, avoidable patches still apply, so only a unit linear
    part is new.
  - **Proposition 4.** The coordinate breaker survives only at coordinates where all patches agree.
  - **Proposition 5.** On a constant background, several patches leave a finite absorbed-translate
    residue.
  - **Seed.** `(x_1 - x_a + x_b) + [(0,1,2)] + [(1,2,0)]`, with two patch symbols at every address. Open.
