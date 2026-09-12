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
- **Constant background with a unit linear part** (w3-bal-design, `constant-background-kills-unit-linear-defect-rules`, checked in artifact Section 7).
  - **Unit case for `R`.** Let `1 - a + b` be a unit with inverse `K`, and put `y = tau_K(delta_1)`.
    - Configurations: `x = 1` off `M`, `x = p + y` on `M`, and `x' = x - y`.
    - Result: `tau_R(x) = tau_R(x')` unless some translate `hM` with `h != 1` lies in `M ∪ supp(y)` and has
      `x'|_(hM) = (0,2,2)`.
    - Why only `x'` matters: `x` shows `p` only at translates with `hM = M`, and those make `<M>` cyclic.
  - **Non-unit case.** By avoidable patches, an injective `R` gives a linear strict automaton over `G`. So `R`
    would not be a new kind of counterexample.
  - **Residue for `R`.** Groups where `1 - a + b` is a unit and the witness above has an absorbed translate.
    Other backgrounds or right-hand sides may still kill these.
- **Rigid rules with repeated pairs.** The distinct-pairs corollary does not reach them, because the moved
  pattern can use every symbol with nonzero augmentation.
  - Example: `x + y + 2z` with the value at `(0,1,2)` moved from `2` to `0`. It has pairs `{0,1}`, `{1,2}`,
    `{1,2}`, identity diagonal, and counts `10, 9, 8`.
  - Constant background `c` still applies, with a weaker exception. Only translates with at most one site
    outside `M ∪ supp(y)`, at the address where `p_m = c`, can show `p`. Each choice of `c` gives its own
    finite exception set.
