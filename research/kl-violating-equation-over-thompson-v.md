---
rg: 2
id: kl-violating-equation-over-thompson-v
kind: claim
title: A Kervaire--Laudenbach-violating equation with coefficients in Thompson's group V
refuted_by: [kl-holds-over-thompson-v]
distinct_from:
  kl-violating-equation-over-leavitt-unit-group: that allows any coefficients from the binary Leavitt unit group; this restricts every coefficient to the copy of Thompson's V inside it, so a witness here is a witness there but not conversely.
  thompson-v-not-hyperlinear: that is non-hyperlinearity of V by any certificate; this asks for one algebraic certificate of it, a nonsingular equation over V with no solution in any overgroup.
  kl-holds-over-thompson-v: that is the positive statement over V; this is its negation, and exactly one of the two can end up established.
---

**OPEN.** There are `w in V * <t>` with `deg_t(w) != 0` and `1 != a in V`
such that `a` dies in `(V * <t>)/<<w>>`.

## Consequences

- **A Leavitt violation.** By `leavitt-kl-violation-from-thompson-v-violation`,
  the same word is a violation over `R^x = L_(F_2)(1,2)^x`.
- **V is not hyperlinear.** By `thompson-v-not-hyperlinear-from-kl-violation`,
  through `kervaire-laudenbach-holds-for-hyperlinear`.

## Why V is a reasonable search space for the violation lane

- **Checkable.** Coefficients are prefix replacements, so products and
  equality are decided by tree-pair normal forms. Because
  `V <= EL_D(R) <= R^x` (`leavitt-cylinder-swaps-generate-thompson-in-el`),
  every candidate is also checkable by the shared Leavitt checker.
- **A different kind of certificate.** Inside V no compression criterion of
  this graph applies (`thompson-v-has-no-rigid-compression-defect`,
  `thompson-v-has-haagerup-property`). A violation over V would certify
  non-hyperlinearity by a mechanism no rigid-defect argument can supply.

## Attempts

1. **Short and generic words.** Dead, for every coefficient group and so
   over V.
   - Variable length at most five: Evangelidou (`length-five-kl-fence-citation`).
   - `t` occurring with one sign only: Levin's positive-equation theorem,
     Bull. Amer. Math. Soc. 68 (1962), 603--604, as cited in
     `length-five-kl-fence-citation`.
   - At least four light same-sign corners: `kl-four-same-sign-corner-words-inject`.
   - Small-cancellation words: `kl-small-cancellation-words-inject-every-coefficient-group`.
2. **Structured candidates.** Deferred. No candidate family over V has been
   proposed. Any surviving word must evade every fence in item 1 with
   coefficients drawn from V.
3. **Exhaustive generator census at variable length six and seven (2026-09-13).** No violation found.
   - **Census:** every `t`-exponent is `+-1` and coefficients are in `{1, a, b, b^(-1), c}`.
     That gives `181202` classes up to rotation and `w -> sigma(w^(-1))`.
   - **Certified injective:** `85432` classes, by
     `kl-thompson-v-short-generator-words-certified-injective`:
     - finite coefficient subgroup: `63678`;
     - four light corners: `4380`;
     - proper powers: `6`;
     - three light corners with (D4) and (A2): `15204`;
     - exact retractions onto V: `2164`.
   - **Collapse test.** The `113144` words left after the first two filters were each run
     through Todd--Coxeter enumeration over `<t>`, using the nine Bleak--Quick relators
     plus `w`, at `200000` cosets. All `113144` overflowed and none collapsed (MSI job array 731591).
     - V is simple, so a violation shows up exactly as index 1.
     - An overflow certifies nothing.
   - **Frontier:** `95770` words, by class in
     `research/artifacts/kl-thompson-v-generator-census-2026-09-13.md`.
   - **What a violation needs.** A violation of variable length at most seven with generator
     coefficients lies in the frontier and needs a coset budget above `200000`. Longer words
     or coefficients beyond the generators are untouched.
