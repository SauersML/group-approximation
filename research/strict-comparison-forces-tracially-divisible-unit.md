---
rg: 2
id: strict-comparison-forces-tracially-divisible-unit
kind: claim
title: Strict comparison makes the unit tracially divisible for simple separable nuclear algebras
distinct_from:
  stw99-problem-lxv-jiang-su-embeddings: that asks which unital algebras contain a unital Z, a question whose unrestricted form fails for simple nuclear AH algebras; this asks only for tracially large order zero division of the unit, and only under strict comparison.
  stw99-problem-xxviii-tracial-divisibility-gamma: that assumes Winter's tracial divisibility of every positive element and asks for Gamma; this asks whether strict comparison gives tracial divisibility of the single element 1.
  stw99-problem-xxvii-comparison-vs-divisibility: that asks whether strict comparison gives almost divisibility of every Cuntz class; this asks for trace-large order zero division of the unit only.
  rank-density-and-strict-comparison-give-purity: that derives purity from rank density of all continuous profiles; this asks for existence at the constant profiles 1/N, which on Bauer simplices generate all profiles.
artifacts:
  - research/artifacts/ex-toms-winter-bauer-divisible-unit-part2-2026-09-12.md
---

**OPEN.** Let `A` be a unital, simple, separable, nuclear, non-elementary, stably
finite C*-algebra with strict comparison of positive elements. Then for every `N`
and `ε > 0` there is a c.p.c. order zero map `φ: M_N → A` with `τ(φ(1)) > 1 − ε`
for every `τ ∈ T(A)`. Equivalently, the uniform tracial ultrapower `A^U` contains
a unital copy of every `M_N`.

**Why it matters.** When `T(A)` is a Bauer simplex and `A` has tracially locally
finite nuclear dimension, this claim is equivalent to Toms–Winter for `A`
(`toms-winter-bauer-tlfnd-iff-tracially-divisible-unit`). It gives
`toms-winter-holds-on-bauer-tlfnd-locus` through route
`toms-winter-bauer-tlfnd-via-divisible-unit`. There the constant profiles `1/N`
generate every continuous profile, so the whole existence problem sits at the unit.

**Model test.**
- `C([0,1])` has no nonzero order zero map from `M_2`, so it fails the conclusion;
  it is not simple.
- Every `Z`-stable algebra satisfies it.
- By Dadarlat–Hirshberg–Toms–Winter (arXiv:0712.2020) a unital simple nuclear AH
  algebra can have a unit into which even `Z_{3,4}` does not map unitally. That
  algebra fails strict comparison. Whether its unit is tracially divisible was not
  examined.

## Attempts

- **Through `Z_{n,n+1}` (heuristic).**
  - Rørdam–Winter's Proposition 5.1 (arXiv:0801.2259, not re-read) gives unital
    `Z_{n,n+1} → A` from an order zero `φ: M_n → A` and `v` with `v*v = 1 − φ(1)` and
    `φ(e_11)v = v`.
  - Strict comparison should supply `v` once `d_τ(1 − φ(1)) < d_τ(φ(e_11))` at every
    trace. The cut-downs were not checked.
  - Unital `Z_{n,n+1}` for large `n` gives the conclusion (Lemma 3.2 of the artifact).
  - So the crux would follow from almost `n`-divisibility of `[1_A]` in `Cu(A)` for
    large `n`: a rank statement at one constant profile. No argument is known.
- **Glimm halving.**
  - Glimm's lemma gives order zero `M_n` in every hereditary subalgebra, but its rank
    profile is uncontrolled across traces.
  - Greedy accumulation adds uncontrolled profiles. Capturing a fixed fraction of
    every remainder at every trace needs half-rank elements everywhere, which is rank
    density again.
- **Where a counterexample must live** (Bauer simplex with tlfnd). Strict comparison
  together with DHTW-type rigidity of the unit in tracially uniform form:
  - not AH;
  - no unital simple infinite-dimensional unique-trace subalgebra;
  - no unital `Z_{n,n+1}` for large `n`;
  - some locally infinite-dimensional extreme trace
    (`bauer-gamma-failure-localizes-to-infinite-dim-point`);
  - no comparison certificate (`strict-comparison-bundle-certificate-vanishes`).
