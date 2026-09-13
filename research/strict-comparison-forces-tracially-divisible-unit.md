---
rg: 2
id: strict-comparison-forces-tracially-divisible-unit
kind: claim
title: Strict comparison makes the unit tracially divisible for simple separable nuclear algebras
distinct_from:
  stw99-problem-lxv-jiang-su-embeddings: that asks which unital algebras contain a unital Z, a question whose unrestricted form fails for simple nuclear AH algebras; this asks only for tracially large order zero division of the unit, and only under strict comparison.
  stw99-problem-xxviii-tracial-divisibility-gamma: that assumes Winter's tracial divisibility of every positive element and asks for Gamma; this asks whether strict comparison gives tracial divisibility of the single element 1.
  stw99-problem-xxvii-comparison-vs-divisibility: that asks whether strict comparison gives almost divisibility of every Cuntz class; this asks for almost divisibility of the class of the unit only.
  rank-density-and-strict-comparison-give-purity: that derives purity from rank density of all continuous profiles; this asks for existence at the constant profiles 1/N, which on Bauer simplices generate all profiles.
  strict-comparison-unit-divisibility-equivalences: that proves the equivalent forms of divisibility of the unit under strict comparison; this asks whether strict comparison produces any of them.
artifacts:
  - research/artifacts/ex-toms-winter-bauer-divisible-unit-part2-2026-09-12.md
  - research/artifacts/ex-toms-winter-unit-divisibility-equivalences-2026-09-12.md
  - research/artifacts/ex-tw-c-space-unit-division-part2-2026-09-13.md
---

**OPEN.** Let `A` be a unital, simple, separable, nuclear, non-elementary, stably
finite C*-algebra with strict comparison of positive elements. Then for every `N`
and `ε > 0` there is a c.p.c. order zero map `φ: M_N → A` with `τ(φ(1)) > 1 − ε`
for every `τ ∈ T(A)`.

**Equivalent forms** (`strict-comparison-unit-divisibility-equivalences`):
- for every `n` some `x ∈ W(A)` has `n x ≤ [1_A] ≤ (n+1) x` (Rørdam–Winter's
  divisibility of the unit);
- for every `n ≥ 2` there is a unital `*`-homomorphism `Z_{n,n+1} → A`;
- the uniform tracial ultrapower contains a unital copy of every `M_N`.

**Why it matters.** When `T(A)` is a Bauer simplex and `A` has tracially locally
finite nuclear dimension, this claim is equivalent to Toms–Winter for `A`
(`toms-winter-bauer-tlfnd-iff-tracially-divisible-unit`). It gives
`toms-winter-holds-on-bauer-tlfnd-locus` through route
`toms-winter-bauer-tlfnd-via-divisible-unit`. It is part (1) of STW XXVII at the
single class `[1_A]`.

**Model test.**
- `C([0,1])` admits no nonzero order zero map from `M_2`, so it fails the
  conclusion; it is not simple.
- Every `Z`-stable algebra satisfies it.
- Dadarlat–Hirshberg–Toms–Winter (arXiv:0712.2020) give a unital simple nuclear AH
  algebra with no unital `Z_{3,4}`. So it fails the second form, and it fails
  strict comparison. Without strict comparison the forms need not be equivalent.

## Attempts

- **Glimm halving.**
  - Glimm's lemma gives order zero `M_n` in every hereditary subalgebra, but its rank
    profile is uncontrolled across traces.
  - Greedy accumulation only adds profiles, so it overshoots where the rank is
    already large.
- **Localized rank bumps (Bauer simplex).** Locally the conclusion holds.
  - Near an extreme trace `λ_0`, lift a trace-`t` projection of the fibre `R` to a
    near projection `c`. Then `d_λ((c − 1/2)_+)` stays near `t` on a neighbourhood.
  - Compress with a central bump `ψ` of the strict closure and approximate from `A`
    in 2-norm. By Markov, `d_λ((a − 1/2)_+) ≤ 2λ(a)`, so the rank is small off the
    bump and near `t` in its core.
  - Summing bumps over a cover gives rank in `[t − η, 2·ord·t + η]`, where `ord` is
    the order of the cover. The window `(1/(n+1), 1/n)` needs ratio below
    `(n+1)/n`. This estimate is useless already in dimension one, where it gives
    ratio 4. Ramps and overlaps are the whole problem.
- **Central staircases with orthogonalizing moves (Bauer simplex): proved over
  C-space boundaries** (2026-09-13, lane `ex-tw-rotation-gluing`,
  `bauer-c-space-strict-comparison-divides-unit`).
  - This repairs the overshoot of localized bumps. A central staircase switches on the
    `N` pieces of a local division one at a time, so the overshoot per active piece is
    `1/N`, not `t`.
  - Strict comparison moves each piece into the exact orthogonal complement of the
    earlier ones, with rank margin `1 − t − ε`. Ranks add over orthogonal sums, so
    errors do not compound.
  - With a fixed number of colours this handles finite-dimensional boundaries.
    Haver's property C, with precisions `(N_k, δ_k)` and `Σ_k (1/N_k + δ_k)^{1/2}` small,
    handles every C-space boundary.
  - Consequences: purity for exact algebras there, and `Z`-stability under tlfnd
    (`bauer-c-space-strict-comparison-pure-and-z-stable`).
  - Local-to-global principle: `bauer-strict-comparison-unit-division-is-local`.
  - **Exact characterization on Bauer simplices**
    (`bauer-unit-division-iff-summable-local-division`). The unit divides iff, for every
    `ε`, some finite cover of `K` by local divisions of weights `(1/N_i + δ_i)^{1/2}` has
    weights summing to at most `ε` at every point. Failure lives on a closed locus in
    the C-kernel of `K`.
  - **Where it dies.** Strongly infinite-dimensional boundaries such as the Hilbert
    cube. There, if local divisions at precision `N` shrink in unboundedly many
    coordinates, no finite family of disjoint levels with summable precision covers.
    The covers depend only on the precision, so the scheme is non-adaptive, and
    property C is its natural domain.
- **Rotation gluing.** On C-spaces it is not needed: the moves above use only global
  comparisons. Beyond C-spaces it would need partial isometries between local halvings
  on overlaps. Strict comparison supplies those only between global projections of
  equal trace (`strict-comparison-bundle-certificate-vanishes`), and such projections
  are what is being constructed.
- **Closed versus open windows.** Weak divisibility `[1] = 2a + 3b` gives
  `2z ≤ [1] ≤ 3z` with `z = a + b`, but only closed rank bounds. The level-`(3n+1)`
  trick of the equivalences artifact converts almost divisibility at large levels
  into open windows. No mechanism turns strict comparison into large-level
  divisibility.
- **Where a counterexample must live** (Bauer simplex with tlfnd). Strict comparison
  together with DHTW-type rigidity of the unit in tracially uniform form:
  - not AH;
  - no unital simple infinite-dimensional unique-trace subalgebra;
  - no unital `Z_{n,n+1}` for large `n`;
  - some locally infinite-dimensional extreme trace
    (`bauer-gamma-failure-localizes-to-infinite-dim-point`);
  - no comparison certificate (`strict-comparison-bundle-certificate-vanishes`);
  - an extreme boundary without property C
    (`bauer-c-space-strict-comparison-divides-unit`), and a nonempty closed division
    locus (`bauer-strict-comparison-unit-division-is-local`).
