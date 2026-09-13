---
rg: 2
id: bernoulli-shifts-above-rokhlin-supremum-are-isomorphic
kind: claim
title: Over a group with finite Rokhlin supremum, Bernoulli shifts whose base entropies exceed the supremum are all isomorphic
distinct_from:
  rokhlin-entropy-is-the-bernoulli-approximation-threshold: that proves the weak* approximation of Bernoulli measures by isomorphic shift models above the supremum; this asks that the approximations close, giving actual isomorphisms.
  bernoulli-entropy-counterexample-constraints: that proves a collapsing pair must lie at or above the supremum; this is the converse, that every pair above it collapses.
  bernoulli-shifts-with-equal-base-entropy-are-isomorphic: that is Seward's theorem that base entropy is sufficient; this asks that Rokhlin entropy, min(base entropy, supremum), be sufficient.
  zero-rokhlin-supremum-forces-bernoulli-collapse: that asks for one collapse when the supremum is zero; this asks for total collapse above any finite supremum, and implies it (route collapse-above-supremum-gives-zero-supremum-collapse).
---

**OPEN.** Let `G` be a countably infinite group with `s = h^Rok_sup(G) < ∞`. For all standard
probability spaces with `s < H(L, lambda) < H(K, kappa) < ∞`, the Bernoulli shifts `L^G` and `K^G` are
isomorphic.

**What it says.**
- By Seward's Theorem 1.10 (`seward-per-group-rokhlin-entropy-of-bernoulli-shifts`),
  `h^Rok_G(L^G) = min(H(L), s)`. So the claim is: Rokhlin entropy is a complete isomorphism invariant of
  Bernoulli shifts over every group.
- It is the exact form of `rokhlin-entropy-is-the-bernoulli-approximation-threshold`, whose approximations
  above `s` go both ways.
- Model tests.
  - Sofic groups have `s = ∞`, so the claim is vacuous there, as it must be.
  - A trivial world with `s = 0` would make all nontrivial finite-entropy Bernoulli shifts isomorphic,
    matching the total collapse of `bernoulli-isomorphism-collapse-set-is-a-subgroup`, item 5.
  - No group with `s < ∞` is known, so nothing tests it against a known example.

**Reformulation.** `L^G ≅ K^G` iff `K^G` has a generating partition `alpha` with distribution `lambda` whose
`G`-translates are independent. Pull back the coordinate partition; conversely, `x ↦ (g ↦ alpha(g^-1 x))`
pushes the measure to `lambda^G` by independence and is injective by generation. Above `s`, Seward's Krieger
theorem gives generating partitions with distribution exactly `lambda`, because
`h^Rok_G(K^G) = s < H(lambda)`. This is Part I, Theorem 1.1, as quoted in
`research/artifacts/rokhlin-entropy-self-copy-dichotomy-2026-09-12.md` (S3). So the claim asks only that one
of them can be taken with independent translates.

## Attempts

- **Algebra.** Dead as a mechanism. Algebraic identities among free and finite-subgroup-induced modules conserve
  the lifted trace, which equals the entropy the co-induced Ornstein theorem adds
  (`finite-subgroup-induced-absorption-conserves-entropy`).
- **Relative Ornstein recoding.** Dead as a mechanism. Seward-type isomorphisms fix a common factor and recode
  i.i.d. rows along an aperiodic `T`. Ornstein's theorem for `Z` then forces equal row entropy (Attempts on
  `bernoulli-shift-entropy-classifies-for-every-group`). A collapse must recode many rows jointly, or move the
  common factor.
- **Factor maps.** Over groups containing `F_2`, `K^G` factors onto `L^G` (Bowen, arXiv:0812.2718), with no
  control of injectivity. Seward's small generating partitions (Theorem 6.7 mechanism) record information on a
  transversal of a finite subgroup. They are generating but carry no independence.
- **What a proof needs.** An Ornstein-type upgrade in which the entropy hypothesis is replaced by "above `s`".
  Perturb a Krieger generating partition with distribution `lambda` towards independence of translates while
  keeping it generating, and converge in `L^1`. The finitely determined property of Bernoulli shifts is known
  only through amenable or sofic counting.
