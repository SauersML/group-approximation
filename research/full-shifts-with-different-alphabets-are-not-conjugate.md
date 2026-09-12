---
rg: 2
id: full-shifts-with-different-alphabets-are-not-conjugate
kind: claim
title: Over every countably infinite group, full shifts on alphabets of different sizes are not topologically conjugate
distinct_from:
  gottschalk-surjunctivity-conjecture: that asks every injective cellular automaton on one full shift to be surjective, and it is open; this is the elementary fact that a conjugacy bijects the constant configurations, so it separates no hypotheses.
  bernoulli-shift-entropy-classifies-for-every-group: that is the measurable isomorphism classification of Bernoulli shifts by base entropy, open over nonsofic groups; this is the topological conjugacy classification, which is elementary because conjugacies biject fixed points, and fixed points are null for every Bernoulli measure.
  measurable-alphabet-compression-over-leavitt-units: that asks for a Borel code into fewer symbols injective almost everywhere, where fixed points are invisible; this concerns homeomorphisms, where fixed points already obstruct.
artifacts:
  - research/artifacts/gk-p-inf-wild-borel-and-topological-2026-09-12.md
---

Let `G` be a countably infinite group and `A`, `B` finite alphabets with `|A| != |B|`. There is no
equivariant homeomorphism `A^G -> B^G`. More generally, if `|A| > |B|` there is no equivariant
injection `A^G -> B^G`, continuous or not.

**ESTABLISHED 2026-09-12** by [[full-shifts-with-different-alphabets-are-not-conjugate-proof]]: the
points fixed by the whole group are the `|A|` constant configurations, and an equivariant injection
maps fixed points injectively to fixed points.

**Correction.** This claim was landed at de573302d0 as OPEN and described as a sharp negative target,
weaker than both Gottschalk and Bernoulli maximality. That was wrong. The lead's calibration counts
the points fixed by a proper finite-index subgroup; taking the subgroup to be `G` itself settles every
group. The routes `alphabet-conjugacy-invariance-from-gottschalk` and
`alphabet-conjugacy-invariance-from-bernoulli-maximality` are valid but redundant.

**What it records.** Topological invariants see fixed and periodic points, and a Bernoulli measure
ignores them. So alphabet size is a trivial conjugacy invariant and an open measurable one. The
content-bearing form is `measurable-alphabet-compression-over-leavitt-units`. On a group with no
proper finite-index subgroup, which includes every infinite simple group, the constants are the only
finite fixed-point set, so periodic-point counting constrains a strict automaton by nothing beyond
this claim (Section 5 of the artifact).
