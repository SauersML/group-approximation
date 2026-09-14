---
rg: 2
id: support-three-zero-divisor-quasimorphism-bound-five-thirds
kind: claim
title: Every homogeneous quasimorphism is at most five thirds of its defect on the differences of a support-three zero divisor
distinct_from:
  support-three-zero-divisor-differences-bounded-quasimorphism: that bounds the differences by three times the defect using the positive relations qualitatively; this sharpens the constant to five thirds by counting syllables of the relations, and shows five thirds is optimal for that set of inequalities.
  zero-divisor-supports-have-no-quasimorphism-isolated-extremes: that forbids isolated extremes on supports of any size; this is a bound on all three differences when the support has three points.
  kaplansky-zero-divisor-conjecture: that is the conjecture; this is an established necessary condition on support-three counterexamples.
artifacts:
  - research/artifacts/hl-zd-amplification-2026-09-13.md
---

**ESTABLISHED.** Let `G` be torsion-free, `k` a field, and `alpha in k[G]` a left
or right zero divisor with `supp alpha = {a_0, a_1, a_2}`. For every
homogeneous quasimorphism `phi` on `G` with defect `D = D(phi)` (definitions as in
`zero-divisor-supports-have-no-quasimorphism-isolated-extremes`) and all `i, j`,

```text
|phi(a_i^-1 a_j)| <= (5/3) D(phi).
```

**Syllable lemma (used in the proof, any group).** Let `p, q in G`, and suppose a
product of elements of `{p, q}` in which both letters occur equals `1`. Then no
homogeneous quasimorphism satisfies `phi(p) >= 0`, `phi(q) >= 0` and
`phi(p) + phi(q) > 2 D(phi)`, and none satisfies `phi(p) <= 0`, `phi(q) <= 0` and
`phi(p) + phi(q) < -2 D(phi)`. This strengthens step (2) of
`zero-divisor-quasimorphism-isolated-extremes-proof`, which forbids only
`phi > D` on both letters.

**Consequences.**
1. If `a_i^-1 a_j in [G, G]`, then `scl_G(a_i^-1 a_j) <= 5/6`, through Bavard duality
   as quoted in `support-three-zero-divisor-differences-bounded-quasimorphism`
   (Calegari, *scl*, Theorem 2.70). This improves `3/2`.
2. *Sieve.* A support triple is excluded in any torsion-free group carrying a
   homogeneous quasimorphism with `|phi(a_i^-1 a_j)| > (5/3) D(phi)` for some pair.
3. *Optimality for the method.* The values
   `(phi(x), phi(y), phi(x^-1 y)) = (5D/3, D/3, -D/3)` satisfy the defect
   inequality for `x^-1 y` and every constraint the syllable lemma extracts from the
   three positive relations of consequence 4 of
   `zero-divisor-support-vertex-cones-contain-positive-relations`. So a constant
   below `5/3` needs input beyond those relations and the defect inequality.

*Scope.* Elementary. No novelty is claimed. The proof uses only the three
positive relations, so the bound holds in every group containing `x, y` with those
relations, zero divisor or not; `three-positive-relations-allow-positive-scl` shows
such groups can have nonzero quasimorphisms on all three differences.

DERIVATION
[[support-three-quasimorphism-five-thirds-proof]]
