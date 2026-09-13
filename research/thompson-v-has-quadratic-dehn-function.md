---
rg: 2
id: thompson-v-has-quadratic-dehn-function
kind: claim
title: Thompson's group V has quadratic Dehn function
distinct_from:
  thompson-t-has-quadratic-dehn-function: that is Migliorini's theorem for the group T; this is the open question for V.
artifacts:
  - research/artifacts/zp-thompson-v-dehn-function-2026-09-13.md
---

**Open.** Conjecture (the V part of Zaremsky Problem 2.5): `δ_V(n) ≃ n^2`.

V contains F, and F contains `Z^2`, so V is not hyperbolic and `δ_V ≽ n^2`
(subquadratic Dehn function implies hyperbolic). The content is the upper bound.

## Attempts

- **Known upper bounds.** `n^11` (Guba 2000) and `n^6` (Lorrain, Theorem 5.7;
  `thompson-v-dehn-function-is-at-most-sextic`).
- **Where Lorrain's degree is lost (read from arXiv:2608.03813v2, pp. 51–65;
  details in the artifact, §2).** The area `A(n)` of rewriting a length-`n`
  word into Guba's normal form `p π c_(n+1)^m q^(-1)` satisfies
  `A(n) ≤ 2A(n/2) + M(n)`, where `M(n)` is the merge cost. With
  `M(n) = O(n^α)`, `α > 1`, the recursion gives exactly `O(n^α)`, so a quadratic
  merge would suffice. The sextic terms come from π-words:
  - Lemma 4.8 reduces a π-word with area `|π|_∞^2 · O(n^2)`, and
    Corollary 4.6 allows `|π|_∞ = Θ(n^2)`;
  - Lemma 4.14 costs `O(n^6)`.
- **Dead: copying Migliorini's T normal form.** Route
  `thompson-v-quadratic-via-bounded-non-f-normal-form` is invalidated by
  `thompson-v-elements-need-unboundedly-many-non-f-letters`. The order-break
  count is subadditive with `br(F) = 1`, and the depth-`k` block reversal has
  `br = 2^k`, so no normal form with boundedly many non-F letters exists.
- **Permutation inflation (heuristic, artifact §4).** Coxeter π-words of rank
  `n` can have length `Θ(n^2)`, while by counting some permutations of `N`
  cones need word length `Θ(N log N)`, with the upper bound due to Birget. A
  proof paying per Coxeter move meets the `n^6`.
- **Open strategies (artifact §5).**
  - A: Migliorini's triangle criterion (Proposition 4.3) with normal forms
    `u · Λ_1 ⋯ Λ_d · v`, where the `Λ_j` are merge-sort layers of disjoint cone
    swaps and `d = O(log br(g))`. Open lemmas: A1 lengths, A2 an F-letter past a
    layer at linear area, A3 re-sorting two stacks at quadratic area.
  - B: fillings in the Stein–Farley CAT(0) cube complex with logarithmic height
    excess, then pushing down.
  - C: Guba's F diagram lemmas for symmetric diagrams.
- Lane z2-05-v-dehn, 2026-09-13: next is lemma A2 for a single layer.
