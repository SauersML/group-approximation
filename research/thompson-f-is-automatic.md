---
rg: 2
id: thompson-f-is-automatic
kind: claim
title: Thompson's group F admits an automatic structure
distinct_from:
  thompson-f-is-amenable: that claims Følner sets for F; this claims a regular language of normal forms for F with the synchronous fellow traveller property, and no known theorem links the two
  thompson-f-is-not-automatic: that is the negative answer to the same named problem, Zaremsky Problem 2.2
artifacts:
  - research/artifacts/zp-thompson-f-automatic-2026-09-13.md
---

**OPEN.** Some finite generating set of Thompson's group `F` carries an
automatic structure in the sense of Epstein et al., *Word Processing in Groups*
(1992).

Equivalent target, by the standard facts in `zaremsky-2-02-thompson-f-automatic`:
a regular language over `{x0^±1, x1^±1}` that maps bijectively onto `F`, has
the synchronous fellow traveller property, and satisfies `|w| <= N |w̄| + N`
for some `N`.

## Attempts

- **Geodesic or near-geodesic normal forms over `x0, x1`.** Dead. There is no
  regular geodesic language and there are infinitely many cone types
  (Cleary–Elder–Taback, arXiv:math/0410616). `F` is not weakly geodesically
  automatic (Belk, as cited by Hauze). By
  `thompson-f-has-no-near-geodesic-automatic-structure` (Hauze, Theorem 1.1), any
  automatic structure over `{x0^±1, x1^±1}` has words with unbounded additive
  excess over geodesic length. Linear excess is still allowed.
- **The standard infinite normal form, rewritten over `x0, x1`.** It underlies the
  1-counter graph automatic structure of Elder–Taback (arXiv:1501.04313). Right
  multiplication by `x0` shifts indices `x_i -> x_(i+1)` throughout the word, and
  the rewriting `x_i = x0^-(i-1) x1 x0^(i-1)` then changes along the whole word,
  so synchronous fellow travelling is not expected. No proof is recorded.
- **Forest-diagram tours (Belk–Brown).** Words that tour the forest diagram and
  build carets at the pointer. The expected obstacle: a single caret move can
  change where a canonical tour must start, so the words for `g` and `g x1`
  diverge at the beginning rather than at the end, as for tour normal forms of
  lamplighter groups. Viable only with a tour order whose local changes affect a
  bounded suffix after reparametrization. Not attempted beyond this observation.
