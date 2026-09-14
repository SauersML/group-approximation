---
rg: 2
id: kms-vertex-words-close-iff-weights-have-zero-height-moments
kind: claim
title: An alternating word in the KMS vertex groups U_3(p) and U_4(p) is trivial exactly when its x-exponents have vanishing moments at the heights traced by its y-exponents
distinct_from:
  kms-girth-surfaces-give-surface-subgroups: that turns labelled girth surfaces into surface subgroups; this characterizes which vertex words are trivial, so it describes the local condition that a labelling must meet
artifacts:
  - experiments/kms-surface-girth-general/check_moment_lemma.py
  - experiments/kms-surface-girth-general/check-moment-lemma.log
---

**ESTABLISHED.** Let `p` be an odd prime. Let `U_3 = <x,y | x^p, y^p, [x,y,x], [x,y,y]>` and
`U_4 = <x,y | x^p, y^p, [x,y,x], [x,y,y,x], [x,y,y,y]>` (left-normed commutators, `[x,y] = x^{−1}y^{−1}xy`), the
vertex groups of `kms-girth-surfaces-give-surface-subgroups`, with `x` the designated generator of `U_4`. Put
`m = 3` for `U_3` and `m = 4` for `U_4`.

For `a_1, …, a_m, b_1, …, b_m ∈ F_p` consider the alternating word

```text
w = x^{a_1} y^{b_1} x^{a_2} y^{b_2} ⋯ x^{a_m} y^{b_m},      heights H_r = b_1 + ⋯ + b_{r−1}  (H_1 = 0).
```

**1. Moment criterion.** `w = 1` exactly when

```text
b_1 + ⋯ + b_m = 0     and     a_1 H_1^d + ⋯ + a_m H_m^d = 0   for d = 0, 1, …, m − 2.
```

**2. Classification.** Suppose every `a_r` and every `b_r` is nonzero. Then `w = 1` exactly when:
- `m = 3`: `a = λ (H_2 − H_3, H_3 − H_1, H_1 − H_2)` for some `λ ≠ 0`; the three heights are then pairwise distinct;
- `m = 4`: either the four heights are pairwise distinct and `a_r = λ / ∏_{s ≠ r} (H_r − H_s)` for some `λ ≠ 0`
  (generic words), or `H_1 = H_3 ≠ H_2 = H_4` and `a = (a_1, a_2, −a_1, −a_2)` (alternating words).

**3. Counts.** The number of trivial alternating words with all exponents nonzero is `(p−1)^2 (p−2)` in `U_3` and
`(p−1)^2 ((p−2)(p−3) + (p−1))` in `U_4`, of which `(p−1)^3` are alternating.

A word whose first letter is a power of the non-designated generator is a cyclic rotation of one of this form,
so the criterion applies to every closed link walk of a girth surface. In a vertex group of a girth surface the
exponents are the edge labels read along the walk (`kms-girth-surfaces-give-surface-subgroups`, vertex
condition): the labels on sides of the designated type are the weights `a_r`, and the labels on the other sides
are the height increments `b_r`.

Proof: `kms-vertex-words-zero-height-moments-proof`. `check-moment-lemma.log` compares the collection law, the
moment criterion, the classification and the counts on every word with nonzero exponent sums, for
`p = 3, 5, 7, 11, 13` (`U_3`) and `p = 5, 7, 11, 13` (`U_4`).
