---
rg: 2
id: kl-length-six-residue-squares-and-fourth-powers-inject
kind: claim
title: Length-six +++++- words that are a square or a fourth power times a loop coefficient inject over every group
distinct_from:
  kl-even-syllable-words-reduce-to-shorter-equations: that settles the ++++-- families lying in G * <t^2>; this settles four +++++- sub-cases of the residue, where the word is u^2 c or u^4 c for an inner word u that has a sign change.
  kl-length-six-coincidence-saturated-torsion-residue: that is the open statement for whole residue shapes; this proves injectivity only on the sub-cases where the lone label g equals a loop coefficient or its inverse.
---

Let `G` be any group and

```text
w = t a_1 t a_2 t a_3 t a_4 t y t^(-1) x,     a_i, x, y in G,
```

a word of class `+++++-`. Under each hypothesis below, an identity in `G * <t>`
writes `w` as a square or a fourth power times a loop coefficient:

| | Hypothesis | Identity |
|---|---|---|
| (S1) | `a_4 = a_2`, `a_3 = y a_1` | `w = u^2 x`, `u = t a_1 t a_2 t y t^(-1)` |
| (S2) | `a_3 = a_1`, `a_2 = a_4 x` | `w` is conjugate to `u^2 y`, `u = t^(-1) x t a_1 t a_4 t` |
| (S3) | `a_2 = a_3 = a_4 = y a_1` | `w = u^4 x`, `u = t a_1 t y t^(-1)` |
| (S4) | `a_1 = a_2 = a_3 = a_4 x` | `w` is conjugate to `u^4 y`, `u = t^(-1) x t a_4 t` |

In each case `G -> (G * <t>)/<<w>>` is injective. Nothing is assumed about the
orders of `x`, `y` or the labels.

**Residue sub-cases.** Take the normalized shapes of
`kl-length-six-coincidence-saturated-torsion-residue`, whose P-labels lie in
`{1, g}` with `g != 1`. The hypotheses hold in exactly these cases:
- `(1,1,g,1)` with `g = y`, by (S1);
- `(g,1,1,1)` with `g = y^(-1)`, by (S1) and (S3);
- `(1,g,1,1)` with `g = x`, by (S2);
- `(1,1,1,g)` with `g = x^(-1)`, by (S2) and (S4).

No other shape of that list meets any of (S1)-(S4):
- `(1,1,1,1)` and `(1,g,1,g)` would need a loop coefficient equal to `1`;
- `(1,1,g,g)` and `(1,g,g,1)` fail every same-label condition.

With involution loops these are the four three-equal shapes with `g` equal to
the loop coefficient named in the list. Whole shapes stay open.

DERIVATION
kl-length-six-residue-power-words-proof
