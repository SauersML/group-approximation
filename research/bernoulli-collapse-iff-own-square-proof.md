---
rg: 2
id: bernoulli-collapse-iff-own-square-proof
kind: route
title: A self-square is the collapse h ~ 2h, and periodicity of the collapse subgroup produces a self-square from any collapse
target: bernoulli-collapse-iff-a-bernoulli-shift-is-its-own-square
requires:
  - bernoulli-isomorphism-collapse-set-is-a-subgroup
---

"Item n" refers to the prerequisite.

**(2) ⇒ (1).** By item 1, `X_h × X_h ≅ X_(2h)`. So `X_h ≅ X_(2h)` with `h != 2h`, and `h in D(G) \ {0}`.

**(1) ⇒ (2).**
- Take `0 != d in D(G)`. `D(G)` is a subgroup (item 3), so we may take `d > 0`.
- Item 6, with the single element `d`, gives `theta` such that `X_a ≅ X_b` whenever `a, b >= theta` and
  `b - a in dZ`.
- Choose an integer `n >= 1` with `nd >= theta`, and put `h = nd`. Then `2h - h = nd in dZ` and
  `h, 2h >= theta`, so `X_h ≅ X_(2h) ≅ X_h × X_h` by item 1.
- Every `n' >= n` works as well, so the witnesses are unbounded.

**Powers.** If `X ≅ X × X`, then by induction `X^(k+1) = X^k × X ≅ X × X ≅ X`.
