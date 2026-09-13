---
rg: 2
id: thompson-v-powers-have-linearly-growing-slope
kind: claim
title: An infinite-order element of V_n has a periodic point at which the log-slope of its z-th power grows linearly in z
distinct_from:
  thompson-v-cyclic-subgroups-are-undistorted: that is undistortion inside V_n; this is the slope estimate its proof rests on, which is a statement about germs and so survives passage to any ambient group whose length function bounds germ degrees.
  thompson-elements-are-undistorted-in-leavitt-unit-group: that is the consequence inside the binary Leavitt unit group; this is the imported dynamical estimate.
---

**ESTABLISHED** by `thompson-v-powers-have-linearly-growing-slope-citation`.

Let `n >= 2` and let `alpha` be an element of `V_n` of infinite order. Then there are:
- a periodic point `y_0` of `alpha`;
- integers `u >= 1` and `L >= 1`;
- a constant `C`,

such that for every `z >= 1` the germ of `alpha^z` at `y_0` is an affine map of slope
`b^(e(z))` with

```text
e(z) = L (floor(z/u) + 1) + S(z),     |S(z)| <= C,
```

where `b` is the scaling base of the source's realization of the Cantor set.

The same holds for negative powers, at a periodic point of `alpha^-1`.

**Translation to prefix replacements.** A germ `beta w -> alpha' w` scales by
`b^(|beta| - |alpha'|)` in that realization. Its degree `|alpha'| - |beta|` therefore
has absolute value `e(z)`, and it grows linearly in `z`.
