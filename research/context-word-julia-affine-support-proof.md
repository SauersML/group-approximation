---
rg: 2
id: context-word-julia-affine-support-proof
kind: route
title: Diagonalize the commuting context words on the Julia Gram source
target: context-word-julia-rows-only-cut-affine-supports
requires:
  - free-julia-grading-carries-one-gram-at-canonical-quarter-mass
---

The joint spectral projections of the context subgroup are

```text
p_v=2^(-k) product_i(1+(-1)^(v_i)x_i).                 (CJW3)
```

They are mutually orthogonal and sum to one.  On `p_v`, the word `h_l` is
the scalar

```text
s_l (-1)^(sum_i a_(l,i)v_i).                           (CJW4)
```

The equation `h_lG=G`, after left multiplication by `p_v`, gives

```text
(s_l (-1)^(a_l dot v)-1)p_vG=0.                        (CJW5)
```

Thus `p_vG!=0` implies `(CJW2)`.  The simultaneous solution set of those
equations is affine.  Conversely, the displayed return equations impose no
further characterwise restriction, so enlarging the finite list merely
intersects more affine hyperplanes.  Since affine equations true on all
points of a set are true on its affine hull, no such family can delete a
ghost belonging to that hull while retaining every honest point.

