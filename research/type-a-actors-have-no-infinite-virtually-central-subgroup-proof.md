---
rg: 2
id: type-a-actors-have-no-infinite-virtually-central-subgroup-proof
kind: route
title: Pass to the finite-index centralizer, read cosets of each point stabilizer off the ordered pairs (s, zs), and intersect the finitely many finite-index kernels
target: type-a-actors-have-no-infinite-virtually-central-subgroup
requires:
  - deligne-universal-cover-lattice-is-non-rf-kazhdan
---

Let `E` act faithfully on `S` with finitely many orbits of two-element subsets,
let `Z <= E`, and put `C = C_E(Z)` with `[E : C] < infinity`. If `|S| <= 1`, then
`E` is trivial by faithfulness, so assume `|S| >= 2`.

## Step 1: finitely many orbits on points and on ordered pairs

- **Points.** If `s_1, s_2, ...` lay in pairwise distinct `E`-orbits, the
  two-element subsets `{s_1, s_j}` (`j >= 2`) would lie in pairwise distinct
  orbits, since an orbit of a two-element subset determines the unordered pair
  of point orbits of its elements. So there are finitely many point orbits.
- **Ordered pairs.** The ordered pairs `(x, x)` fall into as many orbits as there
  are point orbits. Each orbit of two-element subsets `{x, y}` meets at most two
  orbits of ordered pairs `(x, y)`, `(y, x)`. So `E` has finitely many orbits on
  `S x S`.
- **Passing to `C`.** Write `E = C t_1 ∪ ... ∪ C t_k` with `k = [E : C]`. For any
  `E`-set `X` and `x in X`, `E x = C t_1 x ∪ ... ∪ C t_k x` is a union of at most
  `k` orbits of `C`. Applying this to `S x S`, the subgroup `C` also has finitely
  many orbits on `S x S`, hence on `S`.

## Step 2: each stabilizer meets `Z` in finite index

`C` acts faithfully on `S`, being a subgroup of `E`, and `Z` is central in `C`.
Let `O_1, ..., O_m` be the `C`-orbits on `S`. Fix `s_i in O_i` and put
`Z_i = Z ∩ Stab_C(s_i)`.

For `z, z' in Z`, suppose `c (s_i, z s_i) = (s_i, z' s_i)` for some `c in C`. Then
`c s_i = s_i`, and since `z` commutes with `c`, `c z s_i = z c s_i = z s_i`. So
`z s_i = z' s_i`, that is `z^-1 z' in Z_i`. Hence `z Z_i -> C (s_i, z s_i)` is
a well-defined injective map from `Z / Z_i` into the finite set of `C`-orbits on
`S x S`: if `z Z_i = z' Z_i` the pairs are equal, and distinct cosets give
distinct orbits by the computation above. So `[Z : Z_i] < infinity`.

## Step 3: the kernels intersect in a finite-index subgroup

For `z in Z_i` and `x = c s_i in O_i`, `z x = z c s_i = c z s_i = c s_i = x`. So
`Z_i` acts trivially on `O_i`. Then `W = Z_1 ∩ ... ∩ Z_m` acts trivially on
`S = O_1 ∪ ... ∪ O_m`, so `W = 1` by faithfulness. `W` is a finite intersection
of finite-index subgroups of `Z`, so `[Z : W] < infinity`. Hence `Z` is finite.

## Corollaries

1. Take `Z = Z(E)`, whose centralizer is `E`.
2. If `g` has finitely many conjugates, then `C_E(g)` has finite index, so `<g>`
   is finite by the theorem.
3. Condition 4 of type (A) is the two-element-subset hypothesis, and a type (A)
   action is faithful.
4. `Z(Gamma~)` contains `ker p = Z`, which is infinite, so `Gamma~` has no type
   (A) action. If `Gamma~ <= E` with `E` a type (A) actor and `c` generates
   `ker p`, then `C_E(<c>)` has infinite index in `E` by the theorem, so `c` has
   infinitely many `E`-conjugates.
