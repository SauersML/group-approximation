---
rg: 2
id: infinite-support-coordinate-permutations-nowhere-v-germs-proof
kind: route
title: A prefix replacement shifts coordinates by a constant, and a permutation of N that is eventually a shift is eventually the identity
target: infinite-support-coordinate-permutations-are-nowhere-v-germs
requires: []
---

Every element `v` of `V` is locally a prefix replacement: for every `x` in `C`
there are finite words `w`, `w'` with `x` in `wC` and `v(wy) = w'y` for all `y`
in `C`. This is the standard definition of `V` as the group of homeomorphisms
given by finitely many prefix exchanges on a finite clopen partition.

**Step 1: agreement forces an eventual shift.** Suppose `v` in `V` agrees with
`f_pi` on a neighbourhood of `x`. Take words `w`, `w'` as above and a cylinder
`uC` with `x` in `uC`, contained in that neighbourhood and in `wC`, with
`u = ws`. Put `c = |w| - |w'|`. For `y` in `C`,
`f_pi(wsy) = v(wsy) = w'sy`. For `j >= |w's|`, coordinate `j` of `w'sy` is
coordinate `j - |w's|` of `y`, which is coordinate `j + c` of `wsy`. So
`f_pi(z)_j = z_(j+c)` for all `z` in `uC` and all `j >= |w's|`.

**Step 2: the shift is the permutation.** Let `K = max(|w's|, |u| - c)`, and fix
`j >= K`, so `j + c >= |u|` and coordinate `j + c` is free on `uC`. By
definition `f_pi(z)_j = z_(pi^(-1)(j))`. If `pi^(-1)(j) != j + c`, choose `z` in
`uC` with `z_(j+c) != z_(pi^(-1)(j))`. This is possible: coordinate `j + c` is
free, and `pi^(-1)(j)` is either a coordinate fixed by `u` or a different free
coordinate. Then `f_pi(z)_j != z_(j+c)`, contradicting Step 1. So
`pi^(-1)(j) = j + c` for all `j >= K`.

**Step 3: an eventual shift of N is eventually the identity.** By Step 2,
`pi^(-1)` maps `[K, infinity)` bijectively onto `[K + c, infinity)`, where
`K + c >= |u| >= 0`. Being a bijection of `N`, it maps the complement
`{0, ..., K-1}` bijectively onto `{0, ..., K+c-1}`. So `K = K + c`, `c = 0`,
and `pi^(-1)(j) = j` for all `j >= K`. Thus `pi` has finite support.

**Conclusion.** If `pi` has infinite support, no `v` in `V` agrees with `f_pi`
near any point, so `sing(f_pi) = C`.

**Consequence.** For `g != 1`, left translation `lambda_g` on `Gamma` has no
fixed point, so when `Gamma` is infinite, `pi_g = nu o lambda_g o nu^(-1)` moves
every point of `N` and has infinite support. So `sing(beta_g) = C` is
uncountable, and `<V, beta(Gamma)>` fails condition (1) of a finite germ
extension of `V`: every element has finitely many singular points.
