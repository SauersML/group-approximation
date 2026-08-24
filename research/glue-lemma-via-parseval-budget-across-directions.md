---
rg: 2
id: glue-lemma-via-parseval-budget-across-directions
kind: route
title: Dead -- bound the number of heavy directions by an L^2 budget
target: affine-orientation-glue-lemma
requires: []
---

**Dead.**  The repair one reaches for after
`glue-lemma-via-ambient-influence-transfer` fails.

The attack: give up on locating ambient influential coordinates and instead
count.  Each heavy direction `b` costs at least `delta^2` of Fourier mass
somewhere, and `||g||_2 <= 1`, so summing over `b in B` should bound `|B|`,
or at least force the heavy cosets to overlap enough that a bounded `Q`
hits a constant fraction of them.

It is killed by `affine-memorizers-are-cross-direction-orthogonal`.  For odd
`r` the memorizers in distinct directions have **disjoint** Fourier
support -- a shared support set would be a `2r`-element set invariant under
two independent `F_2` translations, hence a union of four-element orbits,
against `2r = 2 mod 4`.  Consequently

```text
P_s = sum_{b != 0} s_b B_{b,r}
```

has `||P_s||_2^2 = (N-1)/M = Theta_r(N^(1-r))`, which tends to zero for
`r >= 3`, while the singleton quotient coefficient at `C_b` is exactly
`s_b` for every one of the `N-1` directions.  The budget the attack wanted
to spend is not merely tight -- it is vanishing while the heaviness is
maximal.

The kill is to the counting argument only.  `P_s` is unbounded, so it is no
counterexample to the target, and by
`memorizer-superposition-has-large-sup-norm` no renormalization of it ever
will be.
