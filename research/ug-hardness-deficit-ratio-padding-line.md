---
rg: 2
id: ug-hardness-deficit-ratio-padding-line
kind: claim
title: The deficit ratio R = (1-s)/(1-c) of a unique-games hardness point is invariant under satisfiable padding, exceeds 2 exactly below the padding line s = 2c-1, is forced above 2 by UGC, and stays at most 2 for every padded proper-split pipeline
distinct_from:
  unique-games-hard-at-completeness-one-half: that is the proved hardness point ((1-eps)/2, eps); this is the invariant under which that point and all its paddings sit strictly above the padding line, and the cap that its split pipeline cannot cross.
  unique-constraints-orient-at-most-half-of-a-fiber: that says no network of permutation constraints implements a 2-to-1 merge; this is a statement about achievable (completeness, soundness) pairs, measured by a padding-invariant ratio, and caps proper-split outputs at ratio 2 whatever the source game.
  unique-games-np-hard-below-the-padding-line: that is the open milestone s < 2c-1; this proves it is necessary for UGC and kills one pipeline class for it.
  unique-games-conjecture: that is the open hardness statement at (1-eps, eps); this names a padding-invariant necessary consequence.
artifacts:
  - experiments/ugc-deficit-ratio-2026-09-17/check_deficit_ratio.py
---

**ESTABLISHED.** Elementary. Proof: `ug-hardness-deficit-ratio-padding-line-proof`.

*Setting.* A unique game `U` is a weighted two-prover one-round game with
positive integer edge weights whose constraints are permutations of `[K]`;
`val(U)` is the largest satisfied weight fraction. For rationals
`0 <= s < c < 1`, `Gap-UG_K[c, s]` is the promise problem with YES instances
`val >= c` and NO instances `val <= s`. Its **deficit ratio** is

```text
R(c, s) = (1 - s) / (1 - c).
```

A d-to-d constraint on `(x_i, x_j)` is **proper** if it is the union of `d`
permutation branches `pi_1, ..., pi_d` that are pointwise distinct:
`pi_a(x) != pi_b(x)` for all `x` and `a != b`. The **proper split** of a game
`G` whose constraints are proper of arities `d_e >= 2` replaces each constraint
`e` of weight `w_e` by its `d_e` branches, each of weight `w_e L / d_e`, where
`L = lcm(d_e)`. The linear 2-to-2 constraints `T x_i + T' x_j in {b, b'}` with
`b != b'` are proper of arity 2. The **padding** `P_lambda(U)`, for rational
`lambda = p/q in [0, 1)`, scales every weight of `U` by `q - p` and adds a new
left vertex, a new right vertex and one identity edge of weight `pW`, where `W`
is the total weight of `U`.

**Theorem.**

1. *(Padding.)* `val(P_lambda(U)) = lambda + (1 - lambda) val(U)`. Hence `P_lambda`
   reduces `Gap-UG_K[c, s]` to `Gap-UG_K[lambda + (1-lambda)c, lambda + (1-lambda)s]`,
   and `R` is unchanged. The padding orbit of `(c, s)` is the segment from
   `(c, s)` to `(1, 1)`, on which `R` is constant.
2. *(Padding line.)* `R(c, s) > 2` iff `s < 2c - 1`. Since `s >= 0`, this forces
   `c > 1/2`. For every `c <= 1/2`, `R(c, s) <= 2`. The line `s = 2c - 1` is the
   padding orbit of the degenerate point `(1/2, 0)`.
3. *(Known point.)* The proved point `((1-eps)/2, eps)` of
   `unique-games-hard-at-completeness-one-half` has
   `R = 2(1-eps)/(1+eps) < 2`. So it and every padding of it lie strictly above
   the padding line, and `R -> 2` only as `eps -> 0`.
4. *(UGC forces the crossing.)* If `unique-games-conjecture` holds, then for
   every `eps < 1/3` some `Gap-UG_K[1-eps, eps]` is NP-hard, with
   `R = (1-eps)/eps > 2`, and `R` is unbounded as `eps -> 0`. So UGC implies
   `unique-games-np-hard-below-the-padding-line`.
5. *(Class kill: padded proper splits.)* Let `L` be a language with a YES
   input and a NO input of a common length `n`. Let `Red` be any map, of any
   complexity, sending inputs `x` of length `n` to `P_lambda(n)(Split(G_x))`,
   where `G_x` is any game with proper constraints of arities `>= 2` and
   `lambda(n)` depends only on `n`. If `Red` sends YES inputs of length `n` to
   games of value `>= c` and NO inputs of length `n` to games of value `<= s`,
   then `s >= 2c - 1`, that is `R(c, s) <= 2`. If every arity is `d`, the
   bound is `R <= d/(d-1)`.

**What dies, and where.** A proof of `unique-games-np-hard-below-the-padding-line`
(and so of `unique-games-conjecture`) cannot output padded proper splits of
any d-to-d games, however hard the source and however clever the soundness
analysis. It dies at the **completeness case**. *Invariant:* every satisfied
constraint of a proper game makes exactly one branch hold, so
`val(Split(G)) = E_e [1(e satisfied)/d_e] <= 1/2`. After padding, a YES
output has value at most `(1 + lambda)/2`, while a NO output has value at
least `lambda`. This is the `1/2` wall of the 2-to-2 route, read as a
padding-invariant ratio. It says nothing about splits of improper constraints,
about outputs that are not splits, or about compositions that re-encode labels.
