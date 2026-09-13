---
rg: 2
id: zaremsky-2-05-dehn-functions-of-thompson-t-and-v
kind: claim
title: "Zaremsky Problem 2.5 resolved: do T and V have quadratic Dehn function, and what are the higher-rank Dehn functions of F, T and V?"
root: true
distinct_from:
  thompson-v-finitely-presented-infinite-simple: that records the classical facts that V is finitely presented, infinite and simple; this is the question of how much area relations in T and V need, and of the higher filling functions of F, T and V.
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 2, Problem 5, verbatim:
"Prove T and V have quadratic Dehn function. Compute the higher-rank Dehn
functions of F, T, and V (are they all euclidean?) [Update: Matteo Migliorini
has proved that T has quadratic Dehn function: https://arxiv.org/abs/2410.23088.]"

This claim is the question. It has three parts, and an answer route must
settle all three:

1. the Dehn function of T: answered, quadratic
   (`thompson-t-has-quadratic-dehn-function`);
2. the Dehn function of V: open, conjectured quadratic
   (`thompson-v-has-quadratic-dehn-function`);
3. the k-dimensional Dehn functions of F, T and V for every k ≥ 2: open,
   conjectured euclidean
   (`thompson-groups-f-t-v-have-euclidean-higher-dehn-functions`).

Admissible routes:

- **Euclidean answer**: `zaremsky-2-05-by-euclidean-fillings` requires the
  three claims above.
- **Any other answer**: a route requiring
  `thompson-t-has-quadratic-dehn-function`, an established claim computing the
  Dehn function of V, and established claims computing every higher Dehn
  function of F, T and V explicitly. Such a route is written once those claims
  exist.

Never write a `requires: []` route into this claim.

## Precise reading

- Dehn functions are compared up to the usual equivalence: `f ≼ g` iff
  `f(n) ≤ C g(Cn) + Cn` for some `C`, and `f ≃ g` iff both. The class does not
  depend on the finite presentation and is a quasi-isometry invariant.
  "Quadratic" means `≃ n^2`.
- Since V contains F, which contains `Z^2`, the group V is not hyperbolic, so
  `δ_V ≽ n^2` (a finitely presented group with subquadratic Dehn function is
  hyperbolic: Gromov; proofs by Olshanskii, Bowditch, Papasoglu). The V part is
  therefore the upper bound `δ_V ≼ n^2`. The same holds for T.
- F, T and V are of type `F_∞` (Brown–Geoghegan for F; Brown 1987 for T and V),
  so for every `k ≥ 1` the k-dimensional Dehn function `δ^(k)_G` is defined
  (fill k-spheres by (k+1)-balls in the universal cover of a `K(G,1)` with
  finite (k+1)-skeleton; Alonso–Wang–Pride, J. Group Theory 2 (1999) 81–112)
  and is a quasi-isometry invariant up to `≃`. "Euclidean" means
  `δ^(k) ≃ n^((k+1)/k)`, the filling function of `R^(k+1)`; `k = 1` is
  "quadratic". I read "higher-rank" as `k ≥ 2`, because `k = 1` is the first
  sentence of the problem.
- Homotopical and homological higher Dehn functions can differ
  (Abrams–Brady–Dani–Young, PNAS 2013), so an answer to part 3 should say which
  it computes; the default here is the homotopical one.

## Known results (verified from the sources on 2026-09-13)

- F: quadratic (Guba, Invent. Math. 163 (2006), Theorem 1),
  `thompson-f-has-quadratic-dehn-function`.
- T: quadratic (Migliorini, arXiv:2410.23088, Forum Math. Sigma 13 (2025) e109,
  Theorem A), after Guba's `n^7` bound (Guba 2000) and a quintic bound of
  K. Wang, Z. Zheng and J. Zhang (2015, as recorded in Lorrain's introduction).
- V: `n^11` (Guba 2000), improved to `n^6` by Lorrain (arXiv:2608.03813v2,
  5 Aug 2026, after the list's date), `thompson-v-dehn-function-is-at-most-sextic`.
  Quadratic is open.
- Higher-rank: no computation for F, T or V was found (bounded web and arXiv
  search on 2026-09-13).

## Attempts

- 2026-09-13 (lane z2-05-v-dehn): imported the answered T part and the F and V
  bounds. The open work is in the Attempts of
  `thompson-v-has-quadratic-dehn-function` and
  `thompson-groups-f-t-v-have-euclidean-higher-dehn-functions`.
