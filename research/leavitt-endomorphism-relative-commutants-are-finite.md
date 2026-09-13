---
rg: 2
id: leavitt-endomorphism-relative-commutants-are-finite
kind: claim
title: Every unital endomorphism of the binary Leavitt algebra over F_2 has a finite-dimensional relative commutant
distinct_from:
  leavitt-unit-centralizers-have-finite-rank: that bounds the centralizer of one unit over its own Laurent ring; this bounds, over F_2, the commutant of a whole unital copy of the Leavitt algebra.
  leavitt-triangular-endomorphism-commutants-are-finite: that proves this for core and triangular units; this is the statement for every unit.
---

**OPEN.** Let `R = L_(F_2)(1,2)` and `phi(x) = s_0 x t_0 + s_1 x t_1`. For every unit `u` of `R`,

```text
C_u = C_R(rho_u(R)) = { z in R : z u s_0 = u s_0 z,  z u s_1 = u s_1 z } = { z : z = u phi(z) u^(-1) }
```

is finite-dimensional over `F_2`.

**Payoff.** This answers Ara--Cortiñas Question 5.7 negatively over `F_2`
(`tensor-square-nonembedding-from-finite-relative-commutants`). Every unital `f : L ⊗ L -> L` has
`f(- ⊗ 1) = rho_u` for some unit `u`, and `f(1 ⊗ -)` maps `L` into `C_u`. The C*-analogue is false, since
`O_2 ⊗ O_2 ≅ O_2`. So a proof must use finite depth.

## Attempts

**Core and triangular units (proved).** `leavitt-triangular-endomorphism-commutants-are-finite` proves the claim
when `u` lies in the core or in `H_<=` or `H_>=`, over any field. The degree bound is `|d| <= 2k - 2` for a core
unit of level `k`.
- *Where it dies.* For a unit with components of both signs, `u s_i` is not homogeneous, so `C_u` need not be
  graded.
- The terms of `u` move the tail of a sequence by different amounts, so the last-letter support argument has no
  untouched letter to read.
- Neither obstruction is overcome.

**Exact screens.** 843 random words and 32 random core units give `dim(C_u ∩ R_N) <= 2` for `N <= 3` or `4`,
with no growth in `N` (`research/artifacts/leavitt-relative-commutants-2026-09-13.md`, Section 4). Short words
are a weak test: a counterexample would have to be designed.

**Relation to centralizer rank.** The two premises decide Question 5.7 by different mechanisms, and neither
implies the other as far as is known.
- `leavitt-unit-centralizers-have-finite-rank` decides it through algebraic dependence. Suppose a unital copy
  `B` of `L` lies in `C_u`, and let `y` be the image of the north--south unit in `B`. Then `rho_u(R)` is a
  unital copy of `L` inside `C_R(y)`, and `L ⊗ F_2(y)` is simple and infinite-dimensional. It would map
  unitally into the finite-dimensional `F_2(y)`-algebra `F_2(y) ⊗ C_R(y)`, which is impossible.
- That argument does not make `C_u` finite-dimensional. This claim, conversely, says nothing about
  centralizers of single units.
