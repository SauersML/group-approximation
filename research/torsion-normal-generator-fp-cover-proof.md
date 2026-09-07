---
rg: 2
id: torsion-normal-generator-fp-cover-proof
kind: route
title: Invert the geometric factor of A^m minus one near the identity
target: torsion-normal-generator-fp-cover-linear-gap
requires:
  - full-mf-radical-linear-relator-inequality
artifacts:
  - research/artifacts/universal-seed-review-2026-09-07.md
---

## Proof

Choose a finite generating set with `x_1 = a`, and fix words expressing each
generator as a product of conjugates of `a^(+-1)`, with `L` the total number
of conjugate occurrences in the largest of them.  Let `R_0` consist of
`x_1^m` and the finitely many relations equating each generator with its
normal-generation word.

**Threshold.**  There are a finite set `R` of relations of `G` containing
`R_0` and `delta_0 > 0` such that `Def_R(U) < delta_0` forces
`||U_1 - I|| < 1/2`.  Otherwise exhaust the relations of `G` by finite sets
and choose tuples with vanishing defects and `||U_1 - I|| >= 1/2`; their
classes give a corona homomorphism from `G` that is nontrivial on `a`,
against `Res_MF(G) = G`.

**The linear step.**  Put `A = U_1` and `delta = Def_R(U)`, and suppose
`delta < delta_0`.  From

```text
A^m - I = (A - I)(I + A + ... + A^(m-1))
```

and `||A^j - I|| <= j||A - I||`,

```text
||I + A + ... + A^(m-1) - mI|| <= (m(m-1)/2) ||A - I||.
```

For `m = 4` and `||A - I|| < 1/2` this is at most `6||A-I|| < 3 < 4`, so the
second factor is invertible with inverse of norm at most `1`, and
`||A - I|| <= ||A^m - I|| <= delta` because `x_1^m in R`.  The same holds for
any `m` once the threshold is taken small enough that
`(m(m-1)/2)||A-I|| < m`, which is what `delta_0` is chosen to give.

**Propagation.**  For each generator, its normal-generation relation lies in
`R`, and conjugation is isometric, so

```text
||U_i - I|| <= ||r_i(U) - I|| + L||A - I|| <= (L+1) delta.
```

For `delta >= delta_0` use `||U_i - I|| <= 2 <= (2/delta_0) delta`.  So the
inequality holds with `C_0 = max(L+1, 2/delta_0)`.

**The cover.**  Put `P = <x_1,...,x_k | R>`.  Every `r in R` is a relation of
`G`, so `P` surjects onto `G`; the members of `R_0` give `alpha^m = 1` and
normal generation by `alpha`.  The displayed inequality mentions `P` only
through the words `R`, which are its defining relators, so it holds for `P`,
and the converse half of `full-mf-radical-linear-relator-inequality` gives
`Res_MF(P) = P`.
