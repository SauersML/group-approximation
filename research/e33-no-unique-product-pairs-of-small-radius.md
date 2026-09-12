---
rg: 2
id: e33-no-unique-product-pairs-of-small-radius
kind: claim
title: E_3(3) in SL_3(Z) has no small-radius pair without unique products, hence no zero divisors there over any field
distinct_from:
  e33-balls-have-no-small-zero-divisors: that is a zero-divisor census over F_2, F_3 and Q with supports inside fixed balls; this searches the field-independent obstruction, pairs without unique products normalized by translation, and excludes zero divisors of small radius over every field at once.
  zero-divisor-support-subgroup-host-constraints: that proves a zero-divisor host must lack unique products; this checks that property computationally on one admissible host at small radius.
artifacts:
  - experiments/zero-divisor-tf/up_sat.py
  - experiments/zero-divisor-tf/runs-up/e33-up-r11-control.json
  - experiments/zero-divisor-tf/runs-up/e33-up-r22.json
  - experiments/zero-divisor-tf/runs-up/e33-up-r23.json
---

**ESTABLISHED (exact computation).** Let `H = E_3(3) = <e_ij(3) : i != j>` in
`SL_3(Z)`. Write `|g|` for word length in the generators `e_ij(+-3)` and
`B(r) = {g : |g| <= r}`. For a finite nonempty set `A ⊆ H` put

```text
rad_L(A) = min_(a_0 in A) max_(a in A) |a_0^(-1) a|,
rad_R(A) = min_(a_0 in A) max_(a in A) |a a_0^(-1)|.
```

There is no pair of finite nonempty sets `A, B ⊆ H` without a uniquely
represented product (every `g in AB` has at least two expressions `g = ab`)
such that

1. `rad_L(A) <= 2` and `rad_R(B) <= 2`, or
2. `rad_L(A) <= 2` and `rad_R(B) <= 3`, or `rad_L(A) <= 3` and `rad_R(B) <= 2`.

**Consequence for zero divisors, over every field.** If `k` is any field and
`alpha, beta in k[H]` are nonzero with `alpha beta = 0`, then
`rad_L(supp alpha) + rad_R(supp beta) >= 6`, or one of the two radii is at
least 4.

**Relation to the ball census.** `e33-balls-have-no-small-zero-divisors`
excludes zero divisors over `F_2`, `F_3` and `Q` whose supports lie *inside*
`B(2)`, and over `F_2` inside `B(2) x B(3)`. This claim is independent of the
field, but covers supports of small radius around one of their own points.
- A subset of `B(2)` can have radius up to 4.
- A radius-2 support need not lie in `B(2)`.
So neither statement contains the other.

**Host status.** `H` is an admissible host for
`kaplansky-zero-divisor-conjecture` that avoids every proved class:
- torsion-free, since `H <= Gamma(3)` (Minkowski);
- property (T), so not elementary amenable, not locally indicable (finite
  abelianization), and not virtually compact special
  (`zero-divisor-host-is-not-virtually-compact-special`);
- not left-orderable (Witte, Proc. AMS 122 (1994));
- not a-T-menable. Linnell's class C, on which the Strong Atiyah conjecture
  and hence the characteristic-zero zero-divisor conjecture are known, consists
  of a-T-menable groups: free groups are a-T-menable, and a-T-menability passes
  to directed unions and to extensions with amenable quotient. So `H` is not in
  C.

Whether `H` has unique products is not recorded anywhere in this graph. This
census is the first bounded evidence either way. The known torsion-free groups
without unique products (Promislow's group, the Rips--Segev groups, Steenbock's
graphical small-cancellation groups) were not checked for embeddings into `H`.
An embedding would show that `H` lacks unique products, but would give no zero
divisor by itself.

**Runs** (CaDiCaL 1.5.3 through python-sat, MSI acn112, single thread):

| radii | ball sizes | pairs | cells | singleton cells | vars | clauses | seconds | result |
|---|---|---|---|---|---|---|---|---|
| control 1,1 (adjoined `t = diag(-1,-1,1)`) | 14, 14 | 196 | 134 | 84 | 168 | 615 | 0.0 | SAT, `A = B = {1, t}`, verified |
| 2, 2 | 121, 121 | 14641 | 8569 | 5268 | 13769 | 54861 | 0.25 | UNSAT |
| 2, 3 | 121, 1045 | 126445 | 68941 | 41772 | 127553 | 502401 | 12.56 | UNSAT |

## Pending runs

The instances at radii `(3,3)` and `(2,4)` were still running on MSI (acn112,
time limit 1500 s each) when this claim landed, so they are not part of it.
- Outputs: `/projects/standard/hsiehph/sauer354/zero-divisor-tf/runs-up/e33-up-r33.json`
  and `.../runs-up/e33-up-r24.json`.
- Logs: `.../runs-up/log-r33.txt` and `.../runs-up/log-r24.txt`.

UNSAT there would extend item 2. SAT with a verified pair would show that `H`
lacks unique products, which still gives no zero divisor.
