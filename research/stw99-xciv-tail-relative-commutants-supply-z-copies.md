---
rg: 2
id: stw99-xciv-tail-relative-commutants-supply-z-copies
kind: route
title: Average onto matrix-stage commutants and use the UHF tails
target: stw99-xciv-norm-matrix-tower-has-zstable-hull
requires: []
---

Put `A=closure(union_n A_n)`.  The divisibility
`r_n | r_(n+1)` follows from the unital inclusion of full matrix algebras.
Therefore `A` is a unital UHF algebra.  It is infinite-dimensional because
the `r_n` are unbounded, and every `x in S` belongs to `A` by the assumed
operator-norm approximation.  Every infinite-dimensional UHF algebra absorbs
the Jiang--Su algebra, so `A ~= A tensor Z`.  This already proves the hull
assertion.

We record the promised relative-commutant construction.  Fix `n`.  For
`m>=n`, uniqueness of unital representations of `M_(r_n)` on
`C^(r_m)` gives

```text
A_n' intersect A_m ~= M_(r_m/r_n).
```

Moreover,

```text
A_n' intersect A
  = closure(union_(m>=n) (A_n' intersect A_m)).
```

Indeed, averaging over the compact unitary group of `A_n` defines a
contractive conditional expectation `E_n:A->A_n' intersect A`.  If
`y in A_n' intersect A` is approximated by `b in A_m`, then `E_n(b)` belongs
to `A_n' intersect A_m` and approximates `y` at least as well.  Since
`r_m/r_n -> infinity`, this relative commutant is itself an
infinite-dimensional UHF algebra.  It is therefore `Z`-stable and contains a
unital copy of `Z`: compose `z |-> 1 tensor z` with an isomorphism from its
tensor product with `Z` back onto itself.

Now let finite `F subset S`, finite `G subset Z`, and `epsilon>0` be given.
Set `M=max(1,max_(z in G)||z||)`.  Choose `n` so that every `x in F` has
some `b_x in A_n` with

```text
||x-b_x|| < epsilon/(2M).
```

Choose a unital `phi:Z->A_n' intersect A`.  Since `phi` is isometric and
commutes with `b_x`,

```text
||[x,phi(z)]||
 <= 2 ||x-b_x|| ||phi(z)||
 < epsilon
```

for `x in F` and `z in G`.  All estimates are in operator norm.  Hyperfinite
`2`-norm approximation of arbitrary elements of `R` supplies none of the
displayed distance hypothesis, so the argument does not extend to all of
`R` and does not resolve the XCIV root.
