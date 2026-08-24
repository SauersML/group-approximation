---
rg: 2
id: char-two-basis-swap-normal-generation-proof
kind: route
title: Extract every elementary root from one basis swap
target: char-two-basis-swap-normally-generates-elementary-group
requires: []
---

Fix distinct indices `1,2,3` and let `N` be the normal closure of the standard
basis swap `tau=tau_12` in `E_n(R)`.  In characteristic two,

```text
tau=e_12(1)e_21(1)e_12(1),                              (CTP1)
```

so `tau` lies in `E_n(R)`.

For arbitrary `r in R`, conjugation by `tau` exchanges the first two indices,
so

```text
tau e_13(r) tau^-1 = e_23(r).                           (CTP2)
```

Also `e_13(r)^-1=e_13(r)`.  Hence the commutator

```text
[e_13(r),tau]
 =e_13(r) tau e_13(r)^-1 tau^-1
 =e_13(r)e_23(r)                                        (CTP3)
```

belongs to `N`.

Now put `b=e_12(1)`.  The Steinberg relations give

```text
b e_13(r) b^-1 = e_13(r),
b e_23(r) b^-1 = e_13(r)e_23(r).                        (CTP4)
```

Since `N` is normal, conjugating `(CTP3)` by `b` stays in `N`; using that
`e_13(r)` and `e_23(r)` commute and `e_13(r)^2=1`,

```text
b(e_13(r)e_23(r))b^-1
 =e_13(r)e_13(r)e_23(r)
 =e_23(r).                                               (CTP5)
```

Thus `e_23(r) in N` for every `r in R`.  Every finite basis permutation is a
product of standard swaps, each standard swap has the elementary expression
`(CTP1)` after relabelling, and conjugation by those permutation matrices
moves `(2,3)` to any ordered pair `(i,j)`, `i!=j`.  Consequently

```text
e_ij(r) in N              for all i!=j and r in R.
```

These elementary roots generate `E_n(R)`, proving `N=E_n(R)`.
