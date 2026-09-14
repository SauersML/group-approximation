---
rg: 2
id: cantor-homeomorphisms-miss-a-unimodular-root
kind: claim
title: Homeo of the Cantor set does not solve exponent-sum-one equations internally
invalidates: [kl-via-internal-closure-of-a-universal-group]
distinct_from:
  kervaire-laudenbach-nonsingular-conjecture: that asks for roots in overgroups; this exhibits an exponent-sum-one equation over Homeo of the Cantor set with no root inside Homeo of the Cantor set, while its coefficient group S_3 has roots in overgroups.
  cantor-odometer-has-no-homeomorphism-square-root: that is internal failure of Homeo of the Cantor set at degree two; this is internal failure at the unimodular degree itself.
  infinite-symmetric-groups-miss-a-unimodular-root: that proves the degree-one failure for Sym(Omega) by a transposition count; this is the same equation for any action of S_3 whose orbits have size one or three, which covers Homeo of the Cantor set, where supports are not finite.
---

Let `D` be a Cantor set and `C = (D x {0, 1, 2}) ⊔ R`, where `R` is clopen
(possibly empty). Let `a` swap the labels `0` and `1` and `b` swap `0` and `2`,
fixing `R` pointwise. Then `a, b in Homeo(C)` generate `S_3`.

1. **No internal root.** The equation `x a x a x^(-1) b = 1`, of exponent sum
   `1`, has no solution `x in Homeo(C)`.
2. **The general form.** For any set `Omega` with an action of `S_3 = <a, b>`
   whose orbits all have size `1` or `3`, with at least one of size `3`, there
   is no `x in Sym(Omega)` with `x a x a x^(-1) b = 1`.

Item 1 is item 2 with `Omega = C`, since every `S_3`-orbit on `C` has size `3`
(on `D x {0,1,2}`) or `1` (on `R`).

The coefficient group `S_3` is finite, so the equation has roots in overgroups
(`kervaire-laudenbach-holds-for-hyperlinear`). What fails is the coefficient
embedding: every root must live in an action with an `S_3`-orbit of size `2`
or `6`.

## What it kills

Together with `cantor-odometer-has-no-homeomorphism-square-root` and
`infinite-symmetric-groups-miss-a-unimodular-root`, internal closure of
`Homeo(C)` fails at degrees `1` and `2`, and that of `Sym(Omega)` at `1` and
`2`. So `kl-via-internal-closure-of-a-universal-group` is dead for both
ambients at every degree that matters, including the unimodular one.

**The mechanism.** Internal solvability in a universal group is sensitive to
the orbit type of the coefficient embedding, and universal groups contain
every orbit type. So one bad embedding of one finite coefficient group is
enough to kill internal closure. Any universal-ambient proof of
Kervaire--Laudenbach must first move the coefficients to a better embedding,
and choosing that embedding is exactly the overgroup step that
`overgroup-room-does-not-supply-a-root` shows cannot be free.
