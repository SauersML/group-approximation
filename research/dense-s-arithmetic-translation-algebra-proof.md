---
rg: 2
id: dense-s-arithmetic-translation-algebra-proof
kind: route
title: A right coset of the maximal compact subgroup is a complete section on which only the integral subgroup acts
target: dense-s-arithmetic-translation-algebra-is-amplified-profinite
requires: []
---

Left translation by the discrete group `A` on `(L, Haar)` is free and
measure preserving, and it is ergodic because `A` is dense in `L`
(an `A`-invariant function is invariant under the closure, hence under all
of `L`).  Haar measure is infinite, so `L^infinity(L) rtimes A = L(R_A)` is a
II_infinity factor by Feldman--Moore.

Let `Kg` be a right coset of the compact open subgroup `K` (Haar measure
`Haar(K) in (0, infinity)`).  If `x` and `ax` both lie in `Kg` for some
`a in A`, then `a = (ax) x^-1 in K g g^-1 K = K`, so `a in A cap K = C`.
Conversely `C` preserves `Kg`.  Hence `R_A|_(Kg)` is the orbit relation of
`C` acting by left translation on `Kg`, and the map `kg |-> k` identifies
`(Kg, R_A|_(Kg))` with `(K, R_C)`, `C`-equivariantly.  Since `A` is dense,
every `A`-orbit meets the open set `K`, so `K` is a complete section of
positive finite measure, and

```text
L(R_A) = L(R_A|_K) (x) B(l^2) = L(R_C) (x) B(l^2) = (L^infinity(K) rtimes C) (x) B(l^2),
```

using that the translation action of `C` on `K` is free.  `N = L^infinity(K) rtimes C`
is the increasing union over the principal congruence subgroups `K_m` of
`l^infinity(K/K_m) rtimes C = M_([K:K_m]) (x) L(C cap K_m)`, each Connes
embeddable because `C cap K_m` is residually finite; so `N` is a
Connes-embeddable II_1 factor (ergodic free action).  This is `(DT1)`.

For `(DT2)`: the left `A`-action and the right `Lambda'`-action on `L`
commute, so `L^infinity(L) rtimes (A x Lambda') = (L^infinity(L) rtimes A) rtimes Lambda'`.
Since `Lambda'` acts freely and properly on `L` with a compact fundamental
domain `D` (`D -> L/Lambda'` a measure isomorphism), `L^infinity(L) rtimes Lambda'
= L^infinity(D) (x) B(l^2 Lambda')`, and the commuting `A`-action becomes the
action on `L^infinity(L/Lambda')` tensored with the inner cocycle action on
`B(l^2 Lambda')` coming from the `Lambda'`-valued return cocycle of `D`;
absorbing the cocycle into the group unitaries gives
`(L^infinity(L) rtimes Lambda') rtimes A = (L^infinity(L/Lambda') rtimes A) (x) B(l^2 Lambda')`.
Equivalently, both sides are corners of the II_infinity factor of the orbit
relation of `A x Lambda'` on `L` (essentially free by the centralizer
argument of `homogeneous-quotient-commutant-obstruction-proof`, Step 2),
compressed to the complete sections `D` and `K` respectively.  The
description of the corner over `K` in the statement is the restriction of
that relation to `K`: `x, a x l^-1 in K` for `(a, l) in A x Lambda'`.
