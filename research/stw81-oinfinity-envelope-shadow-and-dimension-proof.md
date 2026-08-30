---
rg: 2
id: stw81-oinfinity-envelope-shadow-and-dimension-proof
kind: route
title: Pass O-infinity absorption through every shadow and reflect nuclearity by a slice map
target: stw81-oinfinity-envelopes-have-dimension-one-or-infinity
requires: []
artifacts:
  - research/artifacts/stw81-oinfinity-envelope-audit-2026-08-30.md
---

Put `E=A tensor O_infinity`.  Strong self-absorption gives

```text
E tensor O_infinity ~= E.                                      (1)
```

## Every commutative hereditary shadow vanishes

Let `Q` be a quotient of `E`.  Tensorial absorption by a strongly
self-absorbing algebra passes to quotients of separable C-star algebras, so
`Q` is O-infinity-stable.  It also passes to hereditary subalgebras.  Hence,
if `C subset Q` were a nonzero commutative hereditary subalgebra, then

```text
C tensor O_infinity ~= C.                                      (2)
```

This is impossible.  A nonzero commutative C-star algebra has a character.
On the other hand, an O-infinity-stable algebra is strongly purely infinite
and therefore has no characters.  Equivalently, a character on the left
side of `(2)` would extend nondegenerately to the multiplier algebra and
restrict along `1 tensor O_infinity` to a character of `O_infinity`, whereas
`O_infinity` is simple and noncommutative.

Thus every commutative hereditary subalgebra in every quotient of `E` is
zero.  This argument uses neither nuclearity of `A` nor information about
its ideals.

## Nuclearity is reflected by the envelope

If `A` is nuclear, then `E` is nuclear.  Conversely, fix a state `omega` on
`O_infinity`.  There are completely positive contractions

```text
i:A -> E,             i(a)=a tensor 1,
r:E -> A,             r=id_A tensor omega,
```

with `r composed i=id_A`.  If `E` were nuclear, composing finite-dimensional
completely positive approximations of `id_E` with `i` and `r` would give
such approximations of `id_A`.  Therefore

```text
E is nuclear if and only if A is nuclear.                       (3)
```

When `A` is not nuclear, `(3)` and the fact that finite nuclear dimension
implies nuclearity give `dim_nuc(E)=infinity`.

Suppose now that `A` is nuclear.  Then `E` is nonzero, separable, nuclear,
and O-infinity-stable.  The Bosa--Gabe--Sims--White theorem gives

```text
dim_nuc(E)<=1.                                                   (4)
```

The value cannot be zero.  A separable C-star algebra of nuclear dimension
zero is AF.  But a nonzero O-infinity-stable algebra is strongly purely
infinite; in particular every nonzero projection in it is properly infinite.
A nonzero AF algebra contains a nonzero projection and all of its projections
are finite.  Thus `E` is not AF, and `(4)` is the exact equality
`dim_nuc(E)=1`.

Together with the shadow calculation, this proves the claim.
