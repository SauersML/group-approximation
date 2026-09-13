---
rg: 2
id: sp4-finite-index-fd-projective-multiplier-is-finite
kind: claim
title: Every finite-index subgroup of Sp4(Z) has only finitely many finite-dimensionally realizable scalar classes
distinct_from:
  sp4-fd-projective-multiplier-is-finite: that is the level-one lattice, with the explicit bounds (FM1) and the Deligne-circle picture; this is every finite-index subgroup, proved profinitely (congruence subgroup property, then H^2(sp_4) = 0 through Lazard at the primes dividing the level), and it imports that node only for the factor at the remaining primes.
artifacts:
  - research/artifacts/sp4-chevalley-eilenberg-betti-2026-09-12.py
---

Let `Gamma'` be a finite-index subgroup of `Gamma = Sp_4(Z)` and

```text
R(Gamma') := { [c] in H^2(Gamma',T) : c is the exact 2-cocycle of some
               projective unitary representation Gamma' -> U(d), d < infinity }.
```

**THEOREM.**  `R(Gamma')` is finite.  More precisely, the natural map
from the profinite completion

```text
H^2_cts(Gamma'^, Q/Z) --> H^2(Gamma',T)                        (FI1)
```

is injective with image exactly `R(Gamma')`, and its source is finite.

**The picture.**  `H^2(Gamma',T)` itself is infinite.
- `H_2(Sp_4(Z),Z)` has rank one (`sp4-fd-projective-multiplier-is-finite`).
- Corestriction after restriction is multiplication by the index, so
  `H^2(Sp_4(Z),R) -> H^2(Gamma',R)` is injective.
- So `H^2(Gamma',T) = Hom(H_2(Gamma'),T)` contains a circle.

That circle is archimedean, and finite-dimensional unitary
representations cannot see it.
- They see only finite quotients (Malcev), hence only the profinite
  completion.
- By the congruence subgroup property, that completion is an open
  subgroup of `prod_p Sp_4(Z_p)`.
- At a prime dividing the level, infinitely many classes could only come
  from second Lie algebra cohomology.  But `H^2(sp_4,Q_p) = 0`
  (Whitehead), and Lazard's comparison theorem turns this vanishing into
  finiteness.
- The level-one theorem handles all the remaining primes at once, because
  their product is a direct factor of `Sp_4(Z^)`.

**Calibration: where the hypothesis bites.**  The load-bearing input is
`H^2(g,Q_p) = 0` for the Lie algebra.  The artifact computes exact
Chevalley--Eilenberg Betti numbers `(b_1,b_2,b_3)` over `Q`:

```text
sp_4 (0,0,1)    sl_2 (0,0,1)    abelian Q^2 (2,1,0)    heis_3 (2,2,1)
```

The semisimple algebras have `b_2 = 0`; the two non-semisimple controls
do not.

For the abelian control the conclusion visibly fails: `R(Z^2) = Q/Z` is
infinite.
- If the rotation class `theta` is realized in dimension `d`, the
  determinant of `UV = e(theta) VU` gives `d theta in Z`.
- Conversely, clock-and-shift matrices realize `theta = a/k` in
  dimension `k`.

This is the kind of supply that ISW Corollary B draws on
`Z^2 x| SL_2(Z)`.  At finite index in `Sp_4(Z)` it is gone.  The affine
shape could only reappear at infinite index, and
`sp4-contains-no-isw-affine-subgroup` excludes it there.

**Consequence.**
`isw-theorem-a-has-no-data-on-sp4-finite-index-subgroups`: Theorem A has
no input data on any finite-index subgroup, relative to any subgroup.

**Not claimed.**  No bound on `|R(Gamma')|` in terms of the index.  The
level-one bound `(FM1)` (`2t . R = 0`, `|R| <= 2t^2`) is not asserted to
transfer.
