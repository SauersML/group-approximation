---
rg: 2
id: torus-knot-group-k34-is-not-matricially-stable
kind: claim
title: "The (3,4) torus knot group is not matricially stable, although H^2(K; Z) = 0: an expander obstruction that is not cohomological"
distinct_from:
  torus-knot-group-k34-is-matricially-stable: that claim is the negation of this one; this one refutes it.
  torus-knot-groups-are-rq-stable: that is Willett's padded R_q-stability, which lets an uncontrolled finite-quotient representation be added; this says the unpadded lifting fails.
  dadarlat-matricial-stability-obstruction: that obstruction needs nonvanishing even rational cohomology; here H^2(K; Q) = 0, and the obstruction is a spectral gap of the central quotient.
  torus-knot-k34-expander-pair-has-no-eigencorner: that is the corona pair with no eigencorner; this is the stability consequence obtained from it through matricially-stable-groups-have-central-eigencorners.
---

**ESTABLISHED (written proof; not Lean-verified).**  Proof route:
`torus-knot-group-k34-not-matricially-stable-via-expander-pair`.

`K(3,4) = <x, y | x^4 = y^3>` is not matricially stable in Dadarlat's
point-norm sense.  Concretely, there are unitaries `X_p, Y_p in U(k_p)` with
`||X_p^4 - Y_p^3|| -> 0` that are not asymptotic, pointwise in operator
norm, to any sequence of pairs `(X'_p, Y'_p)` with `X'_p^4 = Y'_p^3`.  The
pairs are those of `torus-knot-k34-expander-pair-has-no-eigencorner`.

## Why it matters

- `K(3,4)` is torsion-free, one-relator, residually finite and
  free-by-cyclic (`F_6 ⋊ Z`).  It has `H_2(K; Z) = 0` and
  `H^2(K; Q) = 0`.  So Dadarlat's rational obstruction vanishes.  Willett's
  winding-number conditions are also vacuous, which is why the group is
  unconditionally `R_q`-stable (`torus-knot-groups-are-rq-stable`).  The
  obstruction here is different.  It is a uniform spectral gap
  (Selberg) for finite quotients of `K / Z(K) = Z/4 * Z/3`, together with a
  central phase that is Lipschitz for the word metric.
- Padding cannot be removed.  `R_q`-stability with an uncontrolled summand
  holds, but plain matricial stability fails.  The added finite-quotient
  representation is exactly what can supply the missing eigencorners.
- The same proof applies to the trefoil group `K(2,3) = B_3`.  See the Scope
  section of `torus-knot-k34-expander-pair-has-no-eigencorner`.
- It is consistent with Hadwin--Shulman.  Their theorem gives tracial
  (Hilbert--Schmidt) stability for these groups, and the pair here is
  Hilbert--Schmidt close to an exact pair.  Their abstract says, verbatim:
  "Our main result is that all 1-relator groups with non-trivial center are
  II₁-factor stable."  (arXiv:1706.08405; their word "matricially stable"
  means stability in the normalized Hilbert--Schmidt norm.)
- For the Leavitt and Thompson goal, the route
  `torus-knot-group-k34-central-eigencorners-via-stability` can never
  fire, because its leaf is false.
