---
rg: 2
id: spherical-quadrature-tensors-through-clifford-folner-windows
kind: claim
title: Spherical quadratures tensor through every finite-depth Clifford Folner window
distinct_from:
  finite-spherical-moments-do-not-fold-regular-double: This claim keeps the spherical quadrature and adds every bounded-depth Clifford transition test.
  depth-two-clifford-types-form-a-finite-fiber-folner-graph: That claim proves amenability of the type graph; this claim couples its windows to the spherical nonfolding witness.
  finite-projective-sector-groupoids-have-conjugate-absorbers: That claim cancels a finite projective cocycle; this claim uses the cancellation inside a tensor escape.
---

# Spherical quadratures tensor through every finite-depth Clifford Folner window

Fix a finite collection of spherical Hecke moments in the arithmetic double.
Also fix a finite collection of bounded-range bisections of the depth-two
Clifford type groupoid, together with local relations which are identities in
that groupoid.  Suppose the two collections are coupled only by requiring
their matrix models to commute.  Then these tests do not force the two
vertices of the double to fold.

More precisely, there is a sequence of finite-dimensional models in which:

1. every prescribed spherical moment converges to its regular value;
2. every prescribed Clifford transition and local cycle has normalized
   Hilbert--Schmidt defect tending to zero;
3. every prescribed cross-commutator is exact; and
4. the lazy block-swap average converges to the nonfolded value `43/168`.

The assertion concerns the separated finite test system just described.  It
does **not** assert that these models extend to microstates of the full
arithmetic double.

## Construction

By `finite-spherical-moments-do-not-fold-regular-double`, the chosen finite
Hecke moment list has finite atomic diagonal quadratures approximating all of
its values arbitrarily well, including the lazy-average value `43/168`.
Choose their error to tend to zero with `R`, and call the corresponding
carrier `H_sph(R)`.

The bounded-depth Clifford type graph is a fixed finite fiber over the
coweight lattice `Z^2`.  Restrict it to a full fiber over a box `B_R`.  Each
prescribed groupoid bisection has bounded range.  On the interior it is the
native permutation; complete it arbitrarily to a permutation on the boundary.
If `r` is one of the selected local relations, its word permutation is the
identity except within a bounded enlargement of that boundary, and hence

```text
||r-1||_2 <= 2 sqrt(O(|partial B_R|)/|B_R|) = O(R^(-1/2)).
```

The finite stabilizer cocycles do not obstruct this completion.  By
`finite-projective-sector-groupoids-have-conjugate-absorbers`, conjugate
doubling gives an honest finite-dimensional realization of every fixed
projective sector.  Thus all fixed local inverse, Weyl, triangle, and
parahoric cycles are exact off the same boundary layer.  Call this carrier
`H_Cl(R)`.

On `H_sph(R) tensor H_Cl(R)`, let the spherical observables act on the first
factor and the Clifford observables on the second.  Their mixed commutators
vanish exactly.  Normalized traces and normalized Hilbert--Schmidt defects
factor, so the spherical moments converge to their regular values, the
lazy-average value converges to `43/168`, and all Clifford defects tend to
zero.

## Consequence

No argument using only finitely many spherical moments, finitely many
bounded-depth Clifford cycles, and commutation between those two families can
prove regular-double folding.  A surviving presentation-level proof must add
a genuinely non-tensorial incidence: one group word must identify a spherical
atom with a Clifford path on the same carrier, or an additive multi-path
relation must make different Clifford histories interfere.  Merely placing
both finite test families in the same matrix algebra leaves the tensor escape.
