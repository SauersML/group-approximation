---
rg: 2
id: exhaustive-marked-type-energy-summation
kind: claim
title: Typewise predicate-energy coverage sums over the entire marked packet without alignment loss
distinct_from:
  shared-multiplicity-commutator-builds-selected-hybrid-row: that supplies a predicate row on one selected marked type; this proves that rows covering all marked types would eliminate the selected-carrier alignment problem analytically.
  single-finite-type-promotion-forces-a-finite-perfect-strategy: that rigidly transports one finite type in an exact model; this only sums orthogonal isotypic energies in finite matrix models and imposes no identification between different context decompositions.
  finite-role-packet-cannot-supply-hybrid-predicate-row: that obstructs one universal scalar row; this permits a finite menu of type-dependent rows and proves the resulting finite-dimensional estimate.
---

Let `H` be a fixed finite group with a central involution `y`.  In an exact
finite-dimensional representation put

```text
Q=(1-y)/2=sum_(lambda in Irr_-(H)) Q_lambda,           (EMT1)
```

where `Irr_-(H)` is the finite set of irreducibles on which `y=-1` and the
`Q_lambda` are the mutually orthogonal central isotypic projections.

Suppose a fixed context predicate has forbidden projection `F`, commuting
with the `H`-type decomposition.  For every marked type `lambda`, suppose a
finite menu `T_lambda` of ordinary relator words has the typewise estimate

```text
sum_(r in T_lambda) ||(r(U)-1)Q_lambda||_2^2
 >= kappa_lambda tr(F Q_lambda)-omega_lambda(delta),  (EMT2)
```

after exactification of the fixed `H` table.  Here every
`kappa_lambda>0`, `delta` is the original presentation defect, and every
`omega_lambda(delta)` tends to zero independently of matrix dimension.
The words need not preserve individual types and the menus may overlap.

Then, with

```text
kappa=min_lambda kappa_lambda>0,
omega=sum_lambda omega_lambda,
T=union_lambda T_lambda,
```

one has the whole-marked-sector estimate

```text
sum_(r in T) ||r(U)-1||_2^2
 >= kappa tr(FQ)-omega(delta).                         (EMT3)
```

Thus exhaustive finite-type coverage has no carrier-alignment loss.  The
number and dimensions of the irreducible types enter only through one fixed
positive constant and one fixed modulus.

## Proof

For any matrix `X` and any subfamily of the mutually orthogonal domain
projections in `(EMT1)`,

```text
sum_lambda ||X Q_lambda||_2^2
 =||XQ||_2^2<=||X||_2^2.                              (EMT4)
```

This identity does not require the ranges `XQ_lambda H` to be orthogonal.
Therefore

```text
sum_(r in T) ||r(U)-1||_2^2
 >=sum_lambda sum_(r in T_lambda)
                  ||(r(U)-1)Q_lambda||_2^2.           (EMT5)
```

Indeed, for each fixed `r`, the types for which `r in T_lambda` form only
a subfamily in `(EMT4)`.  Apply `(EMT2)`, take the minimum `kappa`, and use

```text
sum_lambda tr(FQ_lambda)=tr(FQ).                       (EMT6)
```

This proves `(EMT3)`.

The same proof applies simultaneously to the finitely many contexts of a
fixed BCS game.  Literal consistency-row commutators may be added to the
left-hand side separately.  If the common D8 packet supplies one marked
partial-isometry source and the finite game gap gives

```text
E_predicate(Q)+E_consistency(Q)>=gamma tr(Q)           (EMT7)
```

in the unnormalized common-source convention, then `(EMT3)` and the
already-wordized consistency rows give

```text
E_group(U)+omega(delta)>=kappa_0 gamma tr(Q)           (EMT8)
```

for a fixed `kappa_0>0`.  Hence vanishing presentation defect forces
`tr(Q)->0`.  Canonical microstates of a nontrivial central involution instead
have `tr(Q)->1/2`, so exact completeness with `y!=1` would prove
non-hyperlinearity.

## Robust exactification audit

Only a fixed finite group and finitely many fixed words occur.  Flexible
Hilbert--Schmidt exactification of the complete `H` multiplication table,
spectral rounding of `y`, and telescoping of the fixed words alter `(EMT2)`
by a computable dimension-independent modulus.  Since `Irr_-(H)` is finite,
taking its minimum and summing its moduli preserves dimension independence.

This closes the analytic question posed by exhaustive coverage.  It does
**not** construct the per-type menus `(EMT2)`.  The induction firewall in
`algebraic-exhaustive-marked-type-detectors-violate-induction` shows that a
menu whose typewise estimate is an exact multiplicity-insensitive operator
identity cannot provide them while preserving the finite packet.  A viable
menu must use a genuinely finite-matrix-only actuator.
