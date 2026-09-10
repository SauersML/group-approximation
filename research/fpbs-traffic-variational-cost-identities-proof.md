---
rg: 2
id: fpbs-traffic-variational-cost-identities-proof
kind: route
title: Truncate near-optimal graphings and lift target plans to get both identities
target: fpbs-traffic-variational-cost-identities
requires:
  - fpbs-finite-fiber-cost-bound
artifacts:
  - research/artifacts/fpbs/docs/fixed-price-conditional-traffic.md
---

Sections 5 and 9 of the artifact. For a general countable group with
finite-cost base, fix a finite-cost generating base graphing Lambda and
first choose a finite prefix with arbitrarily small remaining tail cost.
Split a near-optimal source graphing into group-labelled maps. Every one
of the finitely many prefix demands has a finite path almost surely on
its domain, so truncating the graphing and increasing a common length
bound makes the uncovered prefix measure arbitrarily small. Used edges
cost at most the chosen source graphing, and the full demand tail is
charged in B. Source generation after repair proves the opposite bound.

For the target identity, the constructive descent bound is one direction.
Conversely perform the same finite-prefix approximation in a near-optimal
base graphing, and lift that plan. Its traffic is a base-measurable
integer function, so its defect is exactly zero. The ordinary tail cost
is unchanged on lifting. Thus the infima are C(Y) and C(X), both finite.
The zero-gap criterion follows because B-C(Y) and J are nonnegative.
This extends the original finite-generator proof without taking an
unjustified limit of subgroup costs. It is a supplied deduction, not
external validation.

The required finite-fiber bound supplies C(X)<infinity when the
alternative hypothesis is a uniform finite-fiber factor with finite
source cost, or an ergodic base with conditional atoms and finite
source cost. It is used to enter the proved finite-tail setting,
not to assert that the two costs are equal.

Section 10 proves the increasing-factor statement. Choose one
source-near-optimal finite-prefix plan, then approximate its finitely
many used domains in the increasing factor sigma-algebras. For that
fixed plan, finite-word path validity and the finite-prefix failure
score change by at most a finite union bound on translated domain
errors. Repair those failures and append the fixed base tail.
This gives lim_r C(Z_r)<=C(Y)+2epsilon for every epsilon>0,
while lifting gives the reverse bound.
No uniform approximation over changing plans is assumed.
