---
rg: 2
id: kt-q2-bass-serre-unique-trace-proof
kind: route
title: Kill the polynomial core and apply the unique-trace theorem to the Bass--Serre action
target: kt-q2-reduced-cstar-has-unique-trace
requires: []
artifacts:
  - notes/UNIQUE_TRACE_KUN_THOM_DOUBLE.md
---

First show that the normal core of `Gamma` in `G` is trivial.  If
`N normal G` lies in `Gamma` and `z=(z_kl) in N`, conjugate `z` by the
elementary matrix `1+x_1^(-m)E_ij`.  The conjugate belongs to
`N subset EL_r(F_2[x_1,...,x_d])` for every `m`.  Looking first at its
off-diagonal entries and then at its diagonal differences forces `z` to be
scalar.  The only unit in the polynomial ring over `F_2` is `1`, so `z=1`.

The Bass--Serre action of `D=G *_Gamma G` is therefore faithful: an element
in its kernel lies in a vertex stabilizer and in the intersection of all
adjacent edge stabilizers, which is the core just computed.  The action is
minimal and non-elementary because both edge inclusions are proper and
`[G:Gamma]=infinity` (the projection to `SL_d(Z)` vanishes on `Gamma`).

Let `A normal D` be amenable.  An amenable group acts elementarily on a tree.
A hyperbolic element in `A` would give a finite normal limit set in the
boundary, and an elliptic action without a fixed vertex would give a unique
normal fixed end; either contradicts non-elementarity of the ambient action.
Thus `A` fixes a subtree.  Normality makes it `D`-invariant, minimality makes
it the whole tree, and faithfulness gives `A=1`.

The Breuillard--Kalantar--Kennedy--Ozawa unique-trace theorem identifies
triviality of the amenable radical with uniqueness of the tracial state on
the reduced group C-star algebra.  Hence the sole trace on `C*_r(D)` is the
canonical regular trace.
