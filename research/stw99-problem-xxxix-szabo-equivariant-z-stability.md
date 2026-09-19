---
rg: 2
id: stw99-problem-xxxix-szabo-equivariant-z-stability
kind: claim
title: All amenable-group actions on Z-stable classifiable algebras are equivariantly Z-stable (STW Problem XXXIX, Szabo's Conjecture A)
root: true
artifacts:
  - research/artifacts/stw99-dynamics-cluster-2026-08-30.md
---

**Problem XXXIX of Schafhauser--Tikuisis--White, arXiv:2506.10902**
(Szabo, Conjecture A, Anal. PDE): if `G` is countable discrete
amenable and `A` unital simple separable nuclear `Z`-stable, is every
action `G ↷ A` cocycle conjugate to `α ⊗ 1_Z : G ↷ A ⊗ Z`?  No
outerness is assumed — the C*-analogue of Ocneanu / Szabo--Wouters
automatic equivariant McDuffness (which needs no outerness either).

## Attempts

* The von Neumann model is a THEOREM (Szabo--Wouters: amenable actions
  on separably-acting McDuff algebras are equivariantly `R`-stable,
  factoriality not required), so the conjecture is a lifting problem
  of exactly the shape of the Toms--Winter von Neumann strategy:
  transport the equivariant McDuffness of the trace-kernel quotient
  back through the surjection onto the tracial central sequence
  algebra.  The non-equivariant version of that transport is CPoU,
  available from uniform Γ (automatic here); the equivariant version
  needs `G`-invariant complemented partitions — for finite `G` and
  `Z` this is what Szabo's school has done in the finite/compact
  boundary settings, and the wild-boundary equivariant CPoU is the
  same single missing glueing recorded at XXXVIII.  A counterexample
  would need an amenable action mixing the trace simplex so that
  invariant partitions cannot follow the fibrewise Ocneanu data —
  impossible for actions fixing traces pointwise, so any refutation
  acts wildly on `∂_e T(A)`; the first candidate family is Bernoulli-
  type shifts on `Z`-stable algebras with Poulsen simplex, where
  nothing is computed.
