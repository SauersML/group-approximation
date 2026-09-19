---
rg: 2
id: bohr-residual-equals-finite-residual-for-profinite-targets
kind: claim
title: For profinite targets the Bohr theory is the finite-quotient theory
distinct_from:
  commuting-lamp-quotient-finite-residual: That computes the finite residual of one specific witness group; this is a general statement identifying two residuals of an arbitrary discrete group when the targets are restricted to profinite ones, and names no witness.
artifacts:
  - GroupApproximation/Analysis/PeterWeylProfinite.lean
  - GroupApproximation/Sofic/FiveRadicalsCoincide.lean
---

ESTABLISHED, unconditionally.  `Analysis/PeterWeylProfinite` defines the
**Bohr residual** `bohrResidual G` -- the elements of a discrete group killed
by every homomorphism into a compact Hausdorff group -- which the repository
did not previously have, and proves

* `bohrResidual_le_finiteResidual`: a finite group with the discrete topology
  is a compact Hausdorff topological group, so this direction needs no
  analysis;
* `finiteResidual_le_ker_of_profinite`: if the compact target is totally
  disconnected, every homomorphism into it kills the finite residual;
* `bohrResidual_eq_finiteResidual_of_profinite_only`: the resulting two-sided
  statement, in the form the dossier's sections 46.5 and 49.12 use.

So finite quotients already separate the points of a profinite group, and a
homomorphism into a profinite group sees nothing a finite quotient does not.

## Two design points worth keeping

The target groups range over `Type` rather than over a universe of all compact
groups, as with `linearResidual`, so no quantification over a proper class is
needed.  And because the source group is discrete, no continuity condition on
the homomorphisms is required -- which is why the definition is usable
verbatim by the radical chain of `Sofic/FiveRadicalsCoincide`.

## What it does not give

The general compact case.  For that the analytic core is isolated as the named
hypothesis recorded in the
[archived Peter--Weyl formalization note](artifacts/peter-weyl-separation-core.md), and
`fdUnitaryResidual_le_bohrResidual_of_separates` derives the remaining
inclusion from it -- so the dossier's Bohr clauses are conditional on one
precisely stated classical input rather than on a remark.
