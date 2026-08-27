---
rg: 2
id: five-radicals-from-residually-finite-target
kind: route
title: Squeeze the four outer residuals between the MF radical and a residually finite quotient
target: compression-wreath-five-radicals-coincide
requires: [wreath-compression-mf-radical]
artifacts:
  - research/artifacts/multi-mover-hnn-dossier-2026-08-15.md
  - GroupApproximation/Sofic/LinearResidual.lean
  - GroupApproximation/Sofic/FiveRadicalsCoincide.lean
  - GroupApproximation/Analysis/PeterWeylProfinite.lean
---

## Why sufficient

The prerequisite gives `Rad_MF(W_K) = R_K` with quotient
`P_K = K_ab^(Z) x| G*`.  Everything else is a squeeze between two ends.

**Generic chain.**  A finite quotient has a faithful finite-dimensional
permutation representation and a finite-dimensional unitary representation is
a constant-sequence corona representation, so for every group

    Rad_MF <= Rad_fd <= Res_fin,      Rad_lin <= Res_fin.

`LinearResidual.lean` carries `linearResidual_le_fdUnitaryResidual` and
`linearResidual_le_finiteResidual`.

**The far end is residually finite.**  `G*` embeds in `GL_4(Z[1/2])` and is
residually finite by clearing denominators and reducing at an odd prime; the
finite abelian lamplighter `A^(Z) x| Z` is residually finite by reducing the
shift modulo a large `m` and summing lamps over residue classes.  `P_K`
embeds in the product of the two, so `P_K` is residually finite.  Hence any
`w` outside `R_K` is separated by a finite quotient of `P_K` pulled back, so
`Res_fin(W_K) <= R_K` and the chain collapses:
`Rad_MF = Rad_fd = Res_fin = R_K`.

**Linear layer.**  A finitely generated linear group over any field is
residually finite: the entries of a finite symmetric generating set generate a
finitely generated integral domain `R`, and for a nonzero entry `r` of `g - I`
one localizes at `r`, quotients by a maximal ideal, and uses that a field
finitely generated as a ring is finite (Zariski's lemma, plus the
characteristic-zero exclusion via non-integrality of `1/p` over `Z[1/N]`).
The image `rho(W_K)` is finitely generated linear, hence residually finite, so
`rho` cannot detect anything in `Res_fin(W_K) = R_K`; conversely the regular
representation of a finite quotient is linear.  So `Rad_lin = R_K`, `W_K` is
nonlinear over every field, and by the finite-index permanence of residual
finiteness it is not virtually linear either.

**Compact layer.**  Peter--Weyl: finite-dimensional continuous unitary
representations separate points of a compact Hausdorff group, so
`Rad_Bohr = Rad_fd = R_K`, and `W_K` is not maximally almost periodic.

**Factorization form.**  Each equality says every map to the corresponding
target class kills `R_K`; the universal property of the quotient turns that
into unique factorization, and surjectivity of `W_K -> P_K` makes the
factorization bijective on Hom-sets.  For MF targets one restricts a faithful
corona representation of the target to the image; for residually finite
targets one composes with a separating finite quotient.

Finally `R_K = Res_fin(W_K)` is the intersection of all finite-index
subgroups, normal or not, because the normal core of a finite-index subgroup
is again finite index.

## Named classical inputs

Zariski's lemma and Peter--Weyl are used as stated, at the two points marked
above.  Everything else is proved in section 46 of the dossier.

**Where Peter--Weyl now sits in the development.**  It is no longer a remark.
`Analysis/PeterWeylProfinite` defines the Bohr residual, proves
`bohrResidual <= finiteResidual` outright, and isolates the analytic core as
the single named hypothesis `SeparatesPoints`
([archived Peter--Weyl formalization note](artifacts/peter-weyl-separation-core.md)), from which
`fdUnitaryResidual_le_bohrResidual_of_separates` derives the remaining
inclusion.  For **profinite** targets nothing is assumed at all:
[[bohr-residual-equals-finite-residual-for-profinite-targets]] is unconditional
by van Dantzig, and `Sofic/FiveRadicalsCoincide` carries both forms
(`five_radicals_eq` under the separation hypothesis, `five_radicals_eq_profinite`
with none).  So the classical input used here is one precisely stated lemma
about compact groups rather than a citation.

## Priority

The coincidence of five distinct invisibility notions on one explicit kernel
is the part flagged as potentially significant; it appears neither in the
circulated criterion nor in Fournier-Facio's remarks, both of which stop at
"one nontrivial element dies."
