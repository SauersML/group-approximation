---
rg: 2
id: subgroup-exact-outliers-do-not-exist
kind: claim
title: Almost-representations exact on a finite-index Kazhdan subgroup are correctable, so subgroup-exact outliers do not exist
distinct_from:
  sl3z-regular-microstates-are-congruence-correctable: that is the full correctability hole (all regular microstates); this proves the special case where the microstates are EXACT on some finite-index subgroup, shrinking the outlier habitat to sequences non-exact on every finite-index subgroup uniformly.
  two-power-sector-conjugator-dichotomy: that dichotomy concerns the h-twisted pair, where the depth shift makes kernels differ and finite-level equivalence fails; this exploits the opposite phenomenon — integral conjugation preserves congruence levels, so the coset-twisted pairs are exactly equivalent at every level and the conjugacy branch is realized.
  lambda-exact-face-closes-at-p-three: that is a still-open proposed closure of the Lambda-exact face; this independently eliminates the subgroup-exact stratum of the outlier face.
---

THEOREM.  Let `Lambda_1 <= Lambda = SL_3(Z)` be any finite-index
subgroup (hence property (T) with Kazhdan pair `(F_1, eps_1)`), and
let `sigma_m : Lambda -> U(d_m)` be HS-almost-multiplicative maps
whose RESTRICTIONS to `Lambda_1` are genuine representations.  Then
`sigma_m` is asymptotically HS-close to genuine PROJECTIVE
representations of `Lambda` (with 2-cocycle in the finite group
`H^2(Lambda / core, T)`-range, trivializable after passing to a
finite central extension or a further finite-index restriction) —
uniformly, with constants depending only on `(Lambda : Lambda_1)`
and `eps_1`.  Consequently the uniform-outlier sector of the
correctability hole contains NO sequence exact on any finite-index
subgroup: outliers must be non-exact on EVERY finite-index subgroup
of `SL_3(Z)`, uniformly along the sequence.

MECHANISM (route).  Replace `Lambda_1` by its normal core
`Lambda_0`.  For each coset representative `g_i`, the element
`sigma_m(g_i)` almost-conjugates the genuine representation
`sigma_m|_(Lambda_0)` to `sigma_m|_(Lambda_0) compose Ad(g_i)`.
Because `g_i` is INTEGRAL, `Ad(g_i)` preserves every congruence
kernel — no depth shift, the exact opposite of the `h`-twist — so
the two representations are multiples of regular representations of
the SAME finite quotient with the SAME multiplicities: exactly
unitarily equivalent at every level.  The (T)-rigidity argument of
the conjugator dichotomy (conjugacy branch, realized) upgrades the
almost-conjugator `sigma_m(g_i)` to an exact conjugator `u_i` within
`2 eta / eps_1`; the corrected family `{u_i}` multiplies according
to the `Lambda_0`-cosets up to unitaries commuting with the exact
`sigma_m(Lambda_0)` and small errors, giving a genuine projective
representation after solving a finite cocycle problem over
`Lambda / Lambda_0` with coefficients in the commutant — a finite
group acting on a von Neumann algebra, where vanishing holds after
the stated finite adjustments.

## Attempts

- **What this changes for the single remaining target.**  The
  outlier enemy of `(RC3-p3)` now needs microstates that are
  uniformly far from genuine representations of EVERY finite-index
  subgroup simultaneously — "everywhere-inexact" sequences.  All
  congruence structure, at all levels and all finite-index
  localizations, is unusable by the enemy. This is a sharp habitat
  description of the outlier sector, independent of the still-open
  Lambda-exact spread sector.
- **Two-sided note.**  Everywhere-inexact almost-representations of
  higher-rank lattices are not known to exist; their construction
  would itself be a major theorem (a strong negation of stability),
  and their exclusion — the remaining step — is now a statement
  purely about uniformly-non-exact approximate representation
  theory, with every exactness loophole closed.
