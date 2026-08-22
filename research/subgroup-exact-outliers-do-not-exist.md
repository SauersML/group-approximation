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

- **DEMOTED TO OPEN (2026-08-21 adversarial audit).**  The route's Step 2
  lemma ("representations at distance `o(1)` in normalized character are
  equivalent for large `m`") is false -- `close-normalized-characters-do-not-force-equivalence`
  gives the counterexample `pi_0 (+) tau_m` with one small non-invariant
  constituent -- and it invalidates `subgroup-exact-outliers-route`.  The
  (T)-estimate yields only a partial-isometry intertwiner with `o(d)`
  co-support; Step 3 never shows that the cut corners can be made
  simultaneously invariant under the `n` coset conjugators (their products
  satisfy `u_i u_j = c(i,j) u_(ij)` only up to `O(eta_m)`, so they do not
  act as a finite group on projections of the commutant); Step 4 cites a
  nonexistent vanishing theorem for `U(C_m)`-valued cocycles and gives no
  norm control on the trivialization.  The THEOREM is still expected to be
  true (no counterexample is known; the audit's own counterexample to the
  lemma is `O(sqrt(eps_m))`-close to a genuine representation).  The
  correct proof shape is: partial intertwiners from (T); a simultaneous
  invariant corner or a flexible padding argument; then a Kazhdan-style
  averaging-plus-polar trivialization of the NEAR-IDENTITY `U(C_m)`-cocycle
  over the finite group `Lambda / Lambda_0` (a `T`-valued cocycle near `1`
  lifts to `R`, and `H^2(F, R) = 0`), with an explicit `O(eta^(1/2))` loss.
  Consequence caveat even after repair: the output is a PROJECTIVE
  representation; the "everywhere-inexact outliers" corollary needs the
  (RC3) machinery to be insensitive to a finite central twist, which is not
  argued here.  All downstream sentences that describe the outlier habitat
  as "non-exact on every finite-index subgroup" are conditional on this
  claim.
