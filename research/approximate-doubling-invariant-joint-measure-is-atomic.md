---
rg: 2
id: approximate-doubling-invariant-joint-measure-is-atomic
kind: claim
title: Coupled parabolic data is near one common finite odd-order operator model
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
distinct_from:
  parabolic-spectrum-is-doubling-invariant: that is the single-parabolic spectral constraint; this is the joint rigidity that would actually close the far sector, using the coupling the ambient group imposes.
---

OPEN.  Replace the vacuous scalar-measure target by an operator target.
Prove (or refute) that a sufficiently accurate finite-dimensional tuple for
`SL_2(Z[1/2])`, including the two fourth-power conjugacies, the
`S`-conjugation between opposite parabolics, and the half-parabolic edge
relations, is close in normalized HS to one common finite-dimensional model
in which the parabolics have a common finite odd order and all the coupling
words hold exactly.  The modulus must be independent of matrix dimension.

## Attempts

- **Skeleton route now carries a full proof-plan (2026-08-21).**
  `common-odd-model-from-skeleton-relative-stability` reaches this
  target from `skeleton-relative-hs-stability-for-sl2`, whose state
  is: leg (1) PROVED (`bs14-exact-representation-variety-is-hs-
  locally-rigid` plus the top-down tower exactification); leg (2)
  reduced by the swap-transport move (define the lower tower BY the
  swap: `w(1)` exact, no amplified defects) to two unamplified
  fixed-word holonomies on compact centralizer torsors, with a
  spread/degenerate dichotomy and induction as the proposed closing
  argument.  What remains is accounting, not structure: loss
  accumulation along the induction and the joint two-holonomy step.

- The scalar Wasserstein version is invalidated by
  `odd-root-wasserstein-target-is-vacuous`: odd roots are dense, so every
  measure has such approximants.  The claim must control eigenvectors,
  multiplicities and joint moments strongly enough to reconstruct operators.
- **Noncommutative transfer route.**  Work with finite collections of mixed
  moments in `U,L,S` and the square-root word rather than marginal measures.
  The desired gap would have to exclude continuous invariant states while
  remaining compatible with congruence models converging to the regular
  trace.  No such joint-moment gap is presently proved.
- **Numerical status.**  `experiments/psl2_far_sector_probe.py` only measures
  distance from *short* tested odd orders.  It is a bounded falsifier for
  candidate optimization landscapes, not evidence for the operator theorem.

## The single-parabolic form is now PROVABLE (BS(1,4) skeleton, 2026-08-21)

Correction and upgrade.  The subgroup `<u, h> <= SL_2(Z[1/2])` with
`h u h^{-1} = u^4` is `BS(1,4) = Z rtimes_4 Z`, which is HS-stable
(Levit--Vigdorovich arXiv:2206.02268 Cor D(3); dense periodic measures for
the single ergodic solenoid automorphism, Marcus).  Hence every asymptotic
representation of `SL_2(Z[1/2])` has `(pi(u), pi(h))` HS-close to an EXACT
`BS(1,4)`-pair `(V_0, W_0)`, in which the base unitary `V_0` has finite ODD
order (its spectrum is a union of `z -> z^4`-cycles of odd roots of unity).
By Hoffman--Wielandt (unitaries are normal), the empirical spectral measure
of `pi(u)` is `W_2`-close to a measure EXACTLY supported on odd roots of
unity.  So the SINGLE-parabolic form of this claim is a theorem -- the
earlier "single-parabolic version is false (Gibbs)" was wrong (Gibbs
measures ARE weak-* limits of periodic measures, which is the mechanism of
BS(1,4) stability).

**But this does NOT close the far sector.**  Odd order `M -> infinity`
approximates any weak-* measure, so the atomic skeleton does not exclude a
Lebesgue/Gibbs-shaped COARSE spectral profile.  The upgrade is from
"measure approximately invariant" to "measure approximately supported on an
odd-order skeleton"; the remaining obstruction is the JOINT/coupled
statement (parabolic + opposite via the involution + the odd square root),
localized by the next node to spectral scale `1/M`.  The single-parabolic
theorem should be recorded, but the far sector is the joint version.
