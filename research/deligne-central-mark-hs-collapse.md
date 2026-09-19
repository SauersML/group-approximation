---
rg: 2
id: deligne-central-mark-hs-collapse
kind: claim
title: Vanishing HS presentation defect forces the Deligne triple-cover central mark to collapse
artifacts:
  - research/artifacts/deligne-maslov-hyperlinear-strategies-2026-08-21.md
distinct_from:
  hyperlinear-hs-stable-is-residually-finite: that repairs every generator of a hyperlinear microstate to an exact same-dimensional representation; this asks only that one named central word converge to the identity, with no nearby representation required.
  hs-schur-toeplitz-root-defect-collapse: that collapses an engineered Toeplitz/Steinberg root mark through coefficient recurrence; this is the analogous one-word target for Deligne's arithmetic order-three central mark.
  infinite-hyperlinear-kazhdan-group-is-not-hs-stable: that obstructs local HS stability of any infinite hyperlinear property-T group; this claim is much weaker than local stability and is tailored to a single explicit finite presentation.
---

For the explicit triple-cover extension

```text
1 -> <z>=Z/3 -> E_3 -> Sp_4(Z) -> 1,
```

fix any finite presentation containing the central word `z`.  Every sequence
of unitary tuples whose normalized-HS defects on the defining relators tend to
zero satisfies

```text
||phi_n(z)-I||_(2,d_n) -> 0.                              (DCM1)
```

No correction of the other generators is required.

For this particular cover, `deligne-sector-gap-is-exactly-nonhyperlinearity`
shows that `(DCM1)` is nevertheless equivalent to non-hyperlinearity itself.
If collapse fails, central-sector cutting produces a nontrivial projective
almost representation; tensoring it with canonical quotient microstates
makes the whole cover hyperlinear.  Hence the one-word formulation reduces
the number of words to control, but not the logical strength of the terminal
claim.

## Attempts

- **Central-character cut.** `finite-central-hs-sector-decomposition` reduces
  a counterexample to positive asymptotic dimension in the `alpha` or
  `alpha^2` projective sector of `Sp_4(Z)`.  Thus
  `maslov-mod3-projective-defect-gap` is a clean sufficient condition.
- **Do not prove full stability unless forced.**  Deligne already kills the
  mark in every exact finite-dimensional representation.  Repairing every
  generator throws away information and imports the whole Becker--Lubotzky
  instability wall; `(DCM1)` needs only a one-word estimate.
- **Property-T fallback.**  Since `E_3` is a finite central extension of the
  rank-two lattice `Sp_4(Z)`, it has property (T).  Proving local HS stability
  of `E_3` would also imply non-hyperlinearity by
  `infinite-hyperlinear-kazhdan-group-is-not-hs-stable`, but it is a strictly
  stronger target than `(DCM1)`.
