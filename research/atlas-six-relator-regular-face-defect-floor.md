---
rg: 2
id: atlas-six-relator-regular-face-defect-floor
kind: claim
title: The regular common-frame six-relator face has a uniform positive defect floor
distinct_from:
  atlas-six-relator-relative-h-bridge-gap: that asks the six nonlinear rows to control four relative H bridge words quadratically; this asks only for one scalar positive lower bound on the sum of the six nonlinear defects.
  atlas-six-relator-hyperlinear-escape-test: that identifies exact matrix-ultraproduct zeroes with nontrivial hyperlinear quotients; this is the finitary uniform-gap formulation on the regular common-frame matrix coordinates.
  atlas-five-row-operator-phase-lift: that compares the six nonlinear defects to five additive covariance rows; this contains no additive row and no bridge observable.
---

**OPEN.** In the regular common-frame coordinates, put

```text
D_6(U)=sum_(j in {0,11,30,44,55})||pi_U(s_j)-1||_2^2
                         +||pi_U(c_19243)-1||_2^2.    (RDF1)
```

Prove that there is one `eta_6>0`, independent of the external regular
multiplicity `k`, such that

```text
D_6(U)>=eta_6                                             (RDF2)
```

for every `U in U(20160k)` and every `k>=1`.

This is a smaller scalar endpoint than the four-word relative bridge
inequality. It does not ask which bridge survives or how much individual
relators pay for it. It only asks that the six-relator zero set stay a
uniform positive normalized-Hilbert--Schmidt distance from the regular
common-frame matrix locus.

The target is nevertheless sufficient, and in fact quantitatively
equivalent, to `atlas-five-row-operator-phase-lift`. The forward implication
uses only the fixed upper bound on the five additive rows. The reverse
implication uses `atlas-five-row-blowup-branch-is-impossible`; see
`atlas-six-relator-defect-floor-equivalence-proof`.

By compactness through a tracial matrix ultraproduct, failure of `(RDF2)` is
equivalent to an exact regular common-frame model of all six relators.
Hence `atlas-six-relator-hyperlinear-escape-test` also identifies failure of
this scalar floor with a nontrivial hyperlinear quotient of `Gamma_6`.
No proof of `(RDF2)` is asserted here.

## Attempts

- Compactness gives a positive minimum for each fixed multiplicity, but no
  lower bound uniform in `k`; a sequence with `k` tending to infinity is
  exactly the hyperlinear-quotient enemy.
- A universal tracial positivity argument is impossible: the canonical
  Leavitt trace makes all six terms in `(RDF1)` zero. Thus any proof must use
  finite matrix coordinates rather than only the six group identities.
- Exact finite quotients have been screened through the current simple-index
  range, but residual finiteness of any surviving quotient would itself
  produce an exact zero of `(RDF1)`. Finite-target exclusion at bounded
  index is therefore evidence, not a uniform proof.
- The natural alternating family is now excluded in every degree by
  `atlas-six-relator-has-no-natural-alternating-target`: the repeated
  fixed-point-free second-chart letter in `s_0` forces the two natural
  supports to have union degree at most twelve, where the existing exact
  screens finish. This removes one infinite finite-simple family, but
  arbitrary non-natural finite-simple targets and diffuse hyperlinear
  quotients remain.
