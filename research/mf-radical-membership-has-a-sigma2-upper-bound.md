---
rg: 2
id: mf-radical-membership-has-a-sigma2-upper-bound
kind: claim
title: MF-radical membership in a finite presentation is Sigma-zero-two
artifacts:
  - GroupApproximation/Sofic/NormMFCoronaRadical.lean
  - GroupApproximation/Sofic/NormMFUniversalCorona.lean
  - GroupApproximation/Sofic/OperatorMFPairAmplification.lean
distinct_from:
  universal-mf-quotient: that identifies radical membership with equality in the universal MF-visible quotient; this classifies the arithmetical complexity of that equality predicate.
  single-finitely-presented-mf-radical-computer: that makes identity undecidable under a promise that every hard word lies in the radical; this gives a uniform upper bound for actual radical membership.
  fixed-non-mf-radical-membership-undecidable: that supplies lower-bound undecidability for one fixed group; this is the uniform second-level upper bound.
---

Uniformly in a finite presentation code `P` and a raw word `w`,

```text
w notin Res_MF(Carrier P)  is Pi^0_2,
w     in Res_MF(Carrier P) is Sigma^0_2.                  (RAD1)
```

The same upper bound remains after fixing `P`, so the MF radical of every
fixed finitely presented group is a `Sigma^0_2` set of words.

At scale `n` and dimension `d`, ask for a unitary generator tuple with
relator defect at most `eta_n` and `||w(U)-1|| >= 1/2`.  Fixed-dimensional
feasibility is decidable over the real closed field.  Cairn's marked
sequential extraction, pair amplification, and norm-corona machinery gives

```text
w notin Res_MF(Carrier P)
    iff forall n, exists d, D(P,w,n,d).
```

As with the recognition upper bound, the analytic equivalence is backed by
machine-checked corona and amplification APIs, while the final effective
real-closed-field checker is paper-level and is not advertised as a closed
Lean theorem.
