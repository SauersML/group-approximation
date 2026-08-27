---
rg: 2
id: sl3-prime-stable-finite-actions-excludes-coset-soficity
kind: claim
title: Stability in finite actions of one-prime S-arithmetic SL3 would make its building-vertex action nonsofic
artifacts:
  - research/artifacts/alekseev-thom-2512.15494-verified.md
distinct_from:
  sl3-z-inverse-3-is-flexibly-p-stable: that asks for Hamming correction of every asymptotic action; this consumes only stability in finite actions, the strictly weaker weak-containment modulus for sofic approximations.
  sl3-prime-coset-action-exact-atlas-firewall: that proves every positive atlas must be noncorrectable; this shows the still weaker condition which excludes those noncorrectable atlases as well.
  sofic-coset-action-refutes-sl3-central-dual: that is the opposite conditional direction from a positive atlas to a central-dual counterexample; this identifies one precise named actor property which rules out that premise.
---

Fix a prime `p` and put

```text
Gamma=SL_3(Z[1/p]),             Lambda=SL_3(Z).                  (SSF1)
```

If `Gamma` is stable in finite actions, then

```text
Gamma curvearrowright Gamma/Lambda
```

is not sofic.

Indeed `Gamma` is residually finite, `Lambda` is Kazhdan, and
`sl3-prime-permutation-codensity` gives equality of their images in every
finite action.  Apply
`stable-finite-actions-blocks-codense-kazhdan-coset-soficity`.

This is the narrowest currently literature-recognized stability reduction
for the noncorrectable deck-cocycle sector.  It is strictly weaker than
flexible or very-flexible P-stability: no correction in Hamming distance is
requested, only weak containment of the limit action of a sofic
approximation in finite actions.

No known theorem establishes the hypothesis for `(SSF1)`.  The current
literature boundary is unusually sharp: Alekseev--Thom explicitly record
that it remains open whether **any** residually finite group fails to be
stable in finite actions.  Their quotient-inheritance theorem uses a
Kazhdan **normal** subgroup; `Lambda` is commensurated but not normal in
`Gamma`, so it does not apply to this pair.  Becker--Lubotzky's theorem only
refutes strict P-stability, via punctured finite actions that are flexibly
repairable, and therefore does not refute stability in finite actions.
The IRS/hyperfinite criteria classify statistics in special amenable or
hyperfinite regimes but do not provide weak containment for these
Kazhdan-expander component atlases.

DERIVATION
sl3-prime-stable-finite-actions-coset-proof
