---
rg: 2
id: mf-recognition-recursive-presentations-is-second-level-complete
kind: claim
title: MF and non-MF recognition are exactly second-level complete for recursive presentations
artifacts:
  - GroupApproximation/Computability/MFEnumeratedMicrostate.lean
  - GroupApproximation/Computability/MFEnumeratedNormalForm.lean
  - GroupApproximation/Computability/MFEnumeratedPi02.lean
  - GroupApproximation/Endpoint/MFEnumeratedPi02Audit.lean
distinct_from:
  mf-recognition-has-a-pi2-upper-bound: that is the finite-presentation upper bound; this supplies matching FIN and INF hardness on infinitely generated recursively presented groups.
  mf-recognition-finite-presentations-is-pi2-complete: that transports this recursive hardness through the finite-CEP graph witness and tensor-synchronized Higman rope.
---

For the natural effective coding of countably generated recursively presented
groups,

```text
NONMF_rec is Sigma^0_2-complete,
MF_rec    is Pi^0_2-complete.
```

The hardness reduction is uniform and uses only one fixed finitely presented
non-MF group.  The upper-bound certificate argument applies unchanged to a
recursive relator stream after adding the relator-prefix index to the scale.
This statement does not assert anything about finite-presentation hardness.

## Lean

Both classifications are stated on the standard recursively enumerated
presentation codes (`Nat.Partrec.Code`, relators read off the bounded
evaluator), the same syntax as the sofic and LEF classifications.

* `MFEnumeratedNormalForm.isOperatorMF_iff_forall_openAnswersM`: MF-ness is
  exactly "every challenge `(W, N, k)` is void or has a unitary microstate
  displacing the relators at addresses `0, …, N` by less than `1/(k+1)` and
  every word of `W` by more than `1/3`".  The area bound relative to a relator
  prefix (`exists_matrix_area_bound_list`) is what makes finitely many
  relators enough.
* `MFEnumeratedPi02.pi02_isOperatorMF_enum`: the microstate disjunct of a
  challenge is decided by the finite-code matrix checker of
  `MFRecognitionPi02`, applied to the finite code cut from the challenge
  (`challengeCode`: alphabet one letter past every letter of `W` and of the
  first `N + 1` relators, relators those `N + 1` words).  So the upper bound
  needs no new certificate machinery.
* `MFEnumeratedPi02.mf_enum_pi02Complete` and `nonmf_enum_sigma02Complete`
  pair that upper bound with
  `EnumeratedFixedMarkedQueryCompleteness.operatorMFCode_pi02Hard`; the
  closed form `mfEnumeratedExactClassification` carries no hypothesis and is
  a conjunct of `ArithmeticalLedgerEndpoint.arithmeticalLedgerHolds`.

The finite-presentation companion
`mf-recognition-finite-presentations-is-pi2-complete` remains conditional in
Lean on the effective marked Higman compiler
(`Manuscript.MFRecognition.EffectiveHigmanCompiler`), the HNN-permanence
input bundle, and the per-index rope inputs; nothing here touches that.
