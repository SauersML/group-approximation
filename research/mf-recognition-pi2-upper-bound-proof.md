---
rg: 2
id: mf-recognition-pi2-upper-bound-proof
kind: route
title: Arithmetize the normalized operator-norm microstate challenge
target: mf-recognition-has-a-pi2-upper-bound
requires:
  - countable-group-mf-conventions
  - word-problem-of-finite-presentation-is-re
  - mf-recognition-undecidable
artifacts:
  - GroupApproximation/Computability/CodedMicrostate.lean
  - GroupApproximation/Computability/MicrostateNormalForm.lean
  - GroupApproximation/Analysis/OperatorNormCertificate.lean
  - GroupApproximation/Analysis/RatComplexSubfield.lean
---

Fix `P=<x_1,...,x_k | r_1,...,r_s>` and a computable positive rational
sequence `eta_n -> 0`, for example `2^(-n-10)`.  Let `B_n` be the finite word
ball.  A certificate contains a dimension, a bit for every member of `B_n`,
and a finite normal-closure derivation for every word whose bit is `TRIVIAL`.
It passes if all those derivations check and there is a `d`-dimensional
unitary tuple with

```text
||r_j(U)-1|| <= eta_n,
||w(U)-1||   >= 1/2       for every SEPARATE word w.
```

For fixed discrete data this is a first-order real-closed-field sentence:
complex entries split into real and imaginary parts, unitarity and word
evaluation are polynomial, and an operator-norm upper or lower bound is
expressed by quantifying over real unit vectors.  Effective quantifier
elimination makes validity recursive.  Equivalently, Cairn's in-progress
rational route uses exact rational unitaries
(`RatComplexSubfield.exists_rat_unitary_close`) and finite strict norm
certificates (`OperatorNormCertificate`).

If `G_P` is MF, normalized local models with separation `1` give certificates
at every scale.  Telescope the generator values along each bounded word,
label exactly the trivial words `TRIVIAL`, and attach their finite derivations.
The margin between `1` and `1/2` absorbs all telescoping errors.  This analytic
direction is subsumed by the forward half of the machine-checked theorem
`MFMicrostate.isOperatorMF_iff_forall_answers`.

Conversely, fix a finite subset `F` of `G_P`, choose representative words, and
collect the finitely many multiplication words

```text
u_g u_h u_(gh)^-1.
```

Each has a finite normal-closure proof.  If `A` bounds their areas, Cairn's
machine-checked `exists_area_bound_list` gives displacement at most
`A*eta_n`.  Choose `n` so all needed words lie in `B_n` and
`A*eta_n<epsilon`.  A genuine difference word cannot carry a sound
`TRIVIAL` certificate, so its certificate bit supplies the uniform `1/2`
separation.  The result is a weak MF model, and
`IsWeakMF.isOperatorMF` finishes.  This is the backward half of
`microstateNormalForm` in repository-native form.

Therefore `MF(P)` has a `forall n exists c` recursive matrix and is `Pi^0_2`;
its complement is `Sigma^0_2`.  Finally
`MFRecognitionImpossible.nonMF_presentations_not_re` excludes
`NONMF from Sigma^0_1`, and complementation excludes `MF from Pi^0_1`.
