---
rg: 2
id: sofic-recognition-has-a-pi2-upper-bound
kind: claim
title: Soficity is Pi-zero-two for recursive presentations, with a primitive recursive certificate checker
artifacts:
  - GroupApproximation/Computability/SoficEnumeratedPi02.lean
  - GroupApproximation/Computability/SoficRecognitionPi02.lean
  - GroupApproximation/Computability/SoficMicrostateNormalForm.lean
  - GroupApproximation/Sofic/Sofic.lean
  - GroupApproximation/Covers/TableCover.lean
  - research/artifacts/second-level-rice-theorem-2026-08-26.md
distinct_from:
  lef-recognition-has-a-pi2-upper-bound: that certifies with exact finite groups and needs no metric; this certifies with permutation tuples whose relator defects are only small, and the area bookkeeping that turns small relator defects into a model of the ball is the new step.
  mf-recognition-has-a-pi2-upper-bound: that needs unitary matrices and a real-closed-field decision procedure; this needs only finite permutations and exact rational Hamming distances, so its checker is primitive recursive.
  nonhyperlinear-presentation-codes-have-a-sigma2-upper-bound: that is the Hilbert--Schmidt unitary analogue for finite presentation codes; this is the permutation version for recursive presentations, and it is the upper half of the sofic completeness theorems.
---

ESTABLISHED.  Uniformly in a recursive presentation `P = <X | r_1, r_2, ...>`
of a finitely generated group `H`, with `d` the normalized Hamming distance on
`Sym(Y)` and `sigma` extended from `X` to words,

```text
H is sofic   iff   for all (W, N, k):
      (exists w in W, w = 1 in H)
   or (exists finite Y, sigma : X -> Sym(Y):
         d(sigma(r_j), id) <= 1/k   for j <= N,
         d(sigma(w),   id) >= 1 - 1/k  for w in W),                  (SOF1)
```

where `W` ranges over finite lists of words and `N, k` over positive
integers.  The first disjunct is `Sigma^0_1` (the word problem of a recursive
presentation is r.e.); the second is a bounded search over finite sets and
permutation tuples whose body is decided by exact rational arithmetic, hence
`Sigma^0_1` with a primitive recursive checker.  Therefore

```text
SOFIC_rec is Pi^0_2,      NONSOFIC_rec is Sigma^0_2,                   (SOF2)
```

and the same holds for finite presentation codes and for finitely generated
subgroups of a fixed finitely presented group given by generating tuples,
whose induced presentations are recursive uniformly.

Unlike the MF and hyperlinear bounds, no decision procedure for the real
closed field is used: everything in the certificate is finite combinatorics.
This is the upper half of
[[sofic-recognition-two-generator-recursive-is-pi2-complete]] and of
[[sofic-recognition-finite-presentations-arithmetical-position]].

**Machine-checked.**  For finite presentation codes the normal form is
`SoficMicrostateNormalForm.isSofic_iff_forall_answers`, the certificate
checker is a computable Boolean predicate, and
`SoficRecognitionPi02.pi02_isSofic` is the closed `Pi02` statement, with
`sigma02_not_isSofic` for the complement; the recursive-presentation
variant with a relator prefix is in progress.

**Machine-checked on enumerated codes.**  `SoficEnumeratedPi02.isSofic_iff_forall_answersN` is (SOF1) with the relator prefix, and `pi02_isSofic_enum` is the closed `Pi02` statement on enumerated presentation codes.
