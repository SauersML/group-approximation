---
rg: 2
id: mf-recognition-has-a-pi2-upper-bound
kind: claim
title: MF finite presentations are Pi-zero-two and non-MF finite presentations are properly Sigma-zero-two above RE
artifacts:
  - GroupApproximation/Computability/CodedMicrostate.lean
  - GroupApproximation/Computability/MicrostateNormalForm.lean
  - GroupApproximation/Analysis/OperatorNormCertificate.lean
  - GroupApproximation/Analysis/RatComplexSubfield.lean
  - non_mf_group_notes.tex
distinct_from:
  mf-recognition-undecidable: that proves first-level hardness and NONMF is not recursively enumerable; this supplies the second-level upper bound and combines the two facts into proper hierarchy containments.
  nonhyperlinear-presentation-codes-have-a-sigma2-upper-bound: that is the analogous tracial-microstate argument for hyperlinearity; this uses fixed operator-norm separation and classifies MF recognition.
  mf-recognition-finite-presentations-is-pi2-complete: that matching-hardness statement still needs an MF-safe finite-presentation compiler; this claim is only the unconditional upper bound and properness over the first level.
---

For the recursive coding `PresentationCodes.PresentationCode` of finite group
presentations,

```text
MF_fp     is in Pi^0_2,
NONMF_fp  is in Sigma^0_2.                               (MFH1)
```

Together with [[mf-recognition-undecidable]], which proves
`NONMF_fp` is not recursively enumerable, this gives the strict statements

```text
NONMF_fp is in Sigma^0_2 \ Sigma^0_1,
MF_fp    is in Pi^0_2    \ Pi^0_1.                       (MFH2)
```

The upper bound is witnessed by a recursive scale-certificate predicate.
For a code `P` and scale `n`, list the words of length at most `n`.  A
certificate records a dimension, labels each listed word `TRIVIAL` or
`SEPARATE`, supplies a finite normal-closure proof for every `TRIVIAL` label,
and asks for a unitary generator tuple with relator defect at most a computable
`eta_n -> 0` and displacement at least `1/2` on every `SEPARATE` word.  The
finite-dimensional feasibility question is decidable over the real closed
field.  Thus, for a recursive predicate `C_MF`,

```text
IsOperatorMF (Carrier P)  iff  forall n, exists c, C_MF(P,n,c).
```

The fixed separation is essential: it comes from Cairn's machine-checked
`OperatorMFLocalNormalization.isOperatorMF_iff_isNormApproximable_one` and
avoids an additional quantifier over a separation modulus.

The analytic normal form and the quantitative normal-closure estimate are
already machine-checked in `MFMicrostate.microstateNormalForm` and
`MFMicrostate.exists_area_bound_list`.  The final coding of the certificate
checker as a `Computable` Boolean predicate is paper-level: the current Lean
tree contains the rational-unitary density and norm-certificate machinery but
does not yet expose a closed `Pi^0_2` declaration.  This status boundary is
intentional and is part of the claim.
