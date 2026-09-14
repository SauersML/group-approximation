---
rg: 2
id: weak-mf-does-not-imply-sofic
kind: claim
title: Operator-norm MF does not imply soficity
distinct_from:
  nonsofic-mechanism-mf-classification: that classifies three lamp types of one compression mechanism by their operator-MF verdict; this is the bare separation of the two approximation classes, with one witness.
  symmetric-double-weak-mf: that is the positive MF theorem for every symmetric double of a residually finite group; this adds nonsoficity of one such double and draws the separation.
  sofic-non-mf-witness: that separates in the opposite direction, a sofic group which is not MF; this is an MF group which is not sofic.
  mf-implies-hyperlinear: that asks whether operator MF gives the weaker trace approximations; this shows operator MF does not give the stronger permutation approximations.
---

ESTABLISHED.  There is a finitely generated group which is MF in the
Carrión--Dadarlat--Eckhardt operator-norm sense (an injective homomorphism into
the unitary group of a norm matrix corona, `IsOperatorMF`) and which is not
sofic.

**Witness.**  Let

```text
Gamma = EL_r(F_q[x_1,...,x_d]),
G     = EL_r(F_q[x_1^(+-1),...,x_d^(+-1)]) rtimes SL_d(Z),     r,d >= 3,
D     = G *_Gamma G.
```

`G` is residually finite (Kun--Thom Theorem E), so `symmetric-double-weak-mf`
makes `D` operator MF.  The same `D` is not sofic by
`kt-pair-group-double-is-nonsofic` (Kun--Thom, arXiv:2608.06222v3, Theorem A).
`D` is finitely generated because the Kazhdan group `G` is.

Together with `sofic-non-mf-witness` this makes operator MF and soficity
incomparable.

**Trust surface.**  The nonsoficity input is an imported unrefereed preprint;
the MF input rests on Shulman's symmetric-amalgam theorem applied to the
profinite regular completion, as recorded in `symmetric-double-weak-mf-proof`.

**What this does not give.**  No MF convention carrying trace data or
reduced-norm data is separated from soficity by this witness: operator-norm
separation can live on a subspace of vanishing normalized rank.  Which
conventions can separate at all is recorded in
`mf-convention-sofic-separation-map`.
