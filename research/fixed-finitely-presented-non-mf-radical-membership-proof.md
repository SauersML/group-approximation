---
rg: 2
id: fixed-finitely-presented-non-mf-radical-membership-proof
kind: route
title: Retract a non-MF free product onto Kharlampovich's MF factor
target: fixed-non-mf-radical-membership-undecidable
requires:
  - finitely-presented-sofic-non-mf
  - finitely-presented-amenable-undecidable-word-problem
  - mf-radical-functoriality
  - universal-mf-quotient
  - mf-radical-membership-has-a-sigma2-upper-bound
artifacts:
  - GroupApproximation/Sofic/FreeProductMFRadicalRetraction.lean
  - non_mf_group_notes.tex
---

Let `pi_A:E*A -> A` kill `E` and restrict to the identity on `A`.  Since `A`
is MF, `Res_MF(A)=1`.  Functoriality gives

```text
pi_A(Res_MF(E*A)) <= Res_MF(A)=1,
```

or equivalently `Res_MF(E*A) <= ker(pi_A)`.  Therefore

```text
i_A(a) in Res_MF(E*A) => pi_A(i_A(a))=a=1.
```

The converse holds because the identity lies in every subgroup.  The inclusion
of raw `A`-words into free-product words is computable, so a radical-membership
decider would decide the word problem of `A`.  This proves undecidability.

The free factor `E` embeds in `U`, so subgroup heredity makes `U` non-MF.  The
free product of two finite presentations is finite, hence `U` is finitely
presented.  No exact computation of `Res_MF(E)` is used.
