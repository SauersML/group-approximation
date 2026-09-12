---
rg: 2
id: kun-thom-finitary-action-has-no-normalizer-lift
kind: claim
title: The explicit Kun--Thom finitary symmetric action has no trace-correct homomorphic lift to the normalizer of R in its ultrapower
invalidates:
  - kun-thom-finitary-normalizer-lift-proves-hyperlinear-wreath
artifacts:
  - notes/HYPERLINEAR_NONSOFIC_ATTEMPT_2026-08-26.md
distinct_from:
  kun-thom-finitary-action-lifts-to-normalizer: that is the exact positive branch of this decision problem; this is its negative branch.
  invariant-cartan-completion: that asks to recover a diagonal algebra from every abstract embedding of the original abelian-lamp crossed product; this asks directly for non-splitting of a nonabelian normalizer extension for the larger factor-base action.
  kt-centralizer-normalization-hs: that is a relative-commutant collapse statement for arbitrary models of the compression pair; this only asks whether one explicit action on the hyperfinite factor has a trace-correct lift.
---

Use `G`, `Gamma`, `Y`, `R` and `alpha` from
`kun-thom-finitary-action-lifts-to-normalizer`.  There is no homomorphism

```text
u:G -> N_(R^omega)(R)
```

which implements `alpha` and satisfies

```text
tau(x u_g)=0                    (x in R, g != 1).       (KFN1)
```

Equivalently, the pullback normalizer extension has no trace-correct
section, and by `finitary-extension-ce-iff-action-lifts-to-normalizer` the
crossed product `R rtimes_alpha G` is not Connes embeddable.

This is OPEN and is exactly the negative side of the new finitary-extension
fork.  Pointwise approximate-inner lifts do not address it: the obstruction
must show that the resulting `U(R' cap R^omega)`-valued two-cocycle cannot be
killed simultaneously for the two positive compressors.

