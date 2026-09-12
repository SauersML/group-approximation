---
rg: 2
id: stw99-xciv-some-finite-tuple-has-positive-fd-radius
kind: claim
title: Some finite tuple in the hyperfinite factor has positive finite-dimensional norm radius
distinct_from:
  stw99-xciv-finite-dimensional-radius-controls-block-defect: that theorem proves finite-dimensional norm radius is an upper bound for the fixed-block defect; this theorem proves that radius cannot vanish on every finite tuple of R.
  stw99-xciv-two-norm-centrality-does-not-control-norm-centrality: that theorem constructs a sequence with vanishing 2-norm and maximal norm commutator; this theorem gives a finite, though nonexplicit, operator-norm obstruction to local finite-dimensional approximation.
  stw99-problem-x2-hyperfinite-factor-quasidiagonal: that root asks whether R is quasidiagonal; the present theorem only rules out local approximation by actual finite-dimensional subalgebras and makes no quasidiagonality assertion.
  stw99-xciv-finite-norm-spectral-gap-is-negative-certificate: that conditional theorem would obstruct local Jiang--Su copies; positive finite-dimensional radius alone does not give a fixed-block commutator gap and does not answer XCIV negatively.
artifacts:
  - research/artifacts/stw99-xciv-commutant-capacity-audit-2026-08-30.md
---

For finite `F subset R`, retain

```text
alpha_R(F)=inf_E max_(a in F) dist(a,E),
```

where `E` ranges over unital finite-dimensional C*-subalgebras of `R`.
Then there are a finite `F subset R` and a constant `c>0` such that

```text
alpha_R(F)>=c.                                           (1)
```

Thus hyperfiniteness does not make `R` norm-locally finite-dimensional.  In
particular the estimate

```text
gamma_(I_(2,3))(F)<=2 alpha_R(F)
```

cannot by itself prove the local fixed-block condition for all finite tests.

Statement `(1)` is not a negative answer to XCIV: a tuple can have positive
finite-dimensional radius while still admitting arbitrarily norm-central
`I_(2,3)` copies through a diffuse tensor commutant or another
infinite-dimensional mechanism.
