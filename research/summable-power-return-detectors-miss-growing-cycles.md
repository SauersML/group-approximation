---
rg: 2
id: summable-power-return-detectors-miss-growing-cycles
kind: claim
title: Summable heavy-tail power-return detectors miss growing cyclic spectra
distinct_from:
  word-recursion-cannot-amplify-sublinear-summands: that defeats recursive copying by direct-sum dilution; this defeats spectral finiteness detectors even on one full-density unitary with perfectly uniform finite spectrum.
  affine-clone-model-defeats-pure-thompson-prefix-error-spreading: that gives exact finite affine models of binary clone axioms; this rules out finite, summably averaged, and decaying-supremum recurrence tests for a unitary shift.
  odd-root-wasserstein-target-is-vacuous: that shows a particular root-supported target contains all finite cyclic approximants; this gives a general quantitative no-go for weighted power returns converging to Haar moments.
---

Let `c_k>=0` with `sum_k c_k<infinity`, and define

```text
D_c(U)=sum_(k>=1)c_k |tr(U^k)|^2.
```

For the diagonal matrix `U_d` containing every `d`th root of unity once,

```text
tr(U_d^k)=1 if d divides k, and 0 otherwise,
D_c(U_d)=sum_(m>=1)c_(md)<=sum_(k>=d)c_k->0.             (SPR1)
```

Thus a summable heavy-tail average of exact power returns cannot distinguish
finite cyclic spectra from Haar spectrum with a dimension-independent positive
gap. The same conclusion holds with `|.|^2` replaced by any bounded function
vanishing at zero.

More generally, suppose the `k`th return relation costs at most `A(k)delta` in
a defect estimate. Any weighted proof with a dimension-independent total error
constant needs `sum_k c_k A(k)<infinity`; when `A(k)>=1`, `(SPR1)` applies. A
finite cutoff is defeated by `d` beyond the cutoff, and a supremum detector
with weights `c_k->0` is defeated by the first return at `k=d`.

An unweighted supremum over all powers does detect `U_d`, but controlling it
from finitely many relators would require an infinite family of checks at
constant local cost. Ordinary cyclic recurrence, finite truncation, or
summable/heavy-tail averaging cannot provide that.
