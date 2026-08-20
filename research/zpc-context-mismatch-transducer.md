---
rg: 2
id: zpc-context-mismatch-transducer
kind: claim
title: ZPC predication contexts can charge cross-context mismatch to LCS loss
artifacts:
  - research/artifacts/selector-overlap-rounding-2026-08-18.md
  - research/artifacts/compiler-lowering-hyperlinear-2026-08-18.md
distinct_from:
  zpc-selector-robust-lcs-compiler: that is the full quantitative compiler theorem; this isolates the remaining context-consistency inequality after priority decoding has removed selector overlap from the problem.
  zpc-context-overlap-mismatch-transducer: that asks one estimate to pay selector overlap and cross-context mismatch simultaneously; this factors through odd-selector priority decoding first and isolates only the post-decoding gluing debt.
---

For the fixed finite tailored game `G` supplied by
`perfect-zpc-irs-quantum-gap-game`, construct a finite binary LCS together with
a finite family of **local predication contexts** `c` (for example edge
contexts) such that perfect ZPC-IRS strategies compile perfectly and the
following quantitative statement holds.

From every finite-dimensional output strategy of loss `epsilon`, extract in
each context commuting selector involutions `Z_(c,a)` and predicated branch
copies `G_(c,a,i)`.  Write

```text
W_c = product_a Z_(c,a),
E_c = (1-W_c)/2.
```

Apply [[odd-selector-priority-decoding]] inside `E_c` and then
[[onehot-predicated-direct-sum-decoder]].  Let `D_pred` be the weighted total
squared defect of the compiled predicated branch equations and let `D_glue`
be a weighted squared mismatch between the resulting decoded copies of every
unreadable question observable occurring in two incident contexts.

There is a constant `C`, independent of matrix dimension, such that

```text
sum_c (1/4)||W_c+1||_2^2 + D_pred + D_glue
  <= C epsilon.                                         (CTX')
```

The mismatch may be measured after the canonical corner identifications used
by the construction; only a dimension-free spanning-tree gluing estimate is
required downstream.

## What has been removed

No pairwise selector-overlap term occurs in `(CTX')`.  Raw selectors may have
large or even maximal overlap.  Odd parity guarantees that every joint atom
has at least one active branch, and priority decoding assigns it to one such
branch without losing mass.  The affine and finite-group selector barriers
therefore do not block this target: the output relations need not prune the
additional odd selector characters.

## Attempts

- **Parity and predicated equations are already linear.**  One parity row per
  context controls the first term, and
  `controlled-linear-predication-normal-form` supplies the branch equations.
- **Only context consistency remains.**  Choose one reference context per
  question and add bounded-degree equality/covariance checks along a spanning
  tree of its incident contexts.  The target is an `L^2` Poincare-style bound
  from those local test losses to `D_glue`, with constants depending only on
  the fixed finite source game.
- **Do not globalize readable bits unnecessarily.**  The source ZPC hypotheses
  provide local commutation, not one global readable algebra.  The transducer
  should glue decoded unreadable observables across contexts rather than
  assume all remote selectors commute.
