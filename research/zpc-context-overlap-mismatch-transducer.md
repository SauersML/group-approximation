---
rg: 2
id: zpc-context-overlap-mismatch-transducer
kind: claim
title: ZPC predication contexts can charge selector overlap and cross-context mismatch to LCS loss
artifacts:
  - research/artifacts/selector-overlap-rounding-2026-08-18.md
  - research/artifacts/compiler-lowering-hyperlinear-2026-08-18.md
distinct_from:
  zpc-selector-robust-lcs-compiler: that is the full quantitative compiler theorem; this isolates the two remaining local energy inequalities after one-hot rounding and branchwise direct-sum decoding have already been proved.
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
P_(c,a)=(1-Z_(c,a))/2,
W_c=product_a Z_(c,a),
S_c=sum_(a<b) tau(P_(c,a) P_(c,b)).
```

Let `D_pred` be the weighted total squared defect of the compiled predicated
branch equations.  After applying the one-hot sector construction in each
context, let `D_glue` be a weighted squared mismatch between the decoded copies
of every unreadable question observable occurring in two incident contexts.
There is a constant `C`, independent of matrix dimension, such that

```text
sum_c ((1/4)||W_c+1||_2^2 + S_c)
  + D_pred + D_glue
 <= C epsilon.                                         (CTX)
```

The mismatch may be measured after the canonical corner identifications used
by the construction; only a dimension-free spanning-tree gluing estimate is
required downstream.

## Attempts

- **Standalone selector gadget.** Ruled out by
  `finite-group-selector-induction-barrier`: a finite gadget visible only
  through the commuting selector subgroup cannot prune the unwanted joint
  characters while retaining all one-hot ones.
- **Overlap as a positive syndrome carrier.** Couple an invalid overlap sector
  to payload checks so its trace must pay relator energy. The established
  `bounded-overlap-syndrome-energy-accounting` suggests designing a bounded
  incidence transducer rather than classifying representations.
- **Context mismatch as a consistency PCP.** Choose one reference context per
  question and add bounded-degree equality/covariance tests along a spanning
  tree of its incident contexts. The target is an `L^2` Poincare-style bound
  from local test energy to total disagreement, with constants depending only
  on the fixed finite source game.
- **Do not globalize readable bits unnecessarily.** The source ZPC hypotheses
  provide local commutation, not one global readable algebra. The transducer
  should glue decoded unreadable observables across contexts rather than assume
  all remote selectors commute.