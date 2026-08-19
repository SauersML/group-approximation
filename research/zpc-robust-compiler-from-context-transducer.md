---
rg: 2
id: zpc-robust-compiler-from-context-transducer
kind: route
title: One-hot rounding plus finite context gluing yields the quantitative ZPC compiler
target: zpc-selector-robust-lcs-compiler
requires:
  - controlled-linear-predication-normal-form
  - odd-selector-overlap-rounding
  - onehot-predicated-direct-sum-decoder
  - zpc-context-overlap-mismatch-transducer
artifacts:
  - research/artifacts/selector-overlap-rounding-2026-08-18.md
---

Let an output finite-dimensional strategy have loss `epsilon`.  By `(CTX)`, in
every local context the odd-parity defect and pairwise selector overlap tend to
zero with `epsilon`.  `odd-selector-overlap-rounding` therefore supplies
orthogonal one-hot sectors whose total missing trace is `O(epsilon)` (with a
fixed constant because the source game has finitely many contexts).

On each good context corner, `onehot-predicated-direct-sum-decoder` converts
the predicated branch copies into genuine controlled unreadable observables.
Their weighted source-equation squared defect is bounded by the compiled
predicated defect divided by the good-corner trace, hence is `O(epsilon)` for
small enough `epsilon`.

The same transducer bounds `D_glue=O(epsilon)`.  For each source question,
choose one incident context as a reference and a spanning tree through its
finitely many incident contexts.  Replacing each local decoded observable by
the reference copy changes every incident source check by at most the sum of
the edge mismatches along a tree path.  Cauchy--Schwarz and the finite maximum
path length give a constant `C_G`, depending only on the fixed game, so the
globally glued source strategy has total loss `O_G(epsilon)`.

Perfect source strategies compile perfectly by the completeness clause of the
transducer and `controlled-linear-predication-normal-form`.  Since the fixed
source game has quantum value strictly below `1/2`, choose `eta>0` so small
that an output loss at most `eta` would make the glued source loss smaller than
the fixed gap to `1/2`.  Thus every output strategy of value at least
`1-eta` would decode to a source strategy of value greater than `1/2`, exactly
the quantitative soundness required by `zpc-selector-robust-lcs-compiler`.