---
rg: 2
id: titz-witzel-sparse-defect-needs-dense-generator-surgery
kind: claim
title: Sparse relator defects for the Titz--Witzel gate cannot come from sparse surgery on finite exact models
distinct_from:
  titz-witzel-soficity-is-one-finite-csp: That reduces soficity to sparse relator defects with a surviving mark; this proves that those defects cannot be obtained by sparsely editing exact finite sheets.
---

**THEOREM.**  Let `(x0,y0,z0)` be any exact finite permutation solution of
the twelve equations `(TWS4)`, or a disjoint union of such solutions.  If
`(x,y,z)` is another triple on the same `d` points, then

```text
d_H(y^8,1) <= 8 d_H(y,y0).                              (TSS1)
```

Consequently a sequence satisfying the marked objective
`limsup d_H(y^8,1)=c>0` has a subsequence which differs in at least
`(c/8-o(1))d` `y`-edges from every exact finite model.  After discarding the
other indices, it therefore cannot be produced from copies of the exact
`C2` action by changing `o(d)` labeled generator edges.  Any
branched-cover, graph-surgery, or random-lift attack on the finite gate must
therefore have **dense generator monodromy**, even if the twelve relator
defects themselves are sparse.

This does not obstruct soficity: small relator defect does not imply small
generator distance from an exact action.  It rules out precisely the most
literal sparse surgery, in which one starts with finite exact sheets and
edits only the labeled edges incident to `o(d)` branch or seam vertices.
