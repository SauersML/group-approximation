---
rg: 2
id: titz-witzel-sparse-defect-needs-dense-generator-surgery-proof
kind: route
title: Apply the Hamming telescoping inequality to the marked eighth power
target: titz-witzel-sparse-defect-needs-dense-generator-surgery
requires:
  - titz-witzel-soficity-is-one-finite-csp
---

Normalized Hamming distance on `Sym(d)` is bi-invariant.  Hence for any
permutations `p,q` and positive integer `m`, telescoping gives

```text
d_H(p^m,q^m) <= m d_H(p,q).                             (TSP1)
```

Every exact finite solution of `(TWS4)` is a finite action of
`barGamma_1^2`.  Its finite residual has index two and contains the marked
word `y^8`, so `y0^8=1`.  The same is true on a disjoint union of exact
solutions.  Taking `p=y`, `q=y0`, and `m=8` in `(TSP1)` gives

```text
d_H(y^8,1)=d_H(y^8,y0^8)<=8 d_H(y,y0),
```

which is `(TSS1)`.  Changing a labeled `y`-edge at `k` vertices changes the
permutation `y0` on at most `k` inputs, so `d_H(y,y0)<=k/d`.  Thus `o(d)`
labeled-edge edits force `d_H(y^8,1)=o(1)`, contrary to a positive marked
limsup.
