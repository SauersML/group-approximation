---
rg: 2
id: two-center-paired-frames-cannot-isolate-the-joint-hot-bit-proof
kind: route
title: Equal kernels identify the two-dimensional span of the forms
target: two-center-paired-frames-cannot-isolate-the-joint-hot-bit
requires: []
artifacts:
  - experiments/rank_one_context_frame_search.py
---

The annihilator of `ker Phi_B` in `(wedge^2 V)^*` is exactly
`span{F,B}`.  Thus `(TCF2)` gives

```text
span{F,B}=span{F,B'}.                                  (1)
```

If this span has dimension one, then `B,B'` belong to `{0,F}`; equal rank
forces the same choice.  If it has dimension two, binary arithmetic leaves
only

```text
B'=B  or  B'=F+B.
```

The first case is immediate.  In the second, `(TCF3)` says
`rank B=rank(F+B)`, while `F+B'=B`; this is exactly `(TCF4)`.

No assumption on the dimension of `V` was used.  The finite script specializes
the theorem to four frame generators and independently exhausts every word
matrix.
