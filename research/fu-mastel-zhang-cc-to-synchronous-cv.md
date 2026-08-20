---
rg: 2
id: fu-mastel-zhang-cc-to-synchronous-cv
kind: claim
title: Symmetrized constraint-variable conversion preserves finite soundness and PCC completeness
distinct_from:
  oracularizable-tracial-nonru-game-exists: that extends the conversion's completeness to a tracial BCS model and combines it with a non-RU source; the published theorem only asserts finite-dimensional PCC completeness.
---

Let `G` be a finite constraint--constraint BCS game with maximum context
size `C`.  Fu--Mastel--Zhang construct a synchronous game `G^cv` whose
questions are the constraints and variables of `G`.  After sampling an
incident pair `(i,j)`, its verifier chooses uniformly between

```text
(i,i), (j,j), (i,j), (j,i).                               (FMZ1)
```

Their Theorem 3.1 proves:

1. a perfect finite-dimensional strategy for `G` gives a perfect projective,
   commuting, consistent strategy for `G^cv` on a maximally entangled state;
2. if a finite-dimensional strategy for `G^cv` has value `1-epsilon`, then
   `G` has a finite-dimensional strategy of value
   `1-poly(C,epsilon)`, where the loss tends to zero with `epsilon`.

In particular,

```text
omega_qa(G)<1  =>  omega_qa(G^cv)<1.                       (FMZ2)
```

Indeed, otherwise finite-dimensional strategies for `G^cv` with losses
tending to zero, followed by item 2, would force `omega_qa(G)=1`.

No commuting-operator completeness statement is imported here.  The paper
explicitly formulates its strategy model as finite-dimensional tensor-product
strategies.  The tracial completeness extension needed by Cairn is proved
separately from the incidence pattern `(FMZ1)`.
