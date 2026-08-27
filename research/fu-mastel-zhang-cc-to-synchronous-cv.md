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

## Compiler audit of the full succinct-PZK construction

Fu--Mastel--Zhang's Theorems 1.1 and 1.2 additionally give RE protocols with
perfect **finite-dimensional** completeness, constant finite-dimensional
soundness, and respectively `(polylog,O(1))` or `(O(1),polylog)`
question/answer lengths.  Their compression is assembled from question
reduction, oracularization, answer reduction, and parallel repetition.  This
is a strong finite-game source theorem, but it does not strengthen the
ordinary-group endpoint beyond `(FMZ1)--(FMZ2)`:

1. succinctness changes the encoding and verifier distribution, not the fact
   that the resulting BCS predicates are generally nonlinear;
2. the PCC property only asserts compatibility for question pairs sampled by
   the verifier.  It does not make unrelated context algebras commute and does
   not provide a common reducing carrier for all contexts;
3. perfect zero knowledge is a statement about simulation of the honest
   transcript.  It supplies neither a canonical group trace nor ordinary
   group-word equations implementing forbidden BCS projections;
4. the paper explicitly excludes commuting-operator strategies from its
   formal strategy model.  Consequently its perfect-completeness theorem
   cannot by itself supply the perfect commuting side required by a
   non-hyperlinear solution-group diagonal.

Question sampling by the provers is therefore not a group-level substitute
for sampling: once the verifier is compiled to a finite presentation, every
positive-support check is simply a fixed relator/check, and all of them must
hold in a perfect model.  The only reusable nontrivial bridge here is the
symmetrized incidence geometry `(FMZ1)`, already used in
`oracularizable-tracial-nonru-game-exists` together with an independent
tracial BCS model.
