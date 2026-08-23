---
rg: 2
id: lin-to-smooth-label-cover-hybrid-gap-proof
kind: route
title: Run the weighted BCS and CMPS reductions with qc completeness and q soundness
target: lin-gap-smooth-label-cover-projective-color-game
requires:
  - lin-explicit-fixed-bcs-gap-via-generic-conversion
  - mastel-slofstra-private-context-augmentation-preserves-defect
  - fu-mastel-zhang-cc-to-synchronous-cv
  - cmps-lemma20-is-radius-two-incidence-commutation
  - smooth-label-cover-edges-are-finite-phase-projective-color
artifacts:
  - research/artifacts/cmps-smooth-label-monomial-audit-2026-08-23.md
---

Start with the effectively specified `B_loop` from
`lin-explicit-fixed-bcs-gap-via-generic-conversion`.  It has a perfect
tracial model and a positive finite-dimensional defect gap, obtained without
assuming that Lin's perfect strategy is oracularizable.

Apply the contextwise Cook--Levin extension of Mastel--Slofstra Remark 5.8
and bounded subdivision (Theorem 6.4) to obtain 3SAT constraints.  The
classical homomorphisms transport an exact tracial model forward, while the
defect pullback bounds preserve a positive finite-dimensional gap.  Use the
symmetrized constraint-variable conversion and its tracial incidence model;
finite-dimensional soundness is
`fu-mastel-zhang-cc-to-synchronous-cv`, while exact commuting completeness is
the atom/variable functional-calculus construction in
`tracial-bcs-incidence-oracularization-proof`.

Culf--Mastel--Paddock--Spirig Theorem 33 and the equality gadget in Lemma 32
lower the resulting instance to fixed-degree `3SAT5`.  Exact completeness is
obtained by copying each source observable to its occurrence variables and
satisfying every equality gadget; this works in the original tracial von
Neumann algebra.  Theorem 33 pulls every finite-dimensional target trace back
with bounded defect and hence preserves a positive gap.

Next apply CMPS Lemma 20.  Its local-copy/equality construction assigns the
same observable to every copied variable.  Its proof of radius-two
commutation uses only the exact source-context commutators, so it applies in
the tracial model and yields

```text
[A_x,A_y]=0
whenever x,z and y,z occur in two target clauses.        (LSG3)
```

The subdivision soundness cited in Lemma 20 retains a positive
finite-dimensional gap.  This produces the `3SAT10` input used by CMPS
Theorem 19.

For the `(J,R)` dummy game, Lemma 12 amplifies that gap by entangled
projection-game parallel repetition.  On completeness, its displayed tensor
product PVM construction also works for a tracial commuting representation:
take the finite spatial tensor power and the product trace.  Choose `R` so
the finite-dimensional value is at most the requested `s`.

Finally, use the proof of their stronger Theorem 19.  As in Theorem 10 it
discards the right-side PVMs and keeps the left PVMs.  Equality `(3.2)` and
the fiber-coarsening calculation use only
PVM orthogonality, positivity, and traciality, so a perfect commuting dummy
strategy gives a perfect synchronous commuting smooth-label strategy.  The
reverse soundness construction averages the label PVMs into a POVM and uses
finite-dimensional Naimark dilation, so a finite-dimensional smooth-label
strategy of value greater than `s` would contradict the dummy-game bound.
Theorem 19 checks that two label PVMs commute whenever their questions have a
possible common partner; its check invokes only `(LSG3)` and finite products.
It therefore remains valid in the tracial model and proves `(LSG2)` together
with `(LSG1)`.
