---
rg: 2
id: random-hyperplane-hs-binaryization
kind: claim
title: Sign tests turn Hilbert–Schmidt distance into bit disagreement, dimension-free
distinct_from:
  hs-defect-is-mean-square-sphere-displacement: that is the exact identity between HS distance and mean-square displacement of a random unit vector — a statement about continuous positions; this converts the same quantity into the probability that a single random ±1 observable separates the two images, which is what a combinatorial (Boolean, Hamming) rounding step can consume.
artifacts:
  - research/artifacts/hyperlinear-divergent-strategies-2026-08-18.md
---

**Lemma.**  Let `A, B ∈ O(D)`, let `x, a` be independent uniform points of
`S^{D-1}`, and set `b_A = sgn⟨a, Ax⟩`, `b_B = sgn⟨a, Bx⟩`.  Then

```text
d_2(A,B)^2 / (2 pi)   ≤   Pr[ b_A ≠ b_B ]   ≤   d_2(A,B) / 2.
```

The complex case follows by realification, which preserves normalized HS
distance.

**Proof.**  Condition on `x` and let `theta ∈ [0,pi]` be the angle between
`Ax` and `Bx`; a uniformly random hyperplane separates them with probability
`theta/pi` (Goemans–Williamson).  With `r = ‖Ax-Bx‖ = 2 sin(theta/2)` we have
`r^2 = 2(1-cos theta) ≤ 2 theta`, giving `theta/pi ≥ r^2/(2 pi)`; and Jordan's
inequality `sin t ≥ 2t/pi` on `[0,pi/2]` gives `2 theta/pi ≤ 2 sin(theta/2) = r`,
i.e. `theta/pi ≤ r/2`.  Averaging over `x` with
`E_x r^2 = D^{-1}‖A-B‖_F^2 = d_2(A,B)^2` and `E r ≤ (E r^2)^{1/2}` finishes.  ∎

**What it is for.**  It is a dimension-free interface between the metric in
which hyperlinearity is stated and the Boolean data a combinatorial rounding
argument manipulates: HS-close operators almost never disagree on a random
bit test, trace-separated operators disagree with probability bounded below by
a constant, and independent repetitions amplify.  Both constants are absolute.

**What it is NOT.**  The hash `U ↦ (sgn⟨a_j, U x_j⟩)_j` is not multiplicative:
the bits of `UV` are not a function of the bits of `U` and of `V`, so this
lemma alone converts nothing into a sofic model, and it does not resurrect the
refuted shortcut that `(U(d), d_2)` is a sofic metric group.  Its role in this
graph is as an ingredient inside a global consistency mechanism — binary
observables for the conic/CSP encoding of
`group-table-cpsd-cp-face-collapse`, or edge predicates for the candidate
graphs of `spherical-candidate-hypergraph-quasirandom`.

Source and re-derivation: `research/artifacts/hyperlinear-divergent-strategies-2026-08-18.md`
(its Lemma 12.1).
