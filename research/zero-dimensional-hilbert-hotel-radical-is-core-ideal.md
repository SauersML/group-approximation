---
rg: 2
id: zero-dimensional-hilbert-hotel-radical-is-core-ideal
kind: claim
title: For a zero-dimensional crossed product the Hilbert-hotel radical is the ideal of functions vanishing on the chain-recurrent core
distinct_from:
  zero-dimensional-system-mf-radical-is-core-restriction: that is the computed MF radical of the group, the restriction kernel to the chain-recurrent core; this identifies the ring-theoretic ideal behind it, so that the group formula would follow from the general sandwich rather than from the dynamics.
artifacts:
  - research/artifacts/un-open-1-hilbert-hotel-radical-2026-09-13.md
---

**OPEN.** Let `X` be a compact metrizable zero-dimensional space with a homeomorphism `T`, let
`k` be a field of positive characteristic, and let `R = C(X,k) ⋊ T Z` be the algebraic crossed
product. Is

```text
hh(R) = { a in R : a vanishes on the chain-recurrent core of (X,T) } ?
```

The right-hand side is the ideal whose group-level restriction kernel is the MF radical in
`zero-dimensional-system-mf-radical-is-core-restriction` and in the manuscript's
`thm:core-mf-radical`. A positive answer would identify the ideal behind that printed dynamical theorem: through
`mf-radical-sandwiched-by-hilbert-hotel-radical` the printed equality would become the statement that the
defect ideal is the whole core-vanishing ideal and that the relative `K_1` slack between the two bounds is
MF-invisible there. It would read the chain-recurrent core as the dynamical avatar of a purely ring-theoretic
radical: **defects live exactly off the core**.

## Attempts

- **The easy inclusion.** On the core the system has invariant probability measures, so the restricted
  crossed product should be stably finite and its defects zero; that gives `hh(R)` inside the
  vanishing ideal, modulo checking that a measure on the core gives direct finiteness of the
  restricted ring over a field of characteristic `p` — which is exactly the open arrow of
  `un-tarski` and is Kaplansky-hard in full generality. The special structure of a core system may
  avoid that, since the core is a nested intersection of closed invariant sets.
- **The hard inclusion.** Off the core, points are wandering, so `T` genuinely moves a clopen set
  into a proper subset of itself and one expects a one-sided pair supported there. Writing that pair
  down for a general wandering set is the missing construction: the natural candidate is a
  characteristic function of a wandering clopen set composed with the shift, and one has to see that
  its defect is nonzero and generates the vanishing ideal.
- **Calibration.** The minimal case has core `X`, giving `hh = 0`, which agrees with the Pestov
  9.1 ring being stably finite. The Toeplitz-Jacobson algebra is the crossed-product-like case with a
  single wandering orbit, where the answer is the finitary ideal, matching the manuscript.
