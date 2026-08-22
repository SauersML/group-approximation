---
rg: 2
id: kazhdan-almost-centralizers-round-in-finite-actions
kind: claim
title: Almost-centralizing permutations of any finite action of a Kazhdan group round to exact equivariant permutations
artifacts:
  - research/artifacts/wreath-permutation-collapse-2026-08-22.md
distinct_from:
  two-power-sector-conjugator-dichotomy: that is a Hilbert-Schmidt all-or-nothing conjugator dichotomy for parahoric tuples in the tracial setting; this is a HAMMING/permutation rounding theorem for centralizers of arbitrary finite actions, with property (T) entering only through the uniform Kazhdan constant on the orbital complement.
  amenable-rep-of-kazhdan-has-fd-subrep: that extracts finite-dimensional subrepresentations from amenable representations of Kazhdan groups; this rounds an almost-equivariant PERMUTATION to an exactly equivariant one, a combinatorial integrality statement with no operator content.
---

THEOREM.  Let `Lambda` be finitely generated with property (T) and
Kazhdan pair `(S, kappa)`.  For ANY action of `Lambda` on a finite set
`V` and any permutation `P` of `V` with

```text
|{v : P tau(s) v != tau(s) P v}| <= eps |V|,  s in S,  eps < kappa^2/C',
```

there is an exactly `Lambda`-equivariant permutation `c` of `V` with
`|{v : Pv != cv}| <= C eps |V| / kappa^2` (absolute `C, C'`).

Proof (complete in the artifact): the graph of `P` is an
almost-invariant subset of `V x V` under the diagonal action; property
(T) pushes its indicator onto the span of orbital indicators; the
permutation row-constraint makes the surviving orbital out-degrees sum
to exactly one per orbit, so integrality leaves a single degree-one
orbital per orbit — the graph of an equivariant bijection — plus an
isomorphic-orbit matching at vanishing extra cost.

Scope notes.  No transitivity, congruence structure, or infranormality
is assumed; the constant is dimension-free and effective (Kassabov's
explicit Kazhdan constants for `SL_3(Z)`).  The mechanism is the
standard (T)-projection-plus-integrality rounding of the P-stability
literature (Becker–Lubotzky–Thom family), run on the orbital
decomposition of the square; Kun–Thom Theorem 4.1 is the ultraproduct
centralizer-NORMALIZATION statement for infranormal pairs — a
different conclusion under stronger hypotheses.  What this claim adds
to the graph is the exact-rounding form that the wreath permutation
collapse (`wreath-nonsofic-from-flexible-p-stability`) consumes.
