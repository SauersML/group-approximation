---
rg: 2
id: quantum-context-frame-index
kind: claim
title: Pairs of quantum context frames carry a stable local Z2 coherence index
distinct_from:
  random-hyperplane-hs-binaryization: that produces classical bits from metric separation but does not vanish on exact quantum solutions; this index is defined from paired operator frames and is zero on every coherent quantum realization.
  spectral-carrier-to-local-syndrome-transducer: that requires an extensive bounded-overlap syndrome family; this constructs the local quantum-aware label only.
artifacts:
  - research/artifacts/trace-promotion-renormalization-program-2026-08-20.md
---

For each overlap of two exactified BCS/LCS context frames, construct a
conjugation-invariant local index

```text
ind(F_c,F_c') in Z_2
```

from the two-subspace CS decomposition, a Pfaffian sign, or an equivalent
finite-dimensional frame invariant.  It must satisfy:

1. the index is zero for every pair coming from one coherent finite-dimensional
   quantum solution, including magic-square-type solutions;
2. it is stable under sufficiently small normalized-HS perturbations after a
   bounded-rank spectral cut;
3. a nonzero value forces a named local relator-energy payment; and
4. transport around the marked cycle changes the total parity.

The construction must be amplification-invariant after normalization and use
no classical assignment rounding.

## Attempts

- Put two context projections in CS form and test parity of exceptional
  principal-angle blocks, stabilized by a Pfaffian sign after realification.
- The obstacle is HS stability near angle crossings. Spectral slicing must
  discard only controlled marked mass and make each surviving index locally
  constant.
- Reject any candidate nonzero on an exact magic-square representation; that
  detects accidental classicalization immediately.
