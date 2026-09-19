---
rg: 2
id: fournier-facio-universal-frobenius-stable-t-embedding
kind: claim
title: Arbitrary recursive group content embeds in a finitely presented property-(T) Frobenius-stable group
artifacts:
  - research/artifacts/self-similar-dimension-pressure-map-2026-08-20.md
distinct_from:
  hs-stability-forces-nonhyperlinear-central-extension: that consumes normalized Hilbert--Schmidt stability to obstruct hyperlinearity; this theorem concerns the unnormalized Frobenius metric.
  character-rigidity-equals-hyperfinite-hs-stability: that is a normalized-HS character theorem for higher-rank lattices; this constructs new property-(T) groups whose Frobenius stability comes from having no nontrivial Frobenius-approximable quotient.
---

Every countable group embeds into a property-(T), Frobenius-stable group, and
if the input is recursively presented then the host can be chosen finitely
presented.  The host moreover fails property `(T_2)` strongly: its second
cohomology is nonzero for every unitary coefficient representation.

The stability here uses the **unnormalized** Frobenius norm.  The construction
arranges that the host has no nontrivial Frobenius-approximable quotient, so
its Frobenius stability is in this sense vacuous.  Neither statement gives
normalized Hilbert--Schmidt stability, where arbitrarily increasing matrix
dimension makes low-rank errors cheap.  Thus the theorem validates the
architecture

```text
arbitrary recursive content + finite presentation + property (T) + rigidity
```

but does not discharge the normalization gate in the hyperlinear problem.

