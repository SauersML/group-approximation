---
rg: 2
id: support-proportion-size-separates-compressor-images
kind: claim
title: The support proportion of realizers separates a realized twist group from its strict compressor image
refuted_by:
  - conjugation-invariant-sizes-miss-relative-defect
distinct_from:
  relative-normalization-modulo-kazhdan-kernel: that is the open normalization statement; this is one proposed size for proving it, which is false.
  conjugation-invariant-sizes-miss-relative-defect: that is the established no-go for every conjugation-invariant size; this is the specific support-proportion candidate it refutes.
---

**REFUTED.** Proposed in the Attempts of
`relative-normalization-modulo-kazhdan-kernel` as the natural candidate size.
The claim: for a sofic host containing a relative configuration, the support
proportion of realizers, a measure-type size, is strictly monotone under a
strict compressor self-embedding of the realized twist group. The model
would then imitate the way corner copies of Thompson's `V` halve supports on
the Cantor set.

Refuted by `conjugation-invariant-sizes-miss-relative-defect`:

- support proportion is a conjugation invariant of permutations, so it is
  exactly preserved by the compressor endomorphisms;
- in trace-zero models, every nontrivial host element has support
  proportion `1`.

## Attempts

- **Support halving transported to the model: dead.** See the refuter. Cantor
  supports do not survive trace-zero sofic representations.
