---
rg: 2
id: brin-thompson-2v-is-torsion-locally-finite
kind: claim
title: Every finitely generated periodic subgroup of the Brin–Thompson group 2V is finite
distinct_from:
  some-fp-simple-group-has-an-infinite-bounded-exponent-subgroup: that is the open existence question for f.p. simple hosts of infinite bounded-exponent groups; this decides it for the one host where the known argument for V breaks, in either direction.
  circle-and-tree-product-periodic-subgroups-are-finite: that settles circle groups and tree-product lattices; this is the open two-stack case.
artifacts:
  - research/artifacts/gq-bh-bh-free-06-one-stack-pumping.md
---

**OPEN.** Every finitely generated periodic subgroup of Brin's group `2V` is finite.

**Why it matters.** `2V` is infinite, finitely presented and simple.
- **If this fails with bounded exponent**, `2V` witnesses
  `some-fp-simple-group-has-an-infinite-bounded-exponent-subgroup`. That kills the
  bounded-exponent separator of Boone--Higman for that exponent.
- **If it holds**, the barrier recorded there extends from `V` to the first
  multi-stack host. Every infinite bounded-exponent input would then need hosts
  with non-trivial tail germs (Röver--Nekrashevych type) or with genuinely
  infinite-dimensional structure.

**What is known.**
- **`V` is torsion locally finite (Röver).** This is Burillo--Cleary--Röver,
  arXiv:1402.3860, Theorem 1.3, read from the arXiv HTML. The artifact re-proves it
  by one-stack pumping and explains why that argument uses exactly one stack.
- **The only published claim for `nV` has been withdrawn.** arXiv:2209.11982,
  X. Sheng, withdrawn 2025-04-02 with the comment "a flaw in one of the proofs",
  asserted "similar obstructions as Thompson's group V on the torsion subgroups" for
  `nV`.
- **Pumping cannot bound torsion in `2V` uniformly.** Elements of `2V` are two-stack
  transformations, and Belk--Bleak (arXiv:1405.0982) prove the torsion problem of
  `2V` undecidable.
- **A concrete source of candidates (lane remark, elementary).** Identify
  `{0,1}^N × {0,1}^N` with the two-sided full shift `{0,1}^Z`. The baker map
  `(x_0 x', y) ↦ (x', x_0 y)` is then the shift `σ`, and it lies in `2V`. A
  piecewise power of `σ` on a clopen partition is piecewise a product prefix
  replacement on finitely many product cones. So the topological full group
  `[[σ]]` of the full two-sided 2-shift is a subgroup of `2V`. Hence any infinite
  finitely generated periodic subgroup of `[[σ]]` refutes this claim. Matte Bon's
  embeddings of Grigorchuk groups into `[[σ_X]]` use minimal subshifts `X`, not the
  full shift, so they do not apply directly.

## Attempts

1. **Transfer of the `V` argument (2026-09-18, lane `bh-free-06`).** *Dies at the
   second stack.* The window pigeonhole of the artifact needs the part of the
   configuration below the reading depth to be read-only. In `2V`, the second
   coordinate is a second stack that the segment can both read and rewrite, so no
   bounded window determines the segment's action.
