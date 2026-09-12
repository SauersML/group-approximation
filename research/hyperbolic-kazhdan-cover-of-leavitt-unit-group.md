---
rg: 2
id: hyperbolic-kazhdan-cover-of-leavitt-unit-group
kind: claim
title: A hyperbolic Kazhdan group maps onto the binary Leavitt unit group with a Kazhdan kernel
distinct_from:
  rips-kernel-without-finite-quotients: that asks for a Rips kernel with no nontrivial finite quotient over a non-residually-finite quotient; this fixes the quotient to be the nonsofic Leavitt unit group and records property (T) of the hyperbolic group and of the kernel, with no claim about finite quotients of the kernel.
  torsion-free-hyperbolic-kazhdan-partner-exists: that supplies one hyperbolic Kazhdan group; this uses it as the Rips source and produces a different hyperbolic Kazhdan group mapping onto a nonsofic group.
  openai-leavitt-unit-nonsofic: that is nonsoficity of the quotient; this is a hyperbolic cover of it whose own soficity is open.
artifacts:
  - research/artifacts/hyperbolic-leavitt-cover-relative-defect-2026-09-12.md
---

**ESTABLISHED.** Put `R = L_(F_2)(1,2)`. There is a short exact sequence

```text
1 -> N -> G -> R^x -> 1
```

with the following properties:

- `G` is word-hyperbolic;
- `G` and `N` have property (T);
- `N` is infinite;
- every homomorphism `phi` from `G` to a finite group satisfies
  `phi(N) = phi(G)`.

Derivation: `hyperbolic-kazhdan-cover-of-leavitt-unit-group-proof`.

## Why this group matters for the hyperbolic question

`G` is a hyperbolic group that maps onto a nonsofic group with a Kazhdan
kernel. Whether `G` is sofic is open. Every nonsoficity certificate in this
graph is inert on `G`:

- rigid compression defects vanish in hyperbolic groups
  (`hyperbolic-compression-centralizer-rigidity`);
- soficity does not pass to quotients.

What `G` does carry is an infranormal Kazhdan pair whose defect survives modulo
`N` (`hyperbolic-kazhdan-group-has-infranormal-kazhdan-subgroup`). That is the
input to `nonsofic-hyperbolic-via-relative-rigid-defect`.
