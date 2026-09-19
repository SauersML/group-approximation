---
rg: 2
id: literal-sign-free-eight-lamp-packet
kind: claim
title: The literal sign-free quotient contains the finite eight-lamp compression packet
distinct_from:
  literal-lamp-kernel-clifford-block-amalgam: That computes the entire lamp kernel as a free product of eight-site blocks; this selects the one fixed block, its Kazhdan normalizer, and its compressed fixed lamp for the finite-packet argument.
  literal-mark-quotient-not-mf: That proves non-MF by the commuting-involution collapse endpoint; this records the stronger finite-packet input needed for the holonomy/common-carrier proof.
artifacts:
  - research/artifacts/literal-eight-lamp-finite-packet-holonomy-2026-08-26.md
  - notes/LITERAL_GROUP_BLOCK_AMALGAM_STRUCTURE_2026-08-14.md
  - GroupApproximation/Sofic/LiteralSignFreeQuotient.lean
---

Let `H=E/<w>`, `L=q(B)`, `s=q(t)`, and `dbar=q(tct^-1)`.  The `L`-orbit of
`dbar` generates an embedded finite subgroup

```text
K ~= (C_2)^8 <= H.
```

Here `L` is finitely generated and Kazhdan, `sLs^-1<=L`, `K` is normalized by
`L`, and `dbar` is fixed by `sLs^-1`.  The action on the eight basis lamps
factors through `AGL_3(F_2)`, hence induces finite permutation holonomy on the
256 elements of `Irr(K)`.  The element `q(v_1)` moves `dbar`, so the packet
detects the nontrivial image of the unsquared defect
`u=[tct^-1,v_1]`.

