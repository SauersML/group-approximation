---
rg: 2
id: amenable-amalgams-have-mf-full-cstar
kind: claim
title: Amalgamated free products of amenable groups have MF full group C-star algebras
distinct_from:
  symmetric-double-weak-mf: That route uses Shulman's symmetric C-star amalgam theorem for two copies of one MF algebra and concludes the repository's weak-MF predicate; this is the group-specific amenable-factor theorem for an arbitrary pair and gives MF of the full group C-star algebra.
artifacts:
  - notes/FINITE_PACKET_SELF_COPY_COLLAPSE.md
  - notes/FALSE_SHULMAN_TRACE_AUDIT.md
---

If `G₁` and `G₂` are countable amenable groups and `H` is a common subgroup,
then

```text
C*(G₁ *_H G₂)
```

is an MF C-star algebra.  Consequently the amalgamated free product group is
operator-MF.  This is Theorem 19 of Shulman, *The MF property for amalgamated
free products*, arXiv:2603.13564 (2026).

The arbitrary pair is load-bearing: the finite-memory calibration uses
`BS(1,2) *_<a²> Z²`, not a symmetric double.
