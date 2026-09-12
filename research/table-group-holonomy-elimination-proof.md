---
rg: 2
id: table-group-holonomy-elimination-proof
kind: route
title: Eliminate the decoder letters along a spanning forest and restrict to the identity component
target: table-groups-are-memory-holonomy-groups
requires: []
artifacts:
  - research/artifacts/table-group-holonomy-normal-form-2026-09-12.md
---

**The normal form.**
- Every relator of `U_E` reads `x_s = x_s' delta` with `delta` in the free group
  on the memory letters.
- Walk a spanning forest of the difference graph outward from the roots (`1_S`,
  and one free letter per other component). Each tree relator eliminates one
  decoder letter, giving `x_s = x_root w_s`.
- A non-tree edge becomes `w_s = w_s' delta`, since the root letter cancels on the
  left. The other roots occur in no relator, so they split off as a free factor.
- The memory side is the same computation with left multiplication.

**The identity component.**
- An identified pair joins its two decoder addresses, so classes do not cross
  components.
- Fixing symbols on the other components' classes turns the decoder into one
  reading only the component of `1_S`. It is still a left inverse of the same
  encoder, so strictness, which is non-surjectivity of that encoder, does not
  change.
- Restriction and minimization only free the host and lower
  `|S| + #edges`. Iterating them reaches a connected minimal design.

Sections 1 and 2 of the artifact.
