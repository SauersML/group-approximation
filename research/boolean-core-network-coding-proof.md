---
rg: 2
id: boolean-core-network-coding-proof
kind: route
title: Read constant functions on classes as source assignments and force permutation rules on discrete and one-relay tables
target: boolean-core-is-uniform-single-demand-network-coding
requires: []
artifacts:
  - research/artifacts/boolean-core-alphabets-and-network-coding-2026-09-12.md
---

Sections 1 and 3 of the artifact.
- **Network form.** A function constant on the classes is a source assignment. Relay outputs are
  the row evaluations of `mu`, and the sink evaluation is the left side of `Dec`. `Enc` is the same
  computation on the transposed network.
- **Discrete forward table.** Two assignments that differ only in row `1` force `mu` to determine
  the label-1 coordinate. Every relay tuple occurs, which forces `nu` to read relay `1`. The
  reverse composite is then the identity.
- **One relay or one column.** The free symbol of the class of `(1,1)` forces the one-input rule
  to be a permutation, and transposed-constant patterns are row patterns of the forward table.
