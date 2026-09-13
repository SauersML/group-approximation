---
rg: 2
id: explicit-sixty-relator-nonsofic-group-proof
kind: route
title: The sixty-relator group is the binary Leavitt unit group, which is simple and nonsofic
target: explicit-sixty-relator-nonsofic-group
requires: [leavitt-unit-group-steinberg-weyl-presentation, openai-leavitt-unit-nonsofic, binary-leavitt-unit-group-is-simple]
artifacts:
  - research/artifacts/leavitt-unit-group-steinberg-weyl-presentation-2026-09-12.md
---

By `leavitt-unit-group-steinberg-weyl-presentation`, `P = L_(F_2)(1,2)^x` via the stated
images. The unit group is not sofic (`openai-leavitt-unit-nonsofic`; independently
kernel-checked as `universalLeavittUnits_not_isSofic`) and is simple
(`binary-leavitt-unit-group-is-simple`). Soficity and simplicity are isomorphism invariants,
and `P` is finitely presented by construction. QED.
