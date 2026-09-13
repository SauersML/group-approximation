---
rg: 2
id: circle-rotation-zd-full-groups-not-fp-via-finite-type
kind: route
title: A free subshift that is not of finite type has derived and alternating full groups that are not finitely presented
target: circle-rotation-zd-derived-full-groups-are-not-fp
requires:
  - circle-rotation-zd-codings-are-not-of-finite-type
  - fp-alternating-full-groups-of-free-subshifts-force-sft
artifacts:
  - research/artifacts/zp-fp-simple-amenable-obstructions-2026-09-13-part3.md
---

## Why sufficient

1. **The coding.** By `circle-rotation-zd-codings-are-not-of-finite-type`, `X` is a
   subshift over `Z^d` with a free action, and `X` is not of finite type.
2. **Theorem G.** By `fp-alternating-full-groups-of-free-subshifts-force-sft`, a finitely
   presented subgroup of `[[Z^d ~ X]]` containing the rule 3-cycles of some radius forces
   `X` to be of finite type.
3. **Conclusion.** The derived and alternating full groups both contain those 3-cycles, so
   neither is finitely presented.
