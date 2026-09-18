---
rg: 2
id: bmw-44-sat-survivor-dichotomy-via-unconditional-certificates
kind: route
title: The unconditional non-left-orderability of the three parity kernels gives the second alternative of the reducible-or-not-left-orderable dichotomy
target: bmw-44-sat-survivor-parity-kernels-not-left-orderable
requires:
  - bmw-40-40-193-281-332-parity-kernels-not-left-orderable
artifacts:
  - experiments/bmw-44-survivor-left-orders-2026-09-17/README.md
---

The target says that for each of `40_40#193`, `#281` and `#332`, either `Γ` is reducible or `Γ^+` is not
left-orderable.

The required claim says that `Γ^+` is not left-orderable for each of the three classes, with no hypothesis on `Γ`.
So the second alternative holds in every case, and the dichotomy follows. ∎

Remarks:
- For `#281` the first alternative is false by `bmw-40-40-281-is-irreducible`.
- For `#193` and `#332`, reducibility is still undecided and is no longer needed.
