---
rg: 2
id: braid-haagerup-iff-punctured-sphere-mcg-haagerup-proof
kind: route
title: Pass through finite index and the product with the center
target: braid-haagerup-iff-punctured-sphere-mcg-haagerup
requires:
  - pure-braid-group-is-center-times-sphere-pure-mcg
artifacts:
  - research/artifacts/zp-braid-haagerup-reductions-2026-09-13-part1.md
---

The Haagerup property passes to subgroups (restrict a proper cnd function), to finite direct products (sum),
and to finite-index overgroups (induced affine action). `Z` has it (Haagerup 1979). Proofs are in §1 of the
artifact.

- `B_n` ⟺ `P_n`, since `[B_n : P_n] = n!`.
- `P_n ≅ Z × PMod(S_{0,n+1})` (`pure-braid-group-is-center-times-sphere-pure-mcg`), so `P_n` ⟺
  `PMod(S_{0,n+1})`.
- `PMod(S_{0,n+1})` has index `(n+1)!` in `Mod(S_{0,n+1})`.
- `B_n/Z(B_n)` contains `P_n/Z(P_n) ≅ PMod(S_{0,n+1})` with index `n!`.

The monotonicity consequence uses the injective inclusion `B_n ≤ B_{n+1}`.
