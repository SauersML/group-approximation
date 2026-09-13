---
rg: 2
id: o2-tensor-power-shift-is-rokhlin-proof
kind: route
title: The norm of the contractible O_2 is contractible and outer, hence Rokhlin
target: o2-tensor-power-shift-is-rokhlin
requires: [kk-tensor-power-norm-functor-to-kk-zp, outer-actions-on-o2-kk-g-contractible-iff-rokhlin]
artifacts: [research/artifacts/uct-kk-norm-functor-2026-09-13-part1.md]
---

Unreviewed.

1. `[id_(O_2)] = 0` in `KK(O_2, O_2)` (Cuntz).  Item 1 of
   `kk-tensor-power-norm-functor-to-kk-zp` (part 1, Theorem A) gives
   `(O_2^(⊗p), σ) ≃_(KK^G) 0`.
2. Outerness of `σ^k` for `0 < k < p`: extend to the von Neumann tensor power
   of a type III factor representation through the shift-invariant product
   state.  A nontrivial permutation of tensor factors of a non-type-I factor is
   outer (standard, not re-read).
3. `O_2^(⊗p) ≅ O_2` (Elliott).  Item 2 of
   `outer-actions-on-o2-kk-g-contractible-iff-rokhlin` turns contractibility
   plus pointwise outerness into the Rokhlin property and conjugacy to the
   model.
4. Crossed products are functorial on `KK^G`, which gives
   `O_2^(⊗p) ⋊ Z/p ≃_KK 0`.

This is part 1, Corollary A.
