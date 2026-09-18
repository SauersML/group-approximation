---
rg: 2
id: rational-bs12-hull-from-gl-2-q-permutational-class
kind: route
title: GL_2(Q) in B_A implies Q x|_2 Z in B_A, since Q x|_2 Z is the subgroup of affine matrices [[2^k, q],[0,1]]
target: rational-bs12-hull-in-permutational-bh-class
requires:
  - gl-n-q-in-permutational-boone-higman-class
  - boone-higman-type-a-class-closed-under-finite-extensions
---

- The matrices `[[2^k, q],[0,1]]` (`k ∈ Z`, `q ∈ Q`) form a subgroup of `GL_2(Q)`.
- Sending `[[1,q],[0,1]]` to `q` and `[[2,0],[0,1]]` to `s` identifies it with
  `D_2 = <Q, s | s q s^-1 = 2q>`, since
  `[[2,0],[0,1]] [[1,q],[0,1]] [[2,0],[0,1]]^-1 = [[1,2q],[0,1]]`.
- `gl-n-q-in-permutational-boone-higman-class` at `n = 2` gives `GL_2(Q) ∈ B_A`.
- `B_A` is closed under subgroups (item 1 of
  `boone-higman-type-a-class-closed-under-finite-extensions`), so `D_2 ∈ B_A`.

This route records that the stepping stone is necessary for the `B_A` form of the
root. It does not establish anything new while the root is open.
