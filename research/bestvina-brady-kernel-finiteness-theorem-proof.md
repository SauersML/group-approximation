---
rg: 2
id: bestvina-brady-kernel-finiteness-theorem-proof
kind: route
title: Homotopical finiteness of Bestvina--Brady kernels from the printed Main Theorem, Wall's description of F_n, and Hurewicz
target: bestvina-brady-kernel-finiteness-theorem
requires:
  - bestvina-brady-main-theorem
---

Statement (2) of `bestvina-brady-kernel-finiteness-theorem` is item (1) of the Main Theorem
(`bestvina-brady-main-theorem`) with `n` replaced by `n − 1`.

Statement (1), type `F_n` iff `L` is `(n−1)`-connected:
- `n = 1`: type `F_1` means finitely generated, which is type `FP_1(Z)`. By Main Theorem (1) with
  index `0`, that holds iff `L` is homologically `0`-connected, i.e. nonempty and connected.
- `n ≥ 2`: a group is of type `F_n` iff it is finitely presented and of type `FP_n(Z)` (Wall's
  theorem; standard, e.g. in K. S. Brown, *Cohomology of Groups*, VIII.7). By Main Theorem (3) and
  (1), `BB_L` is of type `F_n` iff `L` is simply connected and `H̃_i(L; Z) = 0` for `i ≤ n − 1`. By
  the Hurewicz theorem, a simply connected complex with `H̃_i = 0` for `i ≤ n − 1` is
  `(n−1)`-connected, and conversely.
